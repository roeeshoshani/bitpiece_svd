use std::{
    collections::HashMap,
    ops::{Add, Rem, Sub},
    path::PathBuf,
};

use anyhow::{Context, Result, bail};
use clap::Parser;
use derive_more::Display;
use heck::{ToPascalCase, ToShoutySnakeCase, ToSnakeCase};
use newtype_ops::newtype_ops;
use num_traits::Zero;
use quote::{ToTokens, quote};
use sorted_vec::SortedVec;
use svd_parser::svd::{Device, FieldInfo, PeripheralInfo, RegisterCluster, RegisterInfo};

#[derive(clap::Parser)]
pub struct Cli {
    pub svd_file: PathBuf,
    pub out_dir: PathBuf,
}

fn mk_ident(s: &str) -> syn::Ident {
    let s = if s.chars().next().unwrap().is_ascii_digit() {
        format!("f_{}", s)
    } else {
        s.to_owned()
    };
    // make sure that it is not a keyword
    let parsed: syn::Result<syn::Ident> = syn::parse_str(&s);
    if parsed.is_err() {
        // it is a keyword, postfix with an underscore
        let fixed = format!("{}_", s);
        return syn::Ident::new(&fixed, proc_macro2::Span::call_site());
    }
    syn::Ident::new(&s, proc_macro2::Span::call_site())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Display)]
pub struct BitUnits(pub u64);
impl BitUnits {
    pub fn bytes(&self) -> ByteUnits {
        assert!((self.0 % 8) == 0);
        ByteUnits(self.0 / 8)
    }
}
newtype_ops! { [BitUnits] {add sub mul div rem} {:=} {^&}Self {^&}Self }
impl ToTokens for BitUnits {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        self.0.to_tokens(tokens);
    }
}
impl Zero for BitUnits {
    fn zero() -> Self {
        Self(0)
    }

    fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Display)]
pub struct ByteUnits(pub u64);
impl ByteUnits {
    pub fn bits(&self) -> BitUnits {
        BitUnits(self.0 * 8)
    }
}
newtype_ops! { [ByteUnits] {add sub mul div rem} {:=} {^&}Self {^&}Self }
impl ToTokens for ByteUnits {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        self.0.to_tokens(tokens);
    }
}
impl Zero for ByteUnits {
    fn zero() -> Self {
        Self(0)
    }

    fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

#[derive(Clone, Copy)]
pub struct RegStorageType {
    pub bit_len: BitUnits,
}
impl RegStorageType {
    pub fn bit_len(&self) -> BitUnits {
        self.bit_len
    }
    pub fn byte_len(&self) -> ByteUnits {
        self.bit_len.bytes()
    }
    pub fn alignment(&self) -> ByteUnits {
        self.byte_len()
    }
    pub fn uint_type(&self) -> syn::Type {
        syn::parse_str(&format!("u{}", self.bit_len)).unwrap()
    }
}

fn reg_get_bit_len(reg: &RegisterInfo) -> Result<BitUnits> {
    Ok(BitUnits(
        reg.properties
            .size
            .context(format!("missing size for register {}", reg.name))?
            .into(),
    ))
}

fn reg_get_addr_off(reg: &RegisterInfo) -> ByteUnits {
    ByteUnits(reg.address_offset.into())
}

fn field_get_bit_off(field: &FieldInfo) -> BitUnits {
    BitUnits(field.bit_range.offset.into())
}

fn field_get_bit_width(field: &FieldInfo) -> BitUnits {
    BitUnits(field.bit_range.width.into())
}

fn resolve_opt_vec<T>(opt_vec: &Option<Vec<T>>) -> &[T] {
    match opt_vec {
        Some(v) => v.as_slice(),
        None => &[],
    }
}

fn resolve_reg_cluster(reg_cluster: &RegisterCluster) -> &RegisterInfo {
    match reg_cluster {
        RegisterCluster::Register(x) => resolve_maybe_array(x),
        RegisterCluster::Cluster(_) => {
            panic!("got an svd register cluster after expansion")
        }
    }
}

fn resolve_opt_string(opt_string: &Option<String>) -> &str {
    match opt_string {
        Some(s) => s.as_str(),
        None => "",
    }
}

fn choose_reg_storage_type(reg: &RegisterInfo) -> Result<RegStorageType> {
    let bit_len = reg_get_bit_len(reg)?;
    let res = match bit_len {
        BitUnits(8) | BitUnits(16) | BitUnits(32) | BitUnits(64) => {
            RegStorageType { bit_len: bit_len }
        }
        _ => bail!("invalid reg bit length {}", bit_len),
    };

    // sanity - make sure that the address offset is properly aligned to the type that was chosen according to the size.
    // for example, a register with a bit length of 32 must have a 4-byte aligned address offset.
    let address_offset: ByteUnits = reg_get_addr_off(reg);
    let byte_len = res.byte_len();
    assert!((address_offset % byte_len) == ByteUnits(0));

    Ok(res)
}

pub struct RegAddrRange {
    pub off: ByteUnits,
    pub size: ByteUnits,
}
impl RegAddrRange {
    pub fn end(&self) -> ByteUnits {
        self.off + self.size
    }
    pub fn intersects(&self, other: &Self) -> bool {
        self.off < other.end() && other.off < self.end()
    }
}
impl std::fmt::Display for RegAddrRange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.off, self.end())
    }
}

pub struct PaddingFieldIdentGenerator {
    cur_field_index: usize,
}
impl PaddingFieldIdentGenerator {
    pub fn new() -> Self {
        Self { cur_field_index: 0 }
    }
    pub fn generate(&mut self) -> syn::Ident {
        let res = mk_ident(&format!("svd_padding_{}", self.cur_field_index));
        self.cur_field_index += 1;
        res
    }
}

fn align_up<T: Add<Output = T> + Rem<Output = T> + Sub<Output = T> + Zero + PartialEq + Copy>(
    value: T,
    alignment: T,
) -> T {
    let offset = value % alignment;
    if offset == T::zero() {
        value
    } else {
        value + alignment - offset
    }
}

fn mk_b_type(bit_len: BitUnits) -> Result<syn::Ident> {
    if bit_len.0 < 1 || bit_len.0 > 64 {
        bail!("invalid bit length {} for bit field", bit_len);
    }
    Ok(mk_ident(&format!("B{}", bit_len)))
}

struct EmittedRegFieldTy {
    emitted_code: proc_macro2::TokenStream,
    reg_field_ty_ident: proc_macro2::TokenStream,
}

fn emit_reg_field_ty(group_name: &str, reg_entry: &RegMemMapEntry) -> Result<EmittedRegFieldTy> {
    let mut fields: Vec<&FieldInfo> = resolve_opt_vec(&reg_entry.reg.fields)
        .iter()
        .map(resolve_maybe_array)
        .collect();
    fields.sort_unstable_by_key(|field| field_get_bit_off(field));
    // make it immutable after sorting
    let fields = fields;

    if fields.is_empty() {
        return Ok(EmittedRegFieldTy {
            emitted_code: quote! {},
            reg_field_ty_ident: reg_entry.storage_ty.uint_type().into_token_stream(),
        });
    }

    if fields.len() == 1 {
        let field = &fields[0];

        // a single field which covers the entire register
        if field_get_bit_off(field) == BitUnits(0)
            && field_get_bit_width(field) == reg_entry.storage_ty.bit_len
        {
            return Ok(EmittedRegFieldTy {
                emitted_code: quote! {},
                reg_field_ty_ident: reg_entry.storage_ty.uint_type().into_token_stream(),
            });
        }
    }

    let mut struct_fields_code = quote! {};
    let mut cur_off_in_struct = BitUnits(0);
    let mut padding_field_ident_generator = PaddingFieldIdentGenerator::new();
    for field in &fields {
        let start_off = field_get_bit_off(field);

        // add padding if needed
        if cur_off_in_struct < start_off {
            let padding_bits = start_off - cur_off_in_struct;
            let padding_field_ident = padding_field_ident_generator.generate();
            let padding_field_ty = mk_b_type(padding_bits)?;
            struct_fields_code.extend(quote! {
                pub #padding_field_ident: #padding_field_ty,
            });
            cur_off_in_struct += padding_bits;
        }

        let field_bit_width = field_get_bit_width(field);

        let field_name = mk_ident(&field.name.to_snake_case());
        let field_ty = mk_b_type(field_bit_width)?;
        let desc = resolve_opt_string(&field.description);
        struct_fields_code.extend(quote! {
            #[doc = #desc]
            pub #field_name: #field_ty,
        });
        cur_off_in_struct += field_bit_width;
    }

    let padding_bits = reg_entry.storage_ty.bit_len - cur_off_in_struct;
    if padding_bits != BitUnits(0) {
        let padding_field_ident = padding_field_ident_generator.generate();
        let padding_field_ty = mk_b_type(padding_bits)?;
        struct_fields_code.extend(quote! {
            pub #padding_field_ident: #padding_field_ty,
        });
    }

    let reg_struct_ident = mk_ident(&format!(
        "{}{}Reg",
        group_name.to_pascal_case(),
        reg_entry.reg.name.to_pascal_case()
    ));

    Ok(EmittedRegFieldTy {
        emitted_code: quote! {
            #[bitpiece]
            #[derive(Debug)]
            pub struct #reg_struct_ident {
                #struct_fields_code
            }
        },
        reg_field_ty_ident: reg_struct_ident.into_token_stream(),
    })
}

struct GeneratedFile {
    path: PathBuf,
    code: syn::File,
}
impl GeneratedFile {
    fn new(path: PathBuf, code: proc_macro2::TokenStream) -> Result<Self> {
        Ok(Self {
            path,
            code: syn::parse2(code.clone()).with_context(|| {
                format!(
                    "failed to parse generated code into a valid ast:\n{}\n",
                    code.to_string(),
                )
            })?,
        })
    }
}

fn write_generated_files<I: Iterator<Item = GeneratedFile>>(files: I) -> Result<()> {
    for file in files {
        if let Some(parent) = file.path.parent() {
            std::fs::create_dir_all(parent).with_context(|| {
                format!(
                    "failed to create parent {} of file {}",
                    parent.display(),
                    file.path.display()
                )
            })?
        }
        let formatted_code = prettyplease::unparse(&file.code);
        std::fs::write(&file.path, formatted_code)
            .with_context(|| format!("failed to write to file {}", file.path.display()))?;
    }
    Ok(())
}

pub struct RegMemMapEntry<'a> {
    pub reg: &'a RegisterInfo,
    pub addr_range: RegAddrRange,
    pub storage_ty: RegStorageType,
}
impl<'a> PartialEq for RegMemMapEntry<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.addr_range.off == other.addr_range.off
    }
}
impl<'a> Eq for RegMemMapEntry<'a> {}
impl<'a> PartialOrd for RegMemMapEntry<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.addr_range.off.partial_cmp(&other.addr_range.off)
    }
}
impl<'a> Ord for RegMemMapEntry<'a> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.addr_range.off.cmp(&other.addr_range.off)
    }
}

pub struct RegsMemMap<'a> {
    pub entries: SortedVec<RegMemMapEntry<'a>>,
}
impl<'a> RegsMemMap<'a> {
    pub fn new() -> Self {
        Self {
            entries: SortedVec::new(),
        }
    }
    pub fn from_regs<I: IntoIterator<Item = &'a RegisterCluster>>(regs: I) -> Result<Self> {
        let mut res = Self::new();
        for reg in regs {
            let reg = resolve_reg_cluster(reg);
            res.add_reg(reg)
                .with_context(|| format!("failed to process register {}", reg.name))?;
        }
        Ok(res)
    }
    pub fn add_reg(&mut self, reg: &'a RegisterInfo) -> Result<()> {
        let storage_ty = choose_reg_storage_type(reg)?;
        let new_entry = RegMemMapEntry {
            reg,
            addr_range: RegAddrRange {
                off: reg_get_addr_off(reg),
                size: reg_get_bit_len(reg)?.bytes(),
            },
            storage_ty,
        };

        // check for collisions
        if let Some(entry) = self
            .entries
            .iter()
            .find(|entry| entry.addr_range.intersects(&new_entry.addr_range))
        {
            bail!(
                "register {} with addr region {} intersects with register {} with addr range {}",
                new_entry.reg.name,
                new_entry.addr_range,
                entry.reg.name,
                entry.addr_range,
            )
        }

        self.entries.push(new_entry);

        Ok(())
    }
}
#[derive(Debug, Default)]
struct Group<'a> {
    name: &'a str,
    regs: &'a [RegisterCluster],
    desc: &'a str,
    peripherals: Vec<&'a PeripheralInfo>,
}
impl<'a> Group<'a> {
    fn new(name: &'a str, first_peripheral: &'a PeripheralInfo) -> Self {
        Self {
            name,
            regs: resolve_opt_vec(&first_peripheral.registers),
            peripherals: vec![first_peripheral],
            desc: resolve_opt_string(&first_peripheral.description),
        }
    }
    fn mk_mod_name(&self) -> String {
        self.name.to_snake_case()
    }
    fn mk_mod_file_name(&self) -> String {
        let mod_name = self.mk_mod_name();

        // avoid collision with the lib.rs file
        let mod_name = if mod_name == "lib" { "lib_" } else { &mod_name };

        format!("{}.rs", mod_name)
    }
    fn mk_mod_ident(&self) -> syn::Ident {
        mk_ident(&self.mk_mod_name())
    }
    fn mk_regs_struct_ident(&self) -> syn::Ident {
        mk_ident(&format!("{}Regs", self.name.to_pascal_case()))
    }
    fn emit_peripherals_regs_consts(&self) -> Result<proc_macro2::TokenStream> {
        let regs_struct_ident = self.mk_regs_struct_ident();
        self.peripherals
            .iter()
            .map(|peripheral| {
                let peripheral_regs_const_ident =
                    mk_ident(&format!("{}_REGS", peripheral.name.to_shouty_snake_case()));

                let base_addr_hex = syn::LitInt::new(
                    &format!("0x{:x}", peripheral.base_address),
                    proc_macro2::Span::call_site(),
                );

                Ok(quote! {
                    pub const #peripheral_regs_const_ident: ::volatile::VolatilePtr<'static, #regs_struct_ident> = unsafe {
                        ::volatile::VolatilePtr::new_restricted(
                            ::volatile::access::ReadWrite,
                            ::core::ptr::NonNull::new(#base_addr_hex as *mut #regs_struct_ident).unwrap(),
                        )
                    };
                })
            })
            .collect()
    }
    fn emit_regs_struct(&self) -> Result<proc_macro2::TokenStream> {
        let regs_type_ident = self.mk_regs_struct_ident();

        let regs_mem_map = RegsMemMap::from_regs(self.regs)?;

        let total_size = regs_mem_map
            .entries
            .iter()
            .map(|entry| entry.addr_range.end())
            .max()
            .unwrap_or(ByteUnits(0));

        let alignment = regs_mem_map
            .entries
            .iter()
            .map(|entry| entry.storage_ty.alignment())
            .max()
            .unwrap_or(ByteUnits(1));

        let total_aligned_size = align_up(total_size, alignment);

        let mut struct_fields_code = quote! {};
        let mut reg_field_types_code = quote! {};
        let mut cur_off_in_struct = ByteUnits(0);
        let mut padding_field_ident_generator = PaddingFieldIdentGenerator::new();
        for entry in &regs_mem_map.entries {
            let start_off = entry.addr_range.off;

            // add padding if needed
            if cur_off_in_struct < start_off {
                // NOTE: must cast to `usize` here, otherwise it emits the integer literal with a u64 postfix (e.g `3u64`).
                let padding = start_off - cur_off_in_struct;
                let padding_usize = padding.0 as usize;

                let padding_field_ident = padding_field_ident_generator.generate();

                struct_fields_code.extend(quote! {
                    pub #padding_field_ident: [u8; #padding_usize],
                });
                cur_off_in_struct += padding;
            }

            let field_name = mk_ident(&entry.reg.name.to_snake_case());
            let emitted_reg_field_ty = emit_reg_field_ty(self.name, entry)?;
            reg_field_types_code.extend(emitted_reg_field_ty.emitted_code);

            let field_ty = &emitted_reg_field_ty.reg_field_ty_ident;
            let desc = resolve_opt_string(&entry.reg.description);
            struct_fields_code.extend(quote! {
                #[doc = #desc]
                pub #field_name: #field_ty,
            });
            cur_off_in_struct += entry.storage_ty.byte_len();
        }

        // NOTE: must cast to `usize` here, otherwise it emits the integer literal with a u64 postfix (e.g `3u64`).
        let aligned_size_usize = total_aligned_size.0 as usize;
        let alignment_usize = alignment.0 as usize;
        let group_desc = self.desc;
        Ok(quote! {
            #reg_field_types_code

            #[doc = #group_desc]
            #[repr(C)]
            #[derive(Debug, Clone, ::volatile::VolatileFieldAccess)]
            pub struct #regs_type_ident {
                #struct_fields_code
            }

            const _: () = if ::core::mem::size_of::<#regs_type_ident>() != #aligned_size_usize {
                panic!("unexpected group regs struct size");
            };
            const _: () = if ::core::mem::align_of::<#regs_type_ident>() != #alignment_usize {
                panic!("unexpected group regs struct alignment");
            };
        })
    }
    fn emit_all(&self) -> Result<proc_macro2::TokenStream> {
        let regs_struct = self.emit_regs_struct()?;
        let peripherals_regs_consts = self.emit_peripherals_regs_consts()?;
        Ok(quote! {
            use bitpiece::*;
            #regs_struct
            #peripherals_regs_consts
        })
    }
}

fn resolve_maybe_array<T>(x: &svd_parser::svd::MaybeArray<T>) -> &T {
    match x {
        svd_parser::svd::MaybeArray::Single(single) => single,
        svd_parser::svd::MaybeArray::Array(_, _) => panic!("got an svd array after expansion"),
    }
}

fn mk_groups(device: &Device) -> Result<Vec<Group<'_>>> {
    let mut groups_by_name: HashMap<&str, Group<'_>> = HashMap::new();
    for peripheral in &device.peripherals {
        let peripheral = resolve_maybe_array(peripheral);
        match &peripheral.group_name {
            Some(group_name) => {
                let group_entry = groups_by_name.entry(group_name.as_str());
                match group_entry {
                    std::collections::hash_map::Entry::Occupied(mut occupied_entry) => {
                        let group = occupied_entry.get_mut();

                        let regs = resolve_opt_vec(&peripheral.registers);
                        if group.regs != regs {
                            bail!(
                                "peripherals {} and {} are in the same group but have different register structures",
                                peripheral.name,
                                group.peripherals[0].name
                            );
                        }

                        let desc = resolve_opt_string(&peripheral.description);
                        if group.desc != desc {
                            bail!(
                                "peripherals {} and {} are in the same group but have different descriptions: {:?} != {:?}",
                                peripheral.name,
                                group.peripherals[0].name,
                                desc,
                                group.desc
                            );
                        }

                        group.peripherals.push(peripheral);
                    }
                    std::collections::hash_map::Entry::Vacant(vacant_entry) => {
                        vacant_entry.insert(Group::new(group_name, peripheral));
                    }
                }
            }
            None => {
                let group_name = &peripheral.name;
                let prev_group =
                    groups_by_name.insert(group_name, Group::new(group_name, peripheral));
                if let Some(prev_group) = prev_group {
                    bail!("multiple groups named {}", prev_group.name)
                }
            }
        }
    }
    Ok(groups_by_name.into_values().collect())
}

fn run() -> Result<()> {
    let cli = Cli::parse();

    let svd_raw_xml =
        std::fs::read_to_string(cli.svd_file).context("failed to read input svd file")?;
    let device = svd_parser::parse_with_config(
        &svd_raw_xml,
        &svd_parser::Config::default()
            .validate_level(svd_parser::ValidateLevel::Strict)
            .expand_properties(true)
            .expand(true),
    )
    .context("failed to parse svd file")?;

    let groups = mk_groups(&device).context("failed to divide peripherals into groups")?;
    let groups_generated_files = groups
        .iter()
        .map(|group| {
            GeneratedFile::new(
                cli.out_dir.join(group.mk_mod_file_name()),
                group.emit_all()?,
            )
        })
        .collect::<Result<Vec<_>>>()?;

    let mod_declarations = groups.iter().map(|group| {
        let ident = group.mk_mod_ident();
        quote! {
            pub mod #ident;
        }
    });

    let lib_rs = GeneratedFile::new(
        cli.out_dir.join("lib.rs"),
        quote! {
            #![no_std]
            #(#mod_declarations)*
        },
    )?;

    let generated_files = std::iter::once(lib_rs).chain(groups_generated_files.into_iter());

    write_generated_files(generated_files)?;

    Ok(())
}

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {:#}", err)
    }
}
