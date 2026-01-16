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
use serde::{Deserialize, Deserializer};
use sorted_vec::SortedVec;

#[derive(clap::Parser)]
pub struct Cli {
    pub svd_file: PathBuf,
    pub out_dir: PathBuf,
}

fn mk_ident(s: &str) -> Result<syn::Ident> {
    if s.is_empty() {
        bail!("can't create an empty ident");
    }

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
        return Ok(syn::Ident::new(&fixed, proc_macro2::Span::call_site()));
    }
    Ok(syn::Ident::new(&s, proc_macro2::Span::call_site()))
}

fn mk_peripheral_regs_struct_ident(peripheral_name: &str) -> Result<syn::Ident> {
    mk_ident(&format!("{}Regs", peripheral_name.to_pascal_case()))
}

fn mk_peripheral_mod_name(peripheral_name: &str) -> String {
    peripheral_name.to_snake_case()
}

fn mk_peripheral_mod_file_name(peripheral_name: &str) -> String {
    let mod_name = mk_peripheral_mod_name(peripheral_name);

    // avoid collision with the lib.rs file
    let mod_name = if mod_name == "lib" { "lib_" } else { &mod_name };

    format!("{}.rs", mod_name)
}

fn mk_peripheral_mod_ident(peripheral_name: &str) -> Result<syn::Ident> {
    mk_ident(&mk_peripheral_mod_name(peripheral_name))
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

fn choose_reg_storage_type(reg: &SvdReg) -> Result<RegStorageType> {
    let bit_len = reg.size.0;
    let res = match bit_len {
        BitUnits(8) | BitUnits(16) | BitUnits(32) | BitUnits(64) => {
            RegStorageType { bit_len: bit_len }
        }
        _ => bail!("invalid reg bit length {}", bit_len),
    };

    // sanity - make sure that the address offset is properly aligned to the type that was chosen according to the size.
    // for example, a register with a bit length of 32 must have a 4-byte aligned address offset.
    let address_offset: ByteUnits = reg.address_offset.0;
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

pub struct RegMemMapEntry<'a> {
    pub reg: &'a SvdReg,
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
    pub fn from_regs<I: IntoIterator<Item = &'a SvdReg>>(regs: I) -> Result<Self> {
        let mut res = Self::new();
        for reg in regs {
            res.add_reg(reg)
                .context(format!("failed to process register {}", reg.name))?;
        }
        Ok(res)
    }
    pub fn add_reg(&mut self, reg: &'a SvdReg) -> Result<()> {
        let storage_ty = choose_reg_storage_type(reg)?;
        let new_entry = RegMemMapEntry {
            reg,
            addr_range: RegAddrRange {
                off: reg.address_offset.0,
                size: reg.size.0.bytes(),
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
        res.unwrap()
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
    mk_ident(&format!("B{}", bit_len))
}

struct EmittedRegFieldTy {
    emitted_code: proc_macro2::TokenStream,
    reg_field_ty_ident: proc_macro2::TokenStream,
}

fn emit_reg_field_ty(
    peripheral: &SvdPeripheral,
    reg_entry: &RegMemMapEntry,
) -> Result<EmittedRegFieldTy> {
    if reg_entry.reg.fields.field.is_empty() {
        return Ok(EmittedRegFieldTy {
            emitted_code: quote! {},
            reg_field_ty_ident: reg_entry.storage_ty.uint_type().into_token_stream(),
        });
    }

    if reg_entry.reg.fields.field.len() == 1 {
        let field = &reg_entry.reg.fields.field[0];

        // a single field which covers the entire register
        if field.bit_offset.0 == BitUnits(0) && field.bit_width.0 == reg_entry.storage_ty.bit_len {
            return Ok(EmittedRegFieldTy {
                emitted_code: quote! {},
                reg_field_ty_ident: reg_entry.storage_ty.uint_type().into_token_stream(),
            });
        }
    }

    let mut struct_fields_code = quote! {};
    let mut cur_off_in_struct = BitUnits(0);
    let mut padding_field_ident_generator = PaddingFieldIdentGenerator::new();
    let sorted_fields = {
        let mut fields = reg_entry.reg.fields.field.clone();
        fields.sort_unstable_by_key(|field| field.bit_offset);
        fields
    };
    for field in &sorted_fields {
        let start_off = field.bit_offset.0;

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

        let field_name = mk_ident(&field.name.to_snake_case())?;
        let field_ty = mk_b_type(field.bit_width.0)?;
        let desc = &field.description;
        struct_fields_code.extend(quote! {
            #[doc = #desc]
            pub #field_name: #field_ty,
        });
        cur_off_in_struct += field.bit_width.0;
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
        peripheral.name.to_pascal_case(),
        reg_entry.reg.name.to_pascal_case()
    ))?;

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
struct PeripheralGeneratedMod {
    mod_ident: syn::Ident,
    mod_file_path: PathBuf,
    mod_file_code: syn::File,
}

struct GeneratedFile {
    path: PathBuf,
    code: syn::File,
}

fn write_generated_files<I: Iterator<Item = GeneratedFile>>(files: I) -> Result<()> {
    for file in files {
        let formatted_code = prettyplease::unparse(&file.code);
        std::fs::write(&file.path, formatted_code)
            .context(format!("failed to write to file {}", file.path.display()))?;
    }
    Ok(())
}

fn run() -> Result<()> {
    let cli = Cli::parse();
    let svd = std::fs::read_to_string(cli.svd_file).context("failed to read input svd file")?;
    let device: SvdDevice = quick_xml::de::from_str(&svd).context("failed to parse svd file")?;
    let peripherals = Peripherals::from_svd(&device.peripherals);
    let peripheral_mods = peripherals
        .names()
        .map(|peripheral_name| {
            let raw_code = peripherals.emit_one(peripheral_name)?;
            let mod_file_code = syn::parse2(raw_code).context(format!(
                "failed to parse generated code of peripheral {} into a valid ast",
                peripheral_name
            ))?;
            Ok(PeripheralGeneratedMod {
                mod_ident: mk_peripheral_mod_ident(peripheral_name)?,
                mod_file_path: cli
                    .out_dir
                    .join(mk_peripheral_mod_file_name(peripheral_name)),
                mod_file_code,
            })
        })
        .collect::<Result<Vec<_>>>()?;

    let mod_declarations = peripheral_mods.iter().map(|peripheral_mod| {
        let ident = &peripheral_mod.mod_ident;
        quote! {
            pub mod #ident;
        }
    });

    let lib_rs_code = quote! {
        #![no_std]
        #(#mod_declarations)*
    };
    let lib_rs_file: syn::File =
        syn::parse2(lib_rs_code).context("failed to parse generated code into a valid ast")?;

    let generated_files = std::iter::once(GeneratedFile {
        path: cli.out_dir.join("lib.rs"),
        code: lib_rs_file,
    })
    .chain(
        peripheral_mods
            .into_iter()
            .map(|peripheral_mod| GeneratedFile {
                path: peripheral_mod.mod_file_path,
                code: peripheral_mod.mod_file_code,
            }),
    );

    write_generated_files(generated_files)?;

    Ok(())
}

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {:#}", err)
    }
}

struct Peripherals<'a>(HashMap<&'a str, &'a SvdPeripheral>);
impl<'a> Peripherals<'a> {
    fn from_svd(svd_peripherals: &'a SvdPeripherals) -> Self {
        Self(
            svd_peripherals
                .peripheral
                .iter()
                .map(|x| (x.name.as_str(), x))
                .collect(),
        )
    }

    fn names(&self) -> impl Iterator<Item = &'a str> {
        self.0.keys().copied()
    }

    fn find_root_name(&self, peripheral_name: &'a str) -> &'a str {
        let mut cur_name = peripheral_name;
        loop {
            let cur_peripheral = &self.0[peripheral_name];
            match &cur_peripheral.derived_from {
                Some(parent) => cur_name = parent,
                None => return cur_name,
            }
        }
    }

    fn emit_one(&self, peripheral_name: &str) -> Result<proc_macro2::TokenStream> {
        let peripheral = &self.0[peripheral_name];
        let base_addr = peripheral.base_address.0;
        let peripheral_desc = &peripheral.description;

        let peripheral_regs_const_ident =
            mk_ident(&format!("{}_REGS", peripheral.name.to_shouty_snake_case()))?;

        let (regs_type_ident, extra_code) = match &peripheral.derived_from {
            Some(derived_from) => {
                let root_peripheral_name = self.find_root_name(derived_from);
                let root_peripheral_mod_ident = mk_peripheral_mod_ident(root_peripheral_name)?;
                let root_peripheral_regs_struct_ident =
                    mk_peripheral_regs_struct_ident(root_peripheral_name)?;

                // need to import the regs struct of the root peripheral from which we are derived.
                let extra_code = quote! {
                    pub use super::#root_peripheral_mod_ident::#root_peripheral_regs_struct_ident;
                };

                (root_peripheral_regs_struct_ident, extra_code)
            }
            None => {
                let peripheral_regs_type_ident = mk_peripheral_regs_struct_ident(&peripheral.name)?;

                let regs_mem_map = RegsMemMap::from_regs(&peripheral.registers.register)?;

                let peripheral_size = regs_mem_map
                    .entries
                    .iter()
                    .map(|entry| entry.addr_range.end())
                    .max()
                    .unwrap_or(ByteUnits(0));

                let peripheral_alignment = regs_mem_map
                    .entries
                    .iter()
                    .map(|entry| entry.storage_ty.alignment())
                    .max()
                    .unwrap_or(ByteUnits(1));

                if (base_addr % peripheral_alignment) != ByteUnits(0) {
                    bail!(
                        "peripheral base address {} is not aligned to alignment of {}",
                        base_addr,
                        peripheral_alignment
                    );
                }

                let peripheral_aligned_size = align_up(peripheral_size, peripheral_alignment);

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

                    let field_name = mk_ident(&entry.reg.name.to_snake_case())?;
                    let emitted_reg_field_ty = emit_reg_field_ty(peripheral, entry)?;
                    reg_field_types_code.extend(emitted_reg_field_ty.emitted_code);

                    let field_ty = &emitted_reg_field_ty.reg_field_ty_ident;
                    let desc = &entry.reg.description;
                    struct_fields_code.extend(quote! {
                        #[doc = #desc]
                        pub #field_name: #field_ty,
                    });
                    cur_off_in_struct += entry.storage_ty.byte_len();
                }

                // NOTE: must cast to `usize` here, otherwise it emits the integer literal with a u64 postfix (e.g `3u64`).
                let aligned_size_usize = peripheral_aligned_size.0 as usize;
                let alignment_usize = peripheral_alignment.0 as usize;
                let code = quote! {
                    #reg_field_types_code

                    #[doc = #peripheral_desc]
                    #[repr(C)]
                    #[derive(Debug, Clone, ::volatile::VolatileFieldAccess)]
                    pub struct #peripheral_regs_type_ident {
                        #struct_fields_code
                    }

                    const _: () = if ::core::mem::size_of::<#peripheral_regs_type_ident>() != #aligned_size_usize {
                        panic!("unexpected peripheral regs struct size");
                    };
                    const _: () = if ::core::mem::align_of::<#peripheral_regs_type_ident>() != #alignment_usize {
                        panic!("unexpected peripheral regs struct alignment");
                    };
                };
                (peripheral_regs_type_ident, code)
            }
        };

        let base_addr_hex = syn::LitInt::new(
            &format!("0x{:x}", base_addr.0),
            proc_macro2::Span::call_site(),
        );

        Ok(quote! {
            #[allow(unused_imports)]
            use bitpiece::*;

            #extra_code

            #[doc = #peripheral_desc]
            pub const #peripheral_regs_const_ident: ::volatile::VolatilePtr<'static, #regs_type_ident> = unsafe {
                ::volatile::VolatilePtr::new_restricted(
                    ::volatile::access::ReadWrite,
                    ::core::ptr::NonNull::new(#base_addr_hex as *mut #regs_type_ident).unwrap(),
                )
            };
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SvdNumBitUnits(pub BitUnits);
impl<'de> Deserialize<'de> for SvdNumBitUnits {
    fn deserialize<D>(deserializer: D) -> Result<Self, <D as Deserializer<'de>>::Error>
    where
        D: Deserializer<'de>,
    {
        let num = SvdNum::deserialize(deserializer)?;
        Ok(SvdNumBitUnits(BitUnits(num.0)))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SvdNumByteUnits(pub ByteUnits);
impl<'de> Deserialize<'de> for SvdNumByteUnits {
    fn deserialize<D>(deserializer: D) -> Result<Self, <D as Deserializer<'de>>::Error>
    where
        D: Deserializer<'de>,
    {
        let num = SvdNum::deserialize(deserializer)?;
        Ok(SvdNumByteUnits(ByteUnits(num.0)))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SvdNum(pub u64);
impl<'de> Deserialize<'de> for SvdNum {
    fn deserialize<D>(deserializer: D) -> Result<Self, <D as Deserializer<'de>>::Error>
    where
        D: Deserializer<'de>,
    {
        let as_str = <&'de str>::deserialize(deserializer)?.trim();
        let as_int = if let Some(hex_str) = as_str.strip_prefix("0x") {
            u64::from_str_radix(hex_str, 16).map_err(serde::de::Error::custom)?
        } else if let Some(binary_str) = as_str.strip_prefix("#") {
            u64::from_str_radix(binary_str, 2).map_err(serde::de::Error::custom)?
        } else {
            u64::from_str_radix(as_str, 10).map_err(serde::de::Error::custom)?
        };
        Ok(SvdNum(as_int))
    }
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct SvdDevice {
    pub peripherals: SvdPeripherals,
    pub address_unit_bits: SvdNumBitUnits,
    pub width: SvdNumBitUnits,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct SvdPeripherals {
    pub peripheral: Vec<SvdPeripheral>,
}

#[derive(Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct SvdPeripheral {
    pub name: String,
    pub description: String,
    pub base_address: SvdNumByteUnits,
    #[serde(default)]
    pub registers: SvdRegs,
    #[serde(rename = "@derivedFrom")]
    pub derived_from: Option<String>,
}

#[derive(Deserialize, Debug, Clone, Default)]
#[serde(rename_all = "camelCase")]
pub struct SvdRegs {
    pub register: Vec<SvdReg>,
}

#[derive(Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct SvdReg {
    pub name: String,
    pub description: String,
    pub address_offset: SvdNumByteUnits,
    pub size: SvdNumBitUnits,
    #[serde(default)]
    pub fields: SvdRegFields,
}

#[derive(Deserialize, Debug, Clone, Default)]
#[serde(rename_all = "camelCase")]
pub struct SvdRegFields {
    pub field: Vec<SvdRegField>,
}

#[derive(Deserialize, Debug, Clone)]
#[serde(rename_all = "camelCase")]
pub struct SvdRegField {
    pub name: String,
    pub description: String,
    pub bit_offset: SvdNumBitUnits,
    pub bit_width: SvdNumBitUnits,
}
