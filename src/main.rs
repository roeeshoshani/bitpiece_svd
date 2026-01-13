use std::path::PathBuf;

use anyhow::{Context, Result, bail};
use clap::Parser;
use derive_more::Display;
use heck::{ToPascalCase, ToShoutySnakeCase, ToSnakeCase};
use newtype_ops::newtype_ops;
use quote::{ToTokens, quote};
use serde::{Deserialize, Deserializer};
use sorted_vec::SortedVec;

#[derive(clap::Parser)]
pub struct Cli {
    pub svd_file: PathBuf,
}

fn mk_ident(s: &str) -> syn::Ident {
    syn::Ident::new(s, proc_macro2::Span::call_site())
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

fn choose_reg_storage_type(reg: &Reg) -> Result<RegStorageType> {
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
    pub reg: &'a Reg,
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
    pub fn from_regs<I: IntoIterator<Item = &'a Reg>>(regs: I) -> Result<Self> {
        let mut res = Self::new();
        for reg in regs {
            res.add_reg(reg)
                .context(format!("failed to process register {}", reg.name))?;
        }
        Ok(res)
    }
    pub fn add_reg(&mut self, reg: &'a Reg) -> Result<()> {
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
        let res = mk_ident(&format!("___padding{}", self.cur_field_index));
        self.cur_field_index += 1;
        res
    }
}

fn emit_peripheral(peripheral: &Peripheral) -> Result<proc_macro2::TokenStream> {
    let base_addr = peripheral.base_address.0;
    let peripheral_desc = &peripheral.description;

    let peripheral_regs_type_ident = mk_ident(&format!("{}Regs", peripheral.name.to_pascal_case()));
    let peripheral_regs_const_ident =
        mk_ident(&format!("{}_REGS", peripheral.name.to_shouty_snake_case()));

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

    if (peripheral_size % peripheral_alignment) != ByteUnits(0) {
        bail!(
            "peripheral size {} is not aligned to alignment of {}",
            peripheral_size,
            peripheral_alignment
        );
    }
    if (base_addr % peripheral_alignment) != ByteUnits(0) {
        bail!(
            "peripheral base address {} is not aligned to alignment of {}",
            base_addr,
            peripheral_alignment
        );
    }

    let mut struct_fields_code = quote! {};
    let mut cur_off_in_struct = ByteUnits(0);
    let mut padding_field_ident_generator = PaddingFieldIdentGenerator::new();
    for entry in &regs_mem_map.entries {
        let start_off = entry.addr_range.off;

        // add padding if needed
        if cur_off_in_struct < start_off {
            let padding = start_off - cur_off_in_struct;

            let padding_field_ident = padding_field_ident_generator.generate();

            struct_fields_code.extend(quote! {
                #padding_field_ident: [u8; #padding],
            });
            cur_off_in_struct += padding;
        }

        let field_name = entry.reg.name.to_snake_case();
        let field_ty = entry.storage_ty.uint_type();
        let desc = &entry.reg.description;
        struct_fields_code.extend(quote! {
            #[doc = #desc]
            #field_name: #field_ty,
        });
        cur_off_in_struct += entry.storage_ty.byte_len();
    }

    Ok(quote! {
        #[doc = #peripheral_desc]
        #[repr(C)]
        #[derive(Debug, Clone, ::volatile::VolatileFieldAccess)]
        pub struct #peripheral_regs_type_ident {
            #struct_fields_code
        }

        const _: () = if ::core::mem::size_of::<#peripheral_regs_type_ident>() != #peripheral_size {
            panic!("unexpected peripheral regs struct size");
        };
        const _: () = if ::core::mem::align_of::<#peripheral_regs_type_ident>() != #peripheral_alignment {
            panic!("unexpected peripheral regs struct alignment");
        };

        #[doc = #peripheral_desc]
        pub const #peripheral_regs_const_ident: ::volatile::VolatilePtr<'static, #peripheral_regs_type_ident> = unsafe {
            ::volatile::VolatilePtr::new_restricted(
                ::volatile::access::ReadWrite,
                ::core::ptr::NonNull::new(#base_addr as *mut #peripheral_regs_type_ident).unwrap(),
            )
        };
    })
}

fn run() -> Result<()> {
    let cli = Cli::parse();
    let svd = std::fs::read_to_string(cli.svd_file).context("failed to read input svd file")?;
    let device: Device = quick_xml::de::from_str(&svd).context("failed to parse svd file")?;
    let code = device
        .peripherals
        .peripheral
        .iter()
        .map(|peripheral| {
            emit_peripheral(peripheral).context(format!(
                "failed to emit code for peripheral {}",
                peripheral.name
            ))
        })
        .collect::<Result<proc_macro2::TokenStream>>()?;
    println!("{}", code.to_string());
    Ok(())
}

fn main() {
    if let Err(err) = run() {
        eprintln!("error: {:#}", err)
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
pub struct Device {
    pub peripherals: Peripherals,
    pub address_unit_bits: SvdNumBitUnits,
    pub width: SvdNumBitUnits,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Peripherals {
    pub peripheral: Vec<Peripheral>,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Peripheral {
    pub name: String,
    pub description: String,
    pub base_address: SvdNumByteUnits,
    #[serde(default)]
    pub registers: Regs,
}

#[derive(Deserialize, Debug, Default)]
#[serde(rename_all = "camelCase")]
pub struct Regs {
    pub register: Vec<Reg>,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Reg {
    pub name: String,
    pub description: String,
    pub address_offset: SvdNumByteUnits,
    pub size: SvdNumBitUnits,
    #[serde(default)]
    pub fields: RegFields,
}

#[derive(Deserialize, Debug, Default)]
#[serde(rename_all = "camelCase")]
pub struct RegFields {
    pub field: Vec<RegField>,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct RegField {
    pub name: String,
    pub description: String,
    pub bit_offset: SvdNumBitUnits,
    pub bit_width: SvdNumBitUnits,
}
