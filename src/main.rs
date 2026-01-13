use serde::{Deserialize, Deserializer};

fn main() {
    let svd = std::fs::read_to_string("./esp32c3.svd").unwrap();
    let device: Device = quick_xml::de::from_str(&svd).unwrap();
    assert_eq!(device.width, device.address_unit_bits);
    println!("{:#?}", device);
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
    pub peripherals: Vec<Peripherals>,
    pub address_unit_bits: SvdNum,
    pub width: SvdNum,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Peripherals {
    pub peripheral: Vec<Peripheral>,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Peripheral {
    pub name: Option<String>,
    pub description: Option<String>,
    pub base_address: SvdNum,
    pub registers: Option<Vec<Regs>>,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Regs {
    pub register: Vec<Reg>,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Reg {
    pub name: String,
    pub description: String,
    pub address_offset: SvdNum,
    pub size: SvdNum,
    pub fields: Option<Vec<RegFields>>,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct RegFields {
    pub field: Vec<RegField>,
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct RegField {
    pub name: String,
    pub description: String,
    pub bit_offset: SvdNum,
    pub bit_width: SvdNum,
}
