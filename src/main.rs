use serde::{Deserialize, Deserializer};

fn main() {
    let svd = std::fs::read_to_string("./esp32c3.svd").unwrap();
    let device: Device = quick_xml::de::from_str(&svd).unwrap();
    println!("{:#?}", device);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct AnyBaseU64(pub u64);
impl<'de> Deserialize<'de> for AnyBaseU64 {
    fn deserialize<D>(deserializer: D) -> Result<Self, <D as Deserializer<'de>>::Error>
    where
        D: Deserializer<'de>,
    {
        let as_str = <&'de str>::deserialize(deserializer)?;
        let trimmed_str = as_str.trim();
        let as_int = parse_int::parse(trimmed_str).map_err(serde::de::Error::custom)?;
        Ok(AnyBaseU64(as_int))
    }
}

#[derive(Deserialize, Debug)]
#[serde(rename_all = "camelCase")]
pub struct Device {
    pub peripherals: Vec<Peripherals>,
    pub address_unit_bits: AnyBaseU64,
    pub width: AnyBaseU64,
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
    pub base_address: AnyBaseU64,
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
    pub address_offset: AnyBaseU64,
    pub size: AnyBaseU64,
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
    pub bit_offset: AnyBaseU64,
    pub bit_width: AnyBaseU64,
}
