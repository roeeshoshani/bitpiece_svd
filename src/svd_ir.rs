use std::collections::BTreeMap;

use anyhow::{Result, anyhow};

use svd_parser::{self, Config, svd};

use crate::{
    ident::ident,
    name::{group_key_from_peripheral, sanitize_mod_name},
};

#[derive(Debug, Clone)]
pub struct DeviceIr {
    pub groups: Vec<GroupIr>,
}

#[derive(Debug, Clone)]
pub struct GroupIr {
    /// Rust module name, e.g. "uart"
    pub module_name: String,

    /// Shared register-block type name, e.g. "UartRegs"
    pub regs_ty: syn::Ident,

    /// Items (registers) that define the reg block layout
    pub items: Vec<RegItemIr>,

    /// Peripheral instances that point at that reg block (UART0, UART1, ...)
    pub instances: Vec<InstanceIr>,
}

#[derive(Debug, Clone)]
pub struct InstanceIr {
    pub name: String,      // "UART0"
    pub base_address: u64, // 0x6000_0000
    pub description: Option<String>,
}

#[derive(Debug, Clone)]
pub struct RegItemIr {
    pub name: String,        // full path name (cluster prefixes included) for uniqueness
    pub field_name: String,  // snake_case field in Regs struct
    pub address_offset: u32, // byte offset in register block
    pub description: Option<String>,
    pub kind: RegKindIr,
}

#[derive(Debug, Clone)]
pub enum RegKindIr {
    /// A real register
    Register { reg: svd::RegisterInfo },
}

/// Parse and EXPAND. This resolves derivedFrom paths and expands arrays (peripheral/register/field),
/// and expands inherited properties (size/access/reset). See svd_parser::Config::expand and expand_properties.
pub fn parse_expanded(xml: &str) -> Result<svd::Device> {
    let cfg = Config::default().expand(true).expand_properties(true);

    svd_parser::parse_with_config(xml, &cfg).map_err(|e| anyhow!("SVD parse failed: {e:?}"))
}

pub fn build_device_ir(dev: &svd::Device) -> Result<DeviceIr> {
    // Expanded device should now have Peripheral::Single items (arrays expanded).
    let peripherals = dev.peripherals.iter().filter_map(|p| match p {
        svd::Peripheral::Single(info) => Some(info),
        svd::Peripheral::Array(_, _) => None, // shouldn't happen after expand, but ignore defensively
    });

    // Group peripherals into modules:
    // Prefer groupName if present; else derive from peripheral name (strip trailing digits).
    let mut groups_map: BTreeMap<String, Vec<&svd::PeripheralInfo>> = BTreeMap::new();
    for p in peripherals {
        let key = group_key_from_peripheral(p);
        groups_map.entry(key).or_default().push(p);
    }

    // Build groups.
    let mut groups = Vec::new();
    for (key, ps) in groups_map {
        let module_name = sanitize_mod_name(&key);

        // Decide a shared Regs layout:
        // We try to share if all members have the "same layout signature".
        // Otherwise, we fall back to the first peripheral's layout for now.
        // (You can extend this to split a group into multiple layouts.)
        let def = ps[0];

        let items = collect_register_items_flat(def)?;

        let regs_ty = ident(format!("{}Regs", heck::AsUpperCamelCase(&key)));

        let instances = ps
            .iter()
            .map(|p| InstanceIr {
                name: p.name.clone(),
                base_address: p.base_address as u64,
                description: p.description.clone(),
            })
            .collect();

        groups.push(GroupIr {
            module_name,
            regs_ty,
            items,
            instances,
        });
    }

    Ok(DeviceIr { groups })
}

/// Flatten clusters by prefixing names: CLUSTER_REG.
/// This keeps a correct address layout while staying simple.
fn collect_register_items_flat(p: &svd::PeripheralInfo) -> Result<Vec<RegItemIr>> {
    let regs = match &p.registers {
        Some(r) => r,
        None => return Ok(vec![]),
    };

    let mut out = Vec::new();
    for rc in regs {
        collect_rc(out.as_mut(), "", 0, rc)?;
    }

    out.sort_by_key(|x| x.address_offset);
    Ok(out)
}

fn collect_rc(
    out: &mut Vec<RegItemIr>,
    prefix: &str,
    base_off: u32,
    rc: &svd::RegisterCluster,
) -> Result<()> {
    match rc {
        svd::RegisterCluster::Register(r) => {
            // After expand, Register should be Single.
            let r = match r {
                svd::Register::Single(info) => info,
                svd::Register::Array(_, _) => return Ok(()), // should not happen after expand
            };

            let full_name = if prefix.is_empty() {
                r.name.clone()
            } else {
                format!("{prefix}_{}", r.name)
            };

            let mut field_name = heck::AsSnakeCase(&full_name).to_string();
            if crate::ident::ident(&field_name).to_string() != field_name {
                // normalize to the final safe form (e.g. continue -> continue_)
                field_name = crate::ident::ident(&field_name).to_string();
            }

            out.push(RegItemIr {
                name: full_name,
                field_name,
                address_offset: base_off + r.address_offset,
                description: r.description.clone(),
                kind: RegKindIr::Register { reg: r.clone() },
            });

            Ok(())
        }
        svd::RegisterCluster::Cluster(c) => {
            let cinfo = match c {
                svd::Cluster::Single(i) => i,
                svd::Cluster::Array(_, _) => return Ok(()), // should not happen after expand
            };

            let new_prefix = if prefix.is_empty() {
                cinfo.name.clone()
            } else {
                format!("{prefix}_{}", cinfo.name)
            };
            let new_base = base_off + cinfo.address_offset;

            for child in &cinfo.children {
                collect_rc(out, &new_prefix, new_base, child)?;
            }
            Ok(())
        }
    }
}
