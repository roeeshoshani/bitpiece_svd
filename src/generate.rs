use anyhow::{Context, Result};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::{fs, path::Path};

use crate::svd_ir::{DeviceIr, GroupIr, RegKindIr};

pub fn emit_crate(out_dir: &Path, crate_name: &str, no_std: bool, ir: &DeviceIr) -> Result<()> {
    fs::create_dir_all(out_dir.join("src"))?;

    emit_lib_rs(out_dir, no_std, ir)?;
    for g in &ir.groups {
        emit_group_module(out_dir, g)?;
    }

    Ok(())
}

fn emit_lib_rs(out_dir: &Path, no_std: bool, ir: &DeviceIr) -> Result<()> {
    let mods = ir.groups.iter().map(|g| {
        let m = syn::Ident::new(&g.module_name, proc_macro2::Span::call_site());
        quote!(pub mod #m;)
    });

    let top = if no_std { quote!(#![no_std]) } else { quote!() };

    let file = quote! {
        #top
        #(#mods)*
    };

    write_rust_file(out_dir.join("src").join("lib.rs"), file)
}

fn emit_group_module(out_dir: &Path, g: &GroupIr) -> Result<()> {
    let mod_path = out_dir.join("src").join(format!("{}.rs", g.module_name));

    // Register field structs (bitpiece) + register block struct + instance constants.
    let reg_structs = g.items.iter().filter_map(|it| match &it.kind {
        RegKindIr::Register { reg } => Some(gen_register_type(g, it, reg)),
    });

    let regs_block = gen_regs_block_struct(g);

    let instances = gen_instance_consts(g);

    let file = quote! {
        // Auto-generated. Do not edit.

        use bitpiece::*;
        use core::ptr::NonNull;

        #(#reg_structs)*

        #regs_block

        #instances
    };

    write_rust_file(mod_path, file)
}

fn gen_register_type(
    g: &GroupIr,
    it: &crate::svd_ir::RegItemIr,
    reg: &svd_parser::svd::RegisterInfo,
) -> TokenStream {
    let ty_name = format_ident!(
        "{}{}Reg",
        g.regs_ty.to_string().trim_end_matches("Regs"),
        pascal(&it.name)
    );
    let desc_attr = reg.description.as_ref().map(|d| quote!(#[doc = #d]));

    // If no fields, we don't generate a bitpiece struct; we will use a primitive in the block.
    let fields = match &reg.fields {
        Some(v) if !v.is_empty() => v,
        _ => return quote!(),
    };

    // register size bits (expand_properties should provide this)
    let size_bits = reg.properties.size.unwrap_or(32);

    // only use bitpiece for <= 64 bits
    if size_bits > 64 {
        return quote!();
    }

    // Collect fields as (lsb,width,name,doc).
    let mut finfo = Vec::new();
    for f in fields.iter() {
        let f = match f {
            svd_parser::svd::Field::Single(info) => info,
            svd_parser::svd::Field::Array(_, _) => continue, // shouldn't happen after expand
        };
        let lsb = f.lsb();
        let w = f.bit_width();
        finfo.push((lsb, w, f.name.clone(), f.description.clone()));
    }

    finfo.sort_by_key(|x| x.0);

    // Build bitpiece fields + padding.
    let mut ts = TokenStream::new();
    let mut next_bit: u32 = 0;
    let mut pad_i: usize = 0;

    for (lsb, w, name, doc) in finfo {
        if lsb > next_bit {
            let gap = lsb - next_bit;
            let pad_name = format_ident!("svd_padding_{}", pad_i);
            let pad_ty = format_ident!("B{}", gap);
            ts.extend(quote!(pub #pad_name: #pad_ty,));
            pad_i += 1;
        }

        let field_ident = format_ident!("{}", heck::AsSnakeCase(&name).to_string());
        let field_ty = format_ident!("B{}", w);

        if let Some(d) = doc {
            ts.extend(quote!(#[doc = #d]));
        }
        ts.extend(quote!(pub #field_ident: #field_ty,));

        next_bit = lsb + w;
    }

    if next_bit < size_bits {
        let gap = size_bits - next_bit;
        let pad_name = format_ident!("svd_padding_{}", pad_i);
        let pad_ty = format_ident!("B{}", gap);
        ts.extend(quote!(pub #pad_name: #pad_ty,));
    }

    quote! {
        #desc_attr
        #[bitpiece]
        #[derive(Debug)]
        pub struct #ty_name {
            #ts
        }
    }
}

fn gen_regs_block_struct(g: &GroupIr) -> TokenStream {
    let regs_ty = &g.regs_ty;

    // Sort by address and insert byte padding.
    let mut items = g.items.clone();
    items.sort_by_key(|it| it.address_offset);

    let mut fields_ts = TokenStream::new();
    let mut cur: u32 = 0;
    let mut pad_i: usize = 0;

    for it in items {
        let off = it.address_offset;
        if off > cur {
            let gap = (off - cur) as usize;
            let pad_name = format_ident!("_reserved{}", pad_i);
            fields_ts.extend(quote!(pub #pad_name: [u8; #gap],));
            pad_i += 1;
            cur = off;
        }

        let field_ident = format_ident!("{}", it.field_name);
        let doc_attr = it.description.as_ref().map(|d| quote!(#[doc = #d]));

        let (field_ty, size_bytes) = match &it.kind {
            RegKindIr::Register { reg } => {
                let size_bits = reg.properties.size.unwrap_or(32);
                let size_bytes = ((size_bits + 7) / 8) as u32;

                // If we generated a bitpiece type (has fields and <=64 bits), use it, else primitive.
                let has_fields = reg.fields.as_ref().map(|v| !v.is_empty()).unwrap_or(false);
                if has_fields && size_bits <= 64 {
                    let ty_name = format_ident!(
                        "{}{}Reg",
                        regs_ty.to_string().trim_end_matches("Regs"),
                        pascal(&it.name)
                    );
                    (quote!(#ty_name), size_bytes)
                } else {
                    let prim = storage_ty(size_bits);
                    (quote!(#prim), size_bytes)
                }
            }
        };

        fields_ts.extend(quote! {
            #doc_attr
            pub #field_ident: #field_ty,
        });

        cur += size_bytes;
    }

    quote! {
        #[repr(C)]
        #[derive(Debug, Clone, ::volatile::VolatileFieldAccess)]
        pub struct #regs_ty {
            #fields_ts
        }
    }
}

fn gen_instance_consts(g: &GroupIr) -> TokenStream {
    let regs_ty = &g.regs_ty;

    let consts = g.instances.iter().map(|inst| {
        let cname = format_ident!("{}_REGS", inst.name);
        let base = inst.base_address as usize;
        let doc_attr = inst.description.as_ref().map(|d| quote!(#[doc = #d]));

        quote! {
            #doc_attr
            pub const #cname: ::volatile::VolatilePtr<'static, #regs_ty> = unsafe {
                ::volatile::VolatilePtr::new_restricted(
                    ::volatile::access::ReadWrite,
                    NonNull::new(#base as *mut #regs_ty).unwrap(),
                )
            };
        }
    });

    quote!(#(#consts)*)
}

fn write_rust_file(path: std::path::PathBuf, ts: TokenStream) -> Result<()> {
    let file: syn::File =
        syn::parse2(ts).context("generated tokens didn't parse as a Rust file")?;
    let pretty = prettyplease::unparse(&file);
    fs::write(&path, pretty).with_context(|| format!("write {}", path.display()))?;
    Ok(())
}

fn storage_ty(bits: u32) -> syn::Ident {
    match bits {
        0..=8 => format_ident!("u8"),
        9..=16 => format_ident!("u16"),
        17..=32 => format_ident!("u32"),
        33..=64 => format_ident!("u64"),
        65..=128 => format_ident!("u128"),
        _ => format_ident!("u32"),
    }
}

fn pascal(s: &str) -> String {
    heck::AsUpperCamelCase(s).to_string()
}
