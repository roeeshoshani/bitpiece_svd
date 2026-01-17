use std::{fs, path::PathBuf};

use anyhow::{Context, Result};
use clap::Parser;

mod generate;
mod name;
mod svd_ir;

#[derive(Debug, Parser)]
#[command(name = "svd2pac-bitpiece")]
struct Args {
    /// Input .svd file
    #[arg(long)]
    svd: PathBuf,

    /// Output directory for the generated PAC crate
    #[arg(long)]
    out: PathBuf,

    /// Name for the generated crate (Cargo.toml)
    #[arg(long, default_value = "device-pac")]
    crate_name: String,

    /// Generate #![no_std] in the output crate
    #[arg(long, default_value_t = true)]
    no_std: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();

    let xml = fs::read_to_string(&args.svd)
        .with_context(|| format!("reading SVD: {}", args.svd.display()))?;

    // 1) Parse an "expanded" device: resolves derivedFrom, expands arrays, fills inherited props.
    //    This is what we use for codegen correctness.
    let dev = svd_ir::parse_expanded(&xml)?;

    // 2) Build an IR that groups derived peripherals and decides shared register blocks.
    let ir = svd_ir::build_device_ir(&dev)?;

    // 3) Emit crate: Cargo.toml, lib.rs, and one module per group
    generate::emit_crate(&args.out, &args.crate_name, args.no_std, &ir)?;

    eprintln!("Generated crate at: {}", args.out.display());
    Ok(())
}
