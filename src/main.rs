use std::{fs, path::PathBuf};

use anyhow::{Context, Result};
use clap::Parser;

mod generate;
mod ident;
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
    generate::emit_crate(&args.out, &ir)?;

    eprintln!("Generated crate at: {}", args.out.display());
    Ok(())
}
