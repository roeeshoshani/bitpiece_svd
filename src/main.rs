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

    let dev = svd_ir::parse_expanded(&xml)?;
    let ir = svd_ir::build_device_ir(&dev)?;
    generate::emit_crate(&args.out, &ir)?;

    eprintln!("Generated crate at: {}", args.out.display());
    Ok(())
}
