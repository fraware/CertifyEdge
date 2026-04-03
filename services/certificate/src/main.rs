//! certctl — certificate CLI (minimal stub for Bazel `rust_binary`).

use clap::Parser;

#[derive(Parser)]
#[command(name = "certctl")]
struct Cli {
    #[arg(long)]
    version: bool,
}

fn main() {
    let cli = Cli::parse();
    if cli.version {
        println!("certctl {}", env!("CARGO_PKG_VERSION"));
    } else {
        println!("certctl: use --version");
    }
}
