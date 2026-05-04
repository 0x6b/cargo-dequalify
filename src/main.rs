mod cli;

use std::env::args;

use anyhow::Result;
use clap::Parser;

fn main() -> Result<()> {
    let mut raw_args: Vec<String> = args().collect();
    if raw_args.get(1).is_some_and(|s| s == "dequalify") {
        raw_args.remove(1);
    }
    cli::run(cli::Cli::parse_from(&raw_args))
}
