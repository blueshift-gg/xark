use anyhow::Result;
use clap::Parser;
use tracing_subscriber::EnvFilter;

mod commands;
mod noir_project;

use commands::Cli;

fn main() -> Result<()> {
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
    tracing_subscriber::fmt()
        .with_env_filter(filter)
        .with_target(false)
        .with_writer(std::io::stderr)
        .init();

    let cli = Cli::parse();
    cli.run()
}
