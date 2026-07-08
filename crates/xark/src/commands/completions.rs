//! Shell completion generation for `xark`.
//!
//! Usage:
//!
//! ```text
//! # bash
//! xark completions bash > ~/.local/share/bash-completion/completions/xark
//!
//! # zsh
//! xark completions zsh  > ~/.local/share/zsh/site-functions/_xark
//!
//! # fish
//! xark completions fish > ~/.config/fish/completions/xark.fish
//!
//! # elvish
//! xark completions elvish > ~/.config/elvish/completions/xark.elv
//! ```
//!
//! Package maintainers can use this to ship completions alongside the binary.

use std::io;

use anyhow::Result;
use clap::{CommandFactory, Parser};
use clap_complete::Shell;

use super::Cli;

#[derive(Parser, Debug)]
pub struct CompletionsArgs {
    /// Shell to generate completions for.
    pub shell: Shell,
}

pub fn run(args: CompletionsArgs) -> Result<()> {
    let mut cmd = Cli::command();
    let name = cmd.get_name().to_string();
    clap_complete::generate(args.shell, &mut cmd, name, &mut io::stdout());
    Ok(())
}
