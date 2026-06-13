//! Helpers for arguments that are inferred from a Noir project when
//! running inside one, but required explicitly otherwise.

use clap::CommandFactory;
use clap::error::ErrorKind;

use crate::commands::Cli;

const SINGLE_NOTE: &str = "note: Run from inside a Noir project to infer this path,\n\
      pass --path <DIR> to a Noir project, or provide the\n\
      missing argument explicitly.";

const MULTI_NOTE: &str = "note: Run from inside a Noir project to infer paths,\n\
      pass --path <DIR> to a Noir project, or provide the\n\
      missing arguments explicitly.";

/// Emit a clap-styled error listing every conditional argument that is
/// missing because no Noir project was found to infer them from.
///
/// Accepts a slice of argument names as they should appear in the error
/// output (e.g. `"--artifact <PATH>"`). Reports *all* missing arguments
/// in a single error.
///
/// # Example output
///
/// ```text
/// error: the following required arguments were not provided:
///   --artifact <PATH>
///
/// note: Run from inside a Noir project to infer this path,
///       pass --path <DIR> to a Noir project, or provide the
///       missing argument explicitly.
///
/// Usage: inspect [OPTIONS]
///
/// For more information, try '--help'.
/// ```
pub fn bail_on_missing_args(subcmd: &str, missing: &[&str]) -> ! {
    let mut cmd = Cli::command();
    let sub = cmd
        .find_subcommand_mut(subcmd)
        .unwrap_or_else(|| panic!("{subcmd} subcommand not registered"));

    let list = missing
        .iter()
        .map(|a| format!("  {a}"))
        .collect::<Vec<_>>()
        .join("\n");

    let (verb, note) = if missing.len() == 1 {
        ("argument was", SINGLE_NOTE)
    } else {
        ("arguments were", MULTI_NOTE)
    };

    let msg = format!(
        "the following required {verb} not provided:\n\
         {list}\n\
         \n\
         {note}"
    );

    sub.error(ErrorKind::MissingRequiredArgument, msg).exit()
}
