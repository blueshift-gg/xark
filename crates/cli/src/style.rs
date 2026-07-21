//! Minimal ANSI styling for the `xark` CLI: `#99FF00` branding plus warning /
//! error colors. A no-op when stderr is not a TTY or `NO_COLOR` is set, so piped
//! output (e.g. JSON diagnostics) never gets escape codes.

use std::io::IsTerminal;
use std::sync::OnceLock;

// Brand + status colors, bold. `#99FF00` = rgb(153, 255, 0).
const BRAND: &str = "\x1b[1;38;2;153;255;0m";
const WARN: &str = "\x1b[1;38;2;255;214;0m"; // yellow
const ERR: &str = "\x1b[1;38;2;255;85;85m"; // red
const DIM: &str = "\x1b[2m"; // faint — for inline `# comment` hints
const RESET: &str = "\x1b[0m";

/// Whether to emit escape codes: only for an interactive stderr, and never when
/// `NO_COLOR` is set (https://no-color.org). Cached after the first check.
fn enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| {
        if std::env::var_os("NO_COLOR").is_some() {
            return false; // https://no-color.org
        }
        // `CLICOLOR_FORCE` forces color even when piped (e.g. into a pager).
        std::env::var_os("CLICOLOR_FORCE").is_some() || std::io::stderr().is_terminal()
    })
}

fn wrap(code: &str, s: &str) -> String {
    if enabled() {
        format!("{code}{s}{RESET}")
    } else {
        s.to_string()
    }
}

/// Paint `s` in the brand color (`#99FF00`).
pub fn brand(s: &str) -> String {
    wrap(BRAND, s)
}
/// Paint `s` in the warning color (amber).
pub fn warn(s: &str) -> String {
    wrap(WARN, s)
}
/// Paint `s` in the error color (red).
pub fn err(s: &str) -> String {
    wrap(ERR, s)
}

/// Paint `s` faint — for the inline `# what this does` hints beside the
/// suggested next command, so the command itself stays prominent.
pub fn dim(s: &str) -> String {
    wrap(DIM, s)
}

/// Render a "Next steps" block: a branded header then one line per
/// `(command, hint)`, command in brand color and hint dimmed. One place so every
/// command's guided footer looks identical.
pub fn next_steps(steps: &[(String, &str)]) -> String {
    // Align hints into a column, measured by display columns not bytes (commands
    // may contain `…`, `‖`).
    let width = steps
        .iter()
        .map(|(cmd, _)| cmd.chars().count())
        .max()
        .unwrap_or(0);
    let mut out = brand("Next:");
    for (cmd, hint) in steps {
        out.push_str(&format!(
            "\n  {}{}  {}",
            brand(cmd),
            " ".repeat(width.saturating_sub(cmd.chars().count())),
            dim(&format!("# {hint}")),
        ));
    }
    out
}

/// The `xark` wordmark in brand color, prefixed to xark's own status lines.
pub fn tag() -> String {
    brand("xark")
}

/// clap help styling: brand-colored headers/usage, so `xark --help` is on-brand.
pub fn clap_styles() -> clap::builder::Styles {
    use clap::builder::styling::{AnsiColor, Color, RgbColor, Style};
    let brand = Style::new()
        .bold()
        .fg_color(Some(Color::Rgb(RgbColor(153, 255, 0))));
    clap::builder::Styles::styled()
        .header(brand)
        .usage(brand)
        .literal(Style::new().fg_color(Some(Color::Rgb(RgbColor(153, 255, 0)))))
        .placeholder(Style::new().fg_color(Some(Color::Ansi(AnsiColor::White))))
}
