//! Compiler diagnostics for rejected circuits.
//!
//! Every rejection produces a readable `error:` line with an optional `help:` or
//! `note:` line, then aborts compilation with a non-zero exit code so callers
//! (and tests) can detect the failure.

use std::process;

/// A structured rejection of a circuit program.
#[derive(Debug, Clone)]
pub struct CompileError {
    pub message: String,
    pub help: Option<String>,
    pub note: Option<String>,
    /// Source location of the offending construct, when known. Attached at the
    /// rejection site (the innermost, most precise span wins) so the diagnostic
    /// can be routed through rustc's diagnostic context with a real span.
    pub span: Option<rustc_span::Span>,
}

impl CompileError {
    pub fn new(message: impl Into<String>) -> Self {
        CompileError {
            message: message.into(),
            help: None,
            note: None,
            span: None,
        }
    }

    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.note = Some(note.into());
        self
    }

    /// Attach `span` unconditionally (an explicit, precise location).
    #[allow(dead_code)]
    pub fn with_span(mut self, span: rustc_span::Span) -> Self {
        self.span = Some(span);
        self
    }

    /// Attach `span` only if none is set yet, so an inner error's precise span
    /// wins and the enclosing statement/terminator span is used as a fallback.
    pub fn or_span(mut self, span: rustc_span::Span) -> Self {
        if self.span.is_none() {
            self.span = Some(span);
        }
        self
    }

    /// Print the diagnostic to stderr in the documented format. Used by non-tcx
    /// callers (e.g. CLI argument errors) that have no rustc diagnostic context;
    /// inside the driver, rejections are routed through `tcx.dcx()` for spans.
    #[allow(dead_code)]
    pub fn emit(&self) {
        eprintln!("error: {}", self.message);
        if let Some(help) = &self.help {
            eprintln!("help: {help}");
        }
        if let Some(note) = &self.note {
            eprintln!("note: {note}");
        }
    }

    /// Print the diagnostic and terminate the process.
    #[allow(dead_code)]
    pub fn emit_and_exit(&self) -> ! {
        self.emit();
        process::exit(1);
    }
}

pub type CompileResult<T> = Result<T, CompileError>;
