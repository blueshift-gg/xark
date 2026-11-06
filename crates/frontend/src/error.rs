//! Compile errors with an optional source location, help and notes.

use std::fmt;

#[derive(Clone, Debug)]
pub struct CompileError {
    pub message: String,
    pub location: Option<String>,
    pub help: Vec<String>,
    pub notes: Vec<String>,
    /// The circuit itself diverged here (a panic, `unreachable`, a trap): on a
    /// witness-dependent branch, that arm is impossible for a valid witness.
    pub diverged: bool,
    /// Where the circuit module was when this failed (boxed: errors stay small).
    pub site: Option<Box<ErrorSite>>,
}

/// Where a lowering error happened.
#[derive(Clone, Debug)]
pub struct ErrorSite {
    /// The wasm call stack `(function index, pc)`, outermost first.
    pub stack: Vec<(u32, u32)>,
    /// The user source location it maps to (`file`, 1-based line, column), when
    /// the module has line tables.
    pub span: Option<(String, u32, u32)>,
}

pub type CompileResult<T> = Result<T, CompileError>;

impl CompileError {
    pub fn new(message: impl Into<String>) -> Self {
        CompileError {
            message: message.into(),
            location: None,
            help: Vec::new(),
            notes: Vec::new(),
            diverged: false,
            site: None,
        }
    }

    /// Mark as a divergence of the circuit (see [`CompileError::diverged`]).
    pub fn diverging(mut self) -> Self {
        self.diverged = true;
        self
    }

    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help.push(help.into());
        self
    }

    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    /// Attach `loc` unless a more specific location is already set.
    pub fn or_location(mut self, loc: impl FnOnce() -> Option<String>) -> Self {
        if self.location.is_none() {
            self.location = loc();
        }
        self
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)?;
        if let Some(loc) = &self.location {
            write!(f, "\n  --> {loc}")?;
        }
        for n in &self.notes {
            write!(f, "\n  = note: {n}")?;
        }
        for h in &self.help {
            write!(f, "\n  = help: {h}")?;
        }
        Ok(())
    }
}

impl std::error::Error for CompileError {}
