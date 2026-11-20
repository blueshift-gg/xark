use pinocchio::error::{ProgramError, ToStr};

/// The program's own errors, as `ProgramError::Custom` codes. Every other failure
/// is a built-in: malformed instruction data, a missing signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum {{Error}} {
    /// The proof doesn't verify against the public inputs.
    InvalidProof = 0,
}

impl From<{{Error}}> for ProgramError {
    fn from(e: {{Error}}) -> Self {
        ProgramError::Custom(e as u32)
    }
}

impl TryFrom<u32> for {{Error}} {
    type Error = ProgramError;

    fn try_from(code: u32) -> Result<Self, Self::Error> {
        match code {
            0 => Ok(Self::InvalidProof),
            _ => Err(ProgramError::InvalidArgument),
        }
    }
}

impl ToStr for {{Error}} {
    fn to_str(&self) -> &'static str {
        match self {
            Self::InvalidProof => "InvalidProof: invalid proof",
        }
    }
}
