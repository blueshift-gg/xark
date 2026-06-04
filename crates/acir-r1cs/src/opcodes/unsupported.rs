//! Helpers for turning unsupported opcodes into [`BackendError`] values.

use acir::circuit::Opcode;
use acir::FieldElement;

use crate::error::BackendError;
use crate::opcodes::classify;

/// Build the explicit "unsupported opcode" error for the opcode at `index`.
pub fn unsupported_error(index: usize, opcode: &Opcode<FieldElement>) -> BackendError {
    let class = classify(opcode);
    BackendError::UnsupportedOpcode {
        opcode: class.display_name(),
        index,
        help: class.help(),
    }
}
