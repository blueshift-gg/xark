//! Witness file (.gz) parsing.
//!
//! Defers all serialization to `acir::native_types::WitnessStack`, then
//! exposes the inner witness map in field-agnostic form for downstream code.

use std::collections::{BTreeMap, HashMap};
use std::path::Path;

use acir::FieldElement;
use acir::native_types::{Witness, WitnessStack};
use ark_bn254::Fr;

use crate::artifact::WitnessIndex;
use crate::error::BackendError;
use crate::field::noir_field_to_fr;

/// A map from witness index to field value. Holds the witness for one ACIR
/// function. For multi-function programs, see [`callee_witnesses`]
/// (populated when the witness stack carries more than one entry).
#[derive(Clone, Debug, Default)]
pub struct WitnessMap<F: Clone> {
    pub values: BTreeMap<WitnessIndex, F>,
    /// Per-function-index witness maps for callee functions referenced via
    /// `Opcode::Call`. Populated by the parser when the WitnessStack has
    /// multiple entries. The main function (index 0) lives in `values`;
    /// callees live here.
    pub callee_witnesses: HashMap<u32, BTreeMap<WitnessIndex, F>>,
}

impl<F: Clone> WitnessMap<F> {
    pub fn new() -> Self {
        Self {
            values: BTreeMap::new(),
            callee_witnesses: HashMap::new(),
        }
    }
    pub fn insert(&mut self, idx: WitnessIndex, value: F) -> Option<F> {
        self.values.insert(idx, value)
    }
    pub fn get(&self, idx: &WitnessIndex) -> Option<&F> {
        self.values.get(idx)
    }
    pub fn contains(&self, idx: &WitnessIndex) -> bool {
        self.values.contains_key(idx)
    }
    pub fn len(&self) -> usize {
        self.values.len()
    }
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }
    /// Returns the callee witness map for function index `id`, if present.
    pub fn callee(&self, id: u32) -> Option<&BTreeMap<WitnessIndex, F>> {
        self.callee_witnesses.get(&id)
    }
}

/// Parse a `target/<name>.gz` witness file produced by `nargo execute`.
pub fn parse_witness_file(path: &Path) -> Result<WitnessMap<Fr>, BackendError> {
    let bytes = std::fs::read(path)?;
    parse_witness_bytes(&bytes)
}

/// Parse raw witness file bytes.
pub fn parse_witness_bytes(bytes: &[u8]) -> Result<WitnessMap<Fr>, BackendError> {
    let mut stack: WitnessStack<FieldElement> = WitnessStack::deserialize(bytes)
        .map_err(|e| BackendError::WitnessParse(format!("witness stack decode: {e}")))?;

    if stack.length() == 0 {
        return Err(BackendError::WitnessParse(
            "witness stack is empty".to_string(),
        ));
    }

    // For multi-function programs, the witness stack carries one
    // entry per function. Top of stack (index 0) is `main`; remaining entries
    // are callees keyed by their `AcirFunctionId`.
    let mut out = WitnessMap::<Fr>::new();
    let mut main_seen = false;
    while let Some(item) = stack.pop() {
        let mut map: BTreeMap<WitnessIndex, Fr> = BTreeMap::new();
        for (witness, value) in item.witness.into_iter() {
            map.insert(WitnessIndex(witness.0), noir_field_to_fr(&value));
        }
        if item.index == 0 && !main_seen {
            out.values = map;
            main_seen = true;
        } else {
            out.callee_witnesses.insert(item.index, map);
        }
    }
    if !main_seen {
        return Err(BackendError::WitnessParse(
            "witness stack has no entry for the main function (index 0)".to_string(),
        ));
    }
    Ok(out)
}

/// Convert directly from an in-memory acir [`acir::native_types::WitnessMap`].
pub fn witness_map_from_acir(map: acir::native_types::WitnessMap<FieldElement>) -> WitnessMap<Fr> {
    let mut out = WitnessMap::<Fr>::new();
    for (Witness(idx), value) in map.into_iter() {
        out.insert(WitnessIndex(idx), noir_field_to_fr(&value));
    }
    out
}

/// Witness namespace offset used during Call lowering. Each Call rewrites the
/// callee's witness indices by adding this offset, so they don't collide with
/// the main function's witness namespace. We multiply by the call-site index
/// at the call site to keep different calls from overlapping.
pub const CALLEE_NAMESPACE_STRIDE: u32 = 1 << 24;
