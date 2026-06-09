//! Poseidon2 permutation gadget over BN254 Fr.
//!
//! Implements the Poseidon2 permutation that Noir emits as
//! `BlackBoxFuncCall::Poseidon2Permutation`. Round constants, internal-matrix
//! diagonal, S-box exponent (`x^5`), state width (`t = 4`), and round structure
//! (`R_F = 8` full rounds, `R_P = 56` partial rounds) all match the canonical
//! BN254 reference implementation from
//! `acvm-repo/bn254_blackbox_solver/src/poseidon2.rs` in Noir v1.0.0-beta.22.
//!
//! Round structure (mirrors Noir / Barretenberg):
//!
//! 1. Initial linear layer: `M_E * state` (the 4x4 external matrix).
//! 2. `R_F / 2 = 4` external rounds: add round constants → S-box on all → `M_E`.
//! 3. `R_P = 56` internal rounds: add `rc[r][0]` to `state[0]` → S-box on
//!    `state[0]` → `M_I * state` (internal matrix using the diagonal).
//! 4. Remaining `R_F / 2 = 4` external rounds: add round constants → S-box on
//!    all → `M_E`.
//!
//! Each S-box `x^5` is 3 multiplication constraints (`t = x*x`, `u = t*t`,
//! `out = u*x`). Linear layers fold into LCs and incur no fresh constraints
//! on their own; we still allocate one fresh witness per state cell per round
//! to keep linear-combination sizes bounded and to give us a clean witness
//! handle for the next round's S-box / matrix mix.

// The `for r in start..end {... rc_table[r]... }` loops below are clearer as
// indexed range loops (the index `r` is the round number, used in trace logs
// and round-half/internal-round branching) than as `iter().skip(...).take(...)`
// chains.
#![allow(clippy::needless_range_loop)]

use std::sync::OnceLock;

use ark_bn254::Fr;
use ark_ff::{One, PrimeField, Zero};
use ark_relations::gr1cs::{LinearCombination, SynthesisError, Variable};

use crate::r1cs_builder::R1csBuilder;

/// Poseidon2 state width over BN254 Fr (per Noir's `POSEIDON2_CONFIG`).
pub const T: usize = 4;
/// Number of full rounds.
pub const ROUNDS_F: usize = 8;
/// Number of partial rounds.
pub const ROUNDS_P: usize = 56;

/// Parse a 64-character hex string into an `Fr` via big-endian mod-order
/// reduction (matches Noir's `field_from_hex` / `from_be_bytes_reduce`).
fn fr_from_hex(s: &str) -> Fr {
    let bytes = hex::decode(s).expect("Poseidon2 constants must be valid hex");
    Fr::from_be_bytes_mod_order(&bytes)
}

/// Internal-matrix diagonal entries (verbatim from
/// `bn254_blackbox_solver::poseidon2_constants::INTERNAL_MATRIX_DIAGONAL`).
const INTERNAL_DIAG_HEX: [&str; 4] = [
    "10dc6e9c006ea38b04b1e03b4bd9490c0d03f98929ca1d7fb56821fd19d3b6e7",
    "0c28145b6a44df3e0149b3d0a30b3bb599df9756d4dd9b84a86b38cfb45a740b",
    "00544b8338791518b2c7645a50392798b21f75bb60e3596170067d00141cac15",
    "222c01175718386f2e2e82eb122789e352e105a3b8fa852613bc534433ee428b",
];

/// Per-round constants (`ROUND_CONSTANT[r][i]`), verbatim from
/// `bn254_blackbox_solver::poseidon2_constants::ROUND_CONSTANT`.
const ROUND_CONSTANT_HEX: [[&str; 4]; 64] = [
    [
        "19b849f69450b06848da1d39bd5e4a4302bb86744edc26238b0878e269ed23e5",
        "265ddfe127dd51bd7239347b758f0a1320eb2cc7450acc1dad47f80c8dcf34d6",
        "199750ec472f1809e0f66a545e1e51624108ac845015c2aa3dfc36bab497d8aa",
        "157ff3fe65ac7208110f06a5f74302b14d743ea25067f0ffd032f787c7f1cdf8",
    ],
    [
        "2e49c43c4569dd9c5fd35ac45fca33f10b15c590692f8beefe18f4896ac94902",
        "0e35fb89981890520d4aef2b6d6506c3cb2f0b6973c24fa82731345ffa2d1f1e",
        "251ad47cb15c4f1105f109ae5e944f1ba9d9e7806d667ffec6fe723002e0b996",
        "13da07dc64d428369873e97160234641f8beb56fdd05e5f3563fa39d9c22df4e",
    ],
    [
        "0c009b84e650e6d23dc00c7dccef7483a553939689d350cd46e7b89055fd4738",
        "011f16b1c63a854f01992e3956f42d8b04eb650c6d535eb0203dec74befdca06",
        "0ed69e5e383a688f209d9a561daa79612f3f78d0467ad45485df07093f367549",
        "04dba94a7b0ce9e221acad41472b6bbe3aec507f5eb3d33f463672264c9f789b",
    ],
    [
        "0a3f2637d840f3a16eb094271c9d237b6036757d4bb50bf7ce732ff1d4fa28e8",
        "259a666f129eea198f8a1c502fdb38fa39b1f075569564b6e54a485d1182323f",
        "28bf7459c9b2f4c6d8e7d06a4ee3a47f7745d4271038e5157a32fdf7ede0d6a1",
        "0a1ca941f057037526ea200f489be8d4c37c85bbcce6a2aeec91bd6941432447",
    ],
    [
        "0c6f8f958be0e93053d7fd4fc54512855535ed1539f051dcb43a26fd926361cf",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "123106a93cd17578d426e8128ac9d90aa9e8a00708e296e084dd57e69caaf811",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "26e1ba52ad9285d97dd3ab52f8e840085e8fa83ff1e8f1877b074867cd2dee75",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "1cb55cad7bd133de18a64c5c47b9c97cbe4d8b7bf9e095864471537e6a4ae2c5",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "1dcd73e46acd8f8e0e2c7ce04bde7f6d2a53043d5060a41c7143f08e6e9055d0",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "011003e32f6d9c66f5852f05474a4def0cda294a0eb4e9b9b12b9bb4512e5574",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "2b1e809ac1d10ab29ad5f20d03a57dfebadfe5903f58bafed7c508dd2287ae8c",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "2539de1785b735999fb4dac35ee17ed0ef995d05ab2fc5faeaa69ae87bcec0a5",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "0c246c5a2ef8ee0126497f222b3e0a0ef4e1c3d41c86d46e43982cb11d77951d",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "192089c4974f68e95408148f7c0632edbb09e6a6ad1a1c2f3f0305f5d03b527b",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "1eae0ad8ab68b2f06a0ee36eeb0d0c058529097d91096b756d8fdc2fb5a60d85",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "179190e5d0e22179e46f8282872abc88db6e2fdc0dee99e69768bd98c5d06bfb",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "29bb9e2c9076732576e9a81c7ac4b83214528f7db00f31bf6cafe794a9b3cd1c",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "225d394e42207599403efd0c2464a90d52652645882aac35b10e590e6e691e08",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "064760623c25c8cf753d238055b444532be13557451c087de09efd454b23fd59",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "10ba3a0e01df92e87f301c4b716d8a394d67f4bf42a75c10922910a78f6b5b87",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "0e070bf53f8451b24f9c6e96b0c2a801cb511bc0c242eb9d361b77693f21471c",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "1b94cd61b051b04dd39755ff93821a73ccd6cb11d2491d8aa7f921014de252fb",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "1d7cb39bafb8c744e148787a2e70230f9d4e917d5713bb050487b5aa7d74070b",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "2ec93189bd1ab4f69117d0fe980c80ff8785c2961829f701bb74ac1f303b17db",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "2db366bfdd36d277a692bb825b86275beac404a19ae07a9082ea46bd83517926",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "062100eb485db06269655cf186a68532985275428450359adc99cec6960711b8",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "0761d33c66614aaa570e7f1e8244ca1120243f92fa59e4f900c567bf41f5a59b",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "20fc411a114d13992c2705aa034e3f315d78608a0f7de4ccf7a72e494855ad0d",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "25b5c004a4bdfcb5add9ec4e9ab219ba102c67e8b3effb5fc3a30f317250bc5a",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "23b1822d278ed632a494e58f6df6f5ed038b186d8474155ad87e7dff62b37f4b",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "22734b4c5c3f9493606c4ba9012499bf0f14d13bfcfcccaa16102a29cc2f69e0",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "26c0c8fe09eb30b7e27a74dc33492347e5bdff409aa3610254413d3fad795ce5",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "070dd0ccb6bd7bbae88eac03fa1fbb26196be3083a809829bbd626df348ccad9",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "12b6595bdb329b6fb043ba78bb28c3bec2c0a6de46d8c5ad6067c4ebfd4250da",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "248d97d7f76283d63bec30e7a5876c11c06fca9b275c671c5e33d95bb7e8d729",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "1a306d439d463b0816fc6fd64cc939318b45eb759ddde4aa106d15d9bd9baaaa",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "28a8f8372e3c38daced7c00421cb4621f4f1b54ddc27821b0d62d3d6ec7c56cf",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "0094975717f9a8a8bb35152f24d43294071ce320c829f388bc852183e1e2ce7e",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "04d5ee4c3aa78f7d80fde60d716480d3593f74d4f653ae83f4103246db2e8d65",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "2a6cf5e9aa03d4336349ad6fb8ed2269c7bef54b8822cc76d08495c12efde187",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "2304d31eaab960ba9274da43e19ddeb7f792180808fd6e43baae48d7efcba3f3",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "03fd9ac865a4b2a6d5e7009785817249bff08a7e0726fcb4e1c11d39d199f0b0",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "00b7258ded52bbda2248404d55ee5044798afc3a209193073f7954d4d63b0b64",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "159f81ada0771799ec38fca2d4bf65ebb13d3a74f3298db36272c5ca65e92d9a",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "1ef90e67437fbc8550237a75bc28e3bb9000130ea25f0c5471e144cf4264431f",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "1e65f838515e5ff0196b49aa41a2d2568df739bc176b08ec95a79ed82932e30d",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "2b1b045def3a166cec6ce768d079ba74b18c844e570e1f826575c1068c94c33f",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "0832e5753ceb0ff6402543b1109229c165dc2d73bef715e3f1c6e07c168bb173",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "02f614e9cedfb3dc6b762ae0a37d41bab1b841c2e8b6451bc5a8e3c390b6ad16",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "0e2427d38bd46a60dd640b8e362cad967370ebb777bedff40f6a0be27e7ed705",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "0493630b7c670b6deb7c84d414e7ce79049f0ec098c3c7c50768bbe29214a53a",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "22ead100e8e482674decdab17066c5a26bb1515355d5461a3dc06cc85327cea9",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "25b3e56e655b42cdaae2626ed2554d48583f1ae35626d04de5084e0b6d2a6f16",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "1e32752ada8836ef5837a6cde8ff13dbb599c336349e4c584b4fdc0a0cf6f9d0",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "2fa2a871c15a387cc50f68f6f3c3455b23c00995f05078f672a9864074d412e5",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "2f569b8a9a4424c9278e1db7311e889f54ccbf10661bab7fcd18e7c7a7d83505",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "044cb455110a8fdd531ade530234c518a7df93f7332ffd2144165374b246b43d",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "227808de93906d5d420246157f2e42b191fe8c90adfe118178ddc723a5319025",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "02fcca2934e046bc623adead873579865d03781ae090ad4a8579d2e7a6800355",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "0ef915f0ac120b876abccceb344a1d36bad3f3c5ab91a8ddcbec2e060d8befac",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
        "0000000000000000000000000000000000000000000000000000000000000000",
    ],
    [
        "1797130f4b7a3e1777eb757bc6f287f6ab0fb85f6be63b09f3b16ef2b1405d38",
        "0a76225dc04170ae3306c85abab59e608c7f497c20156d4d36c668555decc6e5",
        "1fffb9ec1992d66ba1e77a7b93209af6f8fa76d48acb664796174b5326a31a5c",
        "25721c4fc15a3f2853b57c338fa538d85f8fbba6c6b9c6090611889b797b9c5f",
    ],
    [
        "0c817fd42d5f7a41215e3d07ba197216adb4c3790705da95eb63b982bfcaf75a",
        "13abe3f5239915d39f7e13c2c24970b6df8cf86ce00a22002bc15866e52b5a96",
        "2106feea546224ea12ef7f39987a46c85c1bc3dc29bdbd7a92cd60acb4d391ce",
        "21ca859468a746b6aaa79474a37dab49f1ca5a28c748bc7157e1b3345bb0f959",
    ],
    [
        "05ccd6255c1e6f0c5cf1f0df934194c62911d14d0321662a8f1a48999e34185b",
        "0f0e34a64b70a626e464d846674c4c8816c4fb267fe44fe6ea28678cb09490a4",
        "0558531a4e25470c6157794ca36d0e9647dbfcfe350d64838f5b1a8a2de0d4bf",
        "09d3dca9173ed2faceea125157683d18924cadad3f655a60b72f5864961f1455",
    ],
    [
        "0328cbd54e8c0913493f866ed03d218bf23f92d68aaec48617d4c722e5bd4335",
        "2bf07216e2aff0a223a487b1a7094e07e79e7bcc9798c648ee3347dd5329d34b",
        "1daf345a58006b736499c583cb76c316d6f78ed6a6dffc82111e11a63fe412df",
        "176563472456aaa746b694c60e1823611ef39039b2edc7ff391e6f2293d2c404",
    ],
];

/// Parsed internal-matrix diagonal (`Fr` values).
fn internal_diag() -> &'static [Fr; T] {
    static CELL: OnceLock<[Fr; T]> = OnceLock::new();
    CELL.get_or_init(|| {
        [
            fr_from_hex(INTERNAL_DIAG_HEX[0]),
            fr_from_hex(INTERNAL_DIAG_HEX[1]),
            fr_from_hex(INTERNAL_DIAG_HEX[2]),
            fr_from_hex(INTERNAL_DIAG_HEX[3]),
        ]
    })
}

/// Parsed round constants (`Fr` values).
fn round_constants() -> &'static [[Fr; T]; ROUNDS_F + ROUNDS_P] {
    static CELL: OnceLock<[[Fr; T]; ROUNDS_F + ROUNDS_P]> = OnceLock::new();
    CELL.get_or_init(|| {
        let mut out = [[Fr::zero(); T]; ROUNDS_F + ROUNDS_P];
        for (r, row) in ROUND_CONSTANT_HEX.iter().enumerate() {
            for (i, hex) in row.iter().enumerate() {
                out[r][i] = fr_from_hex(hex);
            }
        }
        out
    })
}

// ---------------------------------------------------------------------------
// Native reference (used to populate witness values inside the gadget and as
// the in-test reference oracle).
// ---------------------------------------------------------------------------

#[inline]
fn single_box(x: Fr) -> Fr {
    let t = x * x;
    let u = t * t;
    u * x
}

/// External 4x4 linear layer. Matches Barretenberg's straight-line
/// implementation byte-for-byte (`Poseidon2::matrix_multiplication_4x4`).
fn matrix_multiplication_4x4(input: &mut [Fr; T]) {
    let t0 = input[0] + input[1];
    let t1 = input[2] + input[3];
    let mut t2 = input[1] + input[1];
    t2 += t1;
    let mut t3 = input[3] + input[3];
    t3 += t0;
    let mut t4 = t1 + t1;
    t4 += t4;
    t4 += t3;
    let mut t5 = t0 + t0;
    t5 += t5;
    t5 += t2;
    let t6 = t3 + t5;
    let t7 = t2 + t4;
    input[0] = t6;
    input[1] = t5;
    input[2] = t7;
    input[3] = t4;
}

fn internal_m_multiplication(input: &mut [Fr; T]) {
    let mut sum = Fr::zero();
    for i in input.iter() {
        sum += *i;
    }
    let diag = *internal_diag();
    for (index, i) in input.iter_mut().enumerate() {
        *i *= diag[index];
        *i += sum;
    }
}

fn add_round_constants(state: &mut [Fr; T], round: usize) {
    let rc = round_constants()[round];
    for i in 0..T {
        state[i] += rc[i];
    }
}

/// Native Poseidon2 permutation. Mirrors Noir's reference implementation in
/// `bn254_blackbox_solver::poseidon2::Poseidon2::permutation`.
pub fn poseidon2_permutation_native(state: &mut [Fr; T]) {
    matrix_multiplication_4x4(state);

    let rf_half = ROUNDS_F / 2;
    for r in 0..rf_half {
        add_round_constants(state, r);
        for cell in state.iter_mut() {
            *cell = single_box(*cell);
        }
        matrix_multiplication_4x4(state);
    }

    let p_end = rf_half + ROUNDS_P;
    let rc_table = round_constants();
    for r in rf_half..p_end {
        state[0] += rc_table[r][0];
        state[0] = single_box(state[0]);
        internal_m_multiplication(state);
    }

    let num_rounds = ROUNDS_F + ROUNDS_P;
    for r in p_end..num_rounds {
        add_round_constants(state, r);
        for cell in state.iter_mut() {
            *cell = single_box(*cell);
        }
        matrix_multiplication_4x4(state);
    }
}

// ---------------------------------------------------------------------------
// In-circuit gadget.
// ---------------------------------------------------------------------------

/// State cell as it flows through the gadget. `var` is the freshly-allocated
/// witness pinned to the current value; `lc` is the same value in LC form so
/// callers can fold downstream linear combinations without re-pinning.
#[derive(Clone)]
struct Cell {
    var: Variable,
    value: Option<Fr>,
}

impl Cell {
    fn lc(&self) -> LinearCombination<Fr> {
        LinearCombination::from((Fr::one(), self.var))
    }
}

/// Materialize a `LinearCombination` whose proving-time value is `value` into
/// a freshly-allocated witness, pinning it via `0 * 0 = lc - var`.
fn pin_lc(
    builder: &mut R1csBuilder<'_>,
    lc: LinearCombination<Fr>,
    value: Option<Fr>,
) -> Result<Cell, SynthesisError> {
    let var = builder.alloc_with_value(value)?;
    let mut diff = lc;
    diff.0.push((-Fr::one(), var));
    builder.enforce(builder.zero_lc(), builder.zero_lc(), diff)?;
    Ok(Cell { var, value })
}

/// In-circuit `x^5` S-box. Allocates `t = x*x`, `u = t*t`, `out = u*x` and
/// enforces all three. Returns the `Cell` for `out`.
fn sbox(builder: &mut R1csBuilder<'_>, x: &Cell) -> Result<Cell, SynthesisError> {
    let x_val = x.value;
    let t_val = x_val.map(|v| v * v);
    let u_val = t_val.map(|v| v * v);
    let out_val = u_val.zip(x_val).map(|(a, b)| a * b);

    let t = builder.alloc_with_value(t_val)?;
    builder.enforce(x.lc(), x.lc(), LinearCombination::from((Fr::one(), t)))?;
    let u = builder.alloc_with_value(u_val)?;
    let t_lc = LinearCombination::from((Fr::one(), t));
    builder.enforce(t_lc.clone(), t_lc, LinearCombination::from((Fr::one(), u)))?;
    let out = builder.alloc_with_value(out_val)?;
    builder.enforce(
        LinearCombination::from((Fr::one(), u)),
        x.lc(),
        LinearCombination::from((Fr::one(), out)),
    )?;
    Ok(Cell {
        var: out,
        value: out_val,
    })
}

/// External 4x4 linear layer, in-circuit. Produces freshly-pinned cells so
/// LC widths stay bounded across rounds.
fn matrix_4x4_in_circuit(
    builder: &mut R1csBuilder<'_>,
    state: &[Cell; T],
) -> Result<[Cell; T], SynthesisError> {
    // We mirror the native straight-line code, but built as LCs over the input
    // cells. Each output is at most O(t) terms — well within Arkworks LC sizes
    // — and we pin each output to a fresh witness so the *next* round starts
    // from cell variables.
    let in_vals: [Option<Fr>; T] = std::array::from_fn(|i| state[i].value);
    let mut native = [Fr::zero(); T];
    let have_values = in_vals.iter().all(|v| v.is_some());
    if have_values {
        for i in 0..T {
            native[i] = in_vals[i].unwrap();
        }
        matrix_multiplication_4x4(&mut native);
    }

    let l = |i: usize| state[i].lc();
    let add = |a: LinearCombination<Fr>, b: LinearCombination<Fr>| -> LinearCombination<Fr> {
        let mut out = a;
        for (c, v) in b.0 {
            out.0.push((c, v));
        }
        out
    };
    let scale = |a: &LinearCombination<Fr>, k: Fr| -> LinearCombination<Fr> {
        LinearCombination(a.0.iter().map(|(c, v)| (*c * k, *v)).collect())
    };
    let two = Fr::from(2u64);

    // Replay the native straight-line, but as LCs.
    let t0 = add(l(0), l(1));
    let t1 = add(l(2), l(3));
    let mut t2 = scale(&l(1), two);
    t2 = add(t2, t1.clone());
    let mut t3 = scale(&l(3), two);
    t3 = add(t3, t0.clone());
    let mut t4 = scale(&t1, two);
    t4 = scale(&t4, two);
    t4 = add(t4, t3.clone());
    let mut t5 = scale(&t0, two);
    t5 = scale(&t5, two);
    t5 = add(t5, t2.clone());
    let t6 = add(t3, t5.clone());
    let t7 = add(t2, t4.clone());

    let out_vals: [Option<Fr>; T] = if have_values {
        [
            Some(native[0]),
            Some(native[1]),
            Some(native[2]),
            Some(native[3]),
        ]
    } else {
        [None, None, None, None]
    };

    let c0 = pin_lc(builder, t6, out_vals[0])?;
    let c1 = pin_lc(builder, t5, out_vals[1])?;
    let c2 = pin_lc(builder, t7, out_vals[2])?;
    let c3 = pin_lc(builder, t4, out_vals[3])?;
    Ok([c0, c1, c2, c3])
}

/// Internal matrix multiply, in-circuit. `state[i] -> state[i]*diag[i] + sum`.
/// One mul constraint per cell (4 total).
fn internal_m_in_circuit(
    builder: &mut R1csBuilder<'_>,
    state: &[Cell; T],
) -> Result<[Cell; T], SynthesisError> {
    let diag = *internal_diag();

    // sum_lc = state[0] + state[1] + state[2] + state[3]
    let mut sum_lc = LinearCombination(Vec::new());
    for c in state.iter() {
        for (k, v) in c.lc().0 {
            sum_lc.0.push((k, v));
        }
    }

    let in_vals: [Option<Fr>; T] = std::array::from_fn(|i| state[i].value);
    let sum_val: Option<Fr> = if in_vals.iter().all(|v| v.is_some()) {
        let mut s = Fr::zero();
        for v in in_vals.iter() {
            s += v.unwrap();
        }
        Some(s)
    } else {
        None
    };

    let mut out = Vec::with_capacity(T);
    for i in 0..T {
        // out_i = diag[i] * state[i] + sum
        let mut lc = state[i].lc();
        // multiply by diag[i] in-place
        lc = LinearCombination(lc.0.into_iter().map(|(c, v)| (c * diag[i], v)).collect());
        for (k, v) in sum_lc.0.iter() {
            lc.0.push((*k, *v));
        }
        let out_val = match (state[i].value, sum_val) {
            (Some(x), Some(s)) => Some(x * diag[i] + s),
            _ => None,
        };
        out.push(pin_lc(builder, lc, out_val)?);
    }
    Ok([
        out[0].clone(),
        out[1].clone(),
        out[2].clone(),
        out[3].clone(),
    ])
}

/// Add round constants as a pure LC operation. We do *not* pin: the matrix or
/// S-box step that consumes the result will absorb the constant into its LC.
fn add_rc(cell: &Cell, rc: Fr) -> Cell {
    let mut lc = cell.lc();
    if !rc.is_zero() {
        lc.0.push((rc, Variable::One));
    }
    let _ = lc;
    Cell {
        var: cell.var,
        value: cell.value.map(|v| v + rc),
    }
}

/// In-circuit Poseidon2 permutation. Input `state_values` should be `Some(_)`
/// in proving mode and `None` (uniformly) in setup mode.
///
/// Returns the output state as `Variable`s. Each output Variable is pinned to
/// the post-permutation value via the gadget's constraints.
pub fn poseidon2_permutation(
    builder: &mut R1csBuilder<'_>,
    state: &[Variable; T],
    state_values: &[Option<Fr>; T],
) -> Result<[Variable; T], SynthesisError> {
    // Wrap inputs in Cell.
    let mut cells: [Cell; T] = std::array::from_fn(|i| Cell {
        var: state[i],
        value: state_values[i],
    });

    // Initial external layer.
    cells = matrix_4x4_in_circuit(builder, &cells)?;

    let rc_table = round_constants();
    // First half of full rounds.
    let rf_half = ROUNDS_F / 2;
    for r in 0..rf_half {
        // Add round constants (folded into S-box LCs).
        let after_rc: [Cell; T] = std::array::from_fn(|i| add_rc(&cells[i], rc_table[r][i]));
        // The S-box wants a `Cell` whose `var` represents the value being
        // squared. add_rc left the LC value updated but the `var` is still the
        // pre-rc witness; to keep the S-box constraint `var * var = t` clean,
        // we pin the post-rc value to a fresh witness first when the RC is
        // non-zero.
        let mut sb_in: [Cell; T] = std::array::from_fn(|_| Cell {
            var: Variable::One,
            value: None,
        });
        for i in 0..T {
            let rc = rc_table[r][i];
            if rc.is_zero() {
                sb_in[i] = cells[i].clone();
            } else {
                let mut lc = cells[i].lc();
                lc.0.push((rc, Variable::One));
                sb_in[i] = pin_lc(builder, lc, after_rc[i].value)?;
            }
        }
        // S-box each cell.
        let mut after_sbox: [Cell; T] = std::array::from_fn(|_| Cell {
            var: Variable::One,
            value: None,
        });
        for i in 0..T {
            after_sbox[i] = sbox(builder, &sb_in[i])?;
        }
        cells = matrix_4x4_in_circuit(builder, &after_sbox)?;
    }

    // Internal rounds.
    let p_end = rf_half + ROUNDS_P;
    for r in rf_half..p_end {
        let rc0 = rc_table[r][0];
        // Pin `state[0] + rc0` to a fresh witness so S-box's `var * var = t`
        // constraint is well-formed.
        let after_rc_val = cells[0].value.map(|v| v + rc0);
        let sb_in = if rc0.is_zero() {
            cells[0].clone()
        } else {
            let mut lc = cells[0].lc();
            lc.0.push((rc0, Variable::One));
            pin_lc(builder, lc, after_rc_val)?
        };
        let sb_out = sbox(builder, &sb_in)?;
        cells[0] = sb_out;
        cells = internal_m_in_circuit(builder, &cells)?;
    }

    // Second half of full rounds.
    let num_rounds = ROUNDS_F + ROUNDS_P;
    for r in p_end..num_rounds {
        let mut sb_in: [Cell; T] = std::array::from_fn(|_| Cell {
            var: Variable::One,
            value: None,
        });
        for i in 0..T {
            let rc = rc_table[r][i];
            if rc.is_zero() {
                sb_in[i] = cells[i].clone();
            } else {
                let mut lc = cells[i].lc();
                lc.0.push((rc, Variable::One));
                let v = cells[i].value.map(|x| x + rc);
                sb_in[i] = pin_lc(builder, lc, v)?;
            }
        }
        let mut after_sbox: [Cell; T] = std::array::from_fn(|_| Cell {
            var: Variable::One,
            value: None,
        });
        for i in 0..T {
            after_sbox[i] = sbox(builder, &sb_in[i])?;
        }
        cells = matrix_4x4_in_circuit(builder, &after_sbox)?;
    }

    Ok([cells[0].var, cells[1].var, cells[2].var, cells[3].var])
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::gr1cs::ConstraintSystem;

    use crate::field::fr_from_decimal_str;
    use crate::witness::WitnessMap;

    /// Pinned KAT vector from Noir's own
    /// `bn254_blackbox_solver::poseidon2::tests::smoke_test`:
    /// `permutation([0, 0, 0, 0])` over BN254 Fr.
    const KAT_ALL_ZEROS_OUTPUT_HEX: [&str; T] = [
        "18DFB8DC9B82229CFF974EFEFC8DF78B1CE96D9D844236B496785C698BC6732E",
        "095C230D1D37A246E8D2D5A63B165FE0FADE040D442F61E25F0590E5FB76F839",
        "0BB9545846E1AFA4FA3C97414A60A20FC4949F537A68CCECA34C5CE71E28AA59",
        "18A4F34C9C6F99335FF7638B82AEED9018026618358873C982BBDDE265B2ED6D",
    ];

    fn fr_hex(s: &str) -> Fr {
        let lower = s.to_lowercase();
        let bytes = hex::decode(lower).expect("hex");
        Fr::from_be_bytes_mod_order(&bytes)
    }

    #[test]
    fn native_matches_external_kat_all_zeros() {
        // The Noir test suite hard-codes the expected permutation of
        // [0, 0, 0, 0] — see `acvm-repo/bn254_blackbox_solver/src/poseidon2.rs`,
        // function `smoke_test`. This pins our native implementation to that
        // same vector.
        let mut state = [Fr::zero(); T];
        poseidon2_permutation_native(&mut state);
        for i in 0..T {
            assert_eq!(state[i], fr_hex(KAT_ALL_ZEROS_OUTPUT_HEX[i]));
        }
    }

    #[test]
    fn in_circuit_matches_native_on_1_2_3_4() {
        // Build a tiny CS with 4 input witnesses pinned to [1,2,3,4], run the
        // gadget, and assert it agrees with the native impl. Also asserts CS
        // is satisfied.
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::new();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&map));
        builder.finish_public_pass();

        let inputs = [
            Fr::from(1u64),
            Fr::from(2u64),
            Fr::from(3u64),
            Fr::from(4u64),
        ];
        let in_vars: [Variable; T] = {
            let v0 = builder.alloc_with_value(Some(inputs[0])).unwrap();
            let v1 = builder.alloc_with_value(Some(inputs[1])).unwrap();
            let v2 = builder.alloc_with_value(Some(inputs[2])).unwrap();
            let v3 = builder.alloc_with_value(Some(inputs[3])).unwrap();
            [v0, v1, v2, v3]
        };
        let in_vals: [Option<Fr>; T] = [
            Some(inputs[0]),
            Some(inputs[1]),
            Some(inputs[2]),
            Some(inputs[3]),
        ];

        let out_vars = poseidon2_permutation(&mut builder, &in_vars, &in_vals).unwrap();

        let mut native = inputs;
        poseidon2_permutation_native(&mut native);

        // Pull the assigned values out of the CS.
        cs.finalize();
        let assigned = cs.borrow().unwrap().assigned_value(out_vars[0]).unwrap();
        let _ = assigned; // sanity-check assignment exists
        // Use a fresh borrow to fetch each Variable's value.
        let cs_ref = cs.borrow().unwrap();
        for i in 0..T {
            let v = cs_ref.assigned_value(out_vars[i]).expect("assigned");
            assert_eq!(v, native[i], "gadget vs native mismatch at index {i}");
        }
        drop(cs_ref);

        assert!(cs.is_satisfied().unwrap(), "constraint system unsatisfied");
    }

    #[test]
    fn in_circuit_matches_external_kat_all_zeros() {
        // Independent end-to-end check: run the gadget on the same input
        // Noir's smoke test uses ([0,0,0,0]) and compare against the
        // hard-coded external reference vector. This catches the case where
        // *both* our native impl and gadget have the same bug.
        let cs = ConstraintSystem::<Fr>::new_ref();
        let map = WitnessMap::new();
        let mut builder = R1csBuilder::new(cs.clone(), Some(&map));
        builder.finish_public_pass();

        let in_vars: [Variable; T] = [
            builder.alloc_with_value(Some(Fr::zero())).unwrap(),
            builder.alloc_with_value(Some(Fr::zero())).unwrap(),
            builder.alloc_with_value(Some(Fr::zero())).unwrap(),
            builder.alloc_with_value(Some(Fr::zero())).unwrap(),
        ];
        let in_vals = [Some(Fr::zero()); T];
        let out_vars = poseidon2_permutation(&mut builder, &in_vars, &in_vals).unwrap();

        cs.finalize();
        let cs_ref = cs.borrow().unwrap();
        for i in 0..T {
            let v = cs_ref.assigned_value(out_vars[i]).expect("assigned");
            assert_eq!(
                v,
                fr_hex(KAT_ALL_ZEROS_OUTPUT_HEX[i]),
                "external KAT mismatch at {i}"
            );
        }
        drop(cs_ref);
        assert!(cs.is_satisfied().unwrap());
    }

    /// Sanity: `fr_from_decimal_str` is the same parser the rest of the crate
    /// uses; this test guards against drift in how Noir/xark interpret
    /// decimal `Field` values (which is what `Prover.toml` carries).
    #[test]
    fn fr_decimal_parse_roundtrip() {
        let one = fr_from_decimal_str("1").unwrap();
        assert_eq!(one, Fr::from(1u64));
    }

    /// Helper: emit `poseidon2_permutation([1,2,3,4])` in decimal. Used to
    /// populate the Noir `Prover.toml` for `crates/tests/circuits/poseidon_basic/`. Gated
    /// behind `--ignored` so it doesn't pollute normal CI output.
    #[test]
    #[ignore]
    fn print_poseidon2_of_1_2_3_4_decimal() {
        let mut state = [
            Fr::from(1u64),
            Fr::from(2u64),
            Fr::from(3u64),
            Fr::from(4u64),
        ];
        poseidon2_permutation_native(&mut state);
        for v in state.iter() {
            println!("{}", crate::field::fr_to_decimal_string(v));
        }
    }
}
