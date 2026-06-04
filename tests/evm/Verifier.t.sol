// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Foundry smoke test for the auto-generated `Verifier.sol`. See README.md
// in this directory for setup notes. This test is NOT run by `cargo test`;
// the CI gate for the EVM exporter is the Rust-side test at
// `crates/groth16-backend/tests/evm_export.rs`.

import "forge-std/Test.sol";
import "./Verifier.sol";

// Proof + public-input values for `tests/fixtures/groth16/arithmetic_square/`.
// Regenerate with:
//   cargo test -p groth16-backend --test evm_export dump_fixture_for_foundry
// then copy `target/tmp/proof_fixture.txt` here.
contract VerifierTest is Test {
    Verifier internal verifier;

    function setUp() public {
        verifier = new Verifier();
    }

    function _validProof()
        internal
        pure
        returns (
            uint256[2] memory a,
            uint256[2][2] memory b,
            uint256[2] memory c,
            uint256[1] memory inputs
        )
    {
        a = [
            uint256(19164197528943953322504850811541297352270083108476882422942915363860162294090),
            uint256(6689624463854028579325533889670052688001874803651055568466406172922737207021)
        ];
        b = [
            [
                uint256(21093062122322876306757861633438014454747587735593054023684037895207553977825),
                uint256(12492152249113702634430116015629772335515776618206748769156767100777365201915)
            ],
            [
                uint256(6316505154125912469814036596491299989759158053567756092601711458329561012730),
                uint256(627445387527941461674699045913405224089243854832546168122810638013528709970)
            ]
        ];
        c = [
            uint256(5053477051538174321141241716218848152530001574699364435711551058981036292504),
            uint256(14066473929177984386727399927202330151962366715305750291790324723715933738685)
        ];
        // Public input for `arithmetic_square`: the witness publishes
        // x^2 for the private input `x = 9`, so the single public input is 81.
        inputs = [uint256(81)];
    }

    function testVerifyProof_accepts_valid() public view {
        (
            uint256[2] memory a,
            uint256[2][2] memory b,
            uint256[2] memory c,
            uint256[1] memory inputs
        ) = _validProof();
        bool ok = verifier.verifyProof(a, b, c, inputs);
        assertTrue(ok, "valid proof must verify");
    }

    function testVerifyProof_rejects_tampered_input() public view {
        (
            uint256[2] memory a,
            uint256[2][2] memory b,
            uint256[2] memory c,
            uint256[1] memory inputs
        ) = _validProof();
        // Flip the public input: claim x^2 == 82 instead of 81.
        inputs[0] = 82;
        bool ok = verifier.verifyProof(a, b, c, inputs);
        assertFalse(ok, "tampered public input must not verify");
    }
}
