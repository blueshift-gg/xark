use std::ecdsa_secp256r1;

fn main(
    pub_key_x: [u8; 32],
    pub_key_y: [u8; 32],
    signature: [u8; 64],
    message_hash: [u8; 32],
) {
    let valid = ecdsa_secp256r1::verify_signature(
        pub_key_x, pub_key_y, signature, message_hash,
    );
    assert(valid);
}
