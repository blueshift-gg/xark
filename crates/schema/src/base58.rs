//! Base58 as Bitcoin and Solana write it: the alphabet without `0`, `O`, `I` and `l`,
//! most significant digit first, and each leading zero byte a leading `1`. A Solana
//! address (`Pubkey`, @solana/kit's `Address`) is its 32 bytes in this form, so an
//! `xark::Address` input is given and decoded as one.

use num_bigint::BigUint;

const ALPHABET: &[u8; 58] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

/// `bytes` in base58.
pub fn encode(bytes: &[u8]) -> String {
    let zeros = bytes.iter().take_while(|&&b| b == 0).count();
    let mut out = "1".repeat(zeros);
    let n = BigUint::from_bytes_be(&bytes[zeros..]);
    if n.bits() > 0 {
        out.extend(
            n.to_radix_be(58)
                .iter()
                .map(|&d| ALPHABET[d as usize] as char),
        );
    }
    out
}

/// The bytes `s` encodes, or why it isn't base58.
pub fn decode(s: &str) -> Result<Vec<u8>, String> {
    let digits: Vec<u8> = s
        .bytes()
        .map(|c| ALPHABET.iter().position(|&a| a == c).map(|d| d as u8))
        .collect::<Option<_>>()
        .ok_or_else(|| format!("{s:?} is not base58"))?;
    let zeros = digits.iter().take_while(|&&d| d == 0).count();
    let mut out = vec![0u8; zeros];
    if zeros < digits.len() {
        let n = BigUint::from_radix_be(&digits[zeros..], 58)
            .ok_or_else(|| format!("{s:?} is not base58"))?;
        out.extend(n.to_bytes_be());
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Known values: the system program (32 zero bytes), and the SPL Token program's
    /// address with its bytes as `solana-program` lists them.
    #[test]
    fn known_addresses() {
        assert_eq!(encode(&[0; 32]), "11111111111111111111111111111111");
        assert_eq!(decode("11111111111111111111111111111111").unwrap(), [0; 32]);
        let token = [
            6, 221, 246, 225, 215, 101, 161, 147, 217, 203, 225, 70, 206, 235, 121, 172, 28, 180,
            133, 237, 95, 91, 55, 145, 58, 140, 245, 133, 126, 255, 0, 169,
        ];
        assert_eq!(
            encode(&token),
            "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"
        );
        assert_eq!(
            decode("TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA").unwrap(),
            token
        );
        // Bitcoin's examples: "Hello World!" and a leading zero byte.
        assert_eq!(encode(b"Hello World!"), "2NEpo7TZRRrLZSi2U");
        assert_eq!(decode("1112").unwrap(), [0, 0, 0, 1]);
        assert!(decode("0OIl").is_err() && decode("abc!").is_err());
        assert_eq!(decode("").unwrap(), [0u8; 0]);
    }
}
