//! `<Fn>Inputs::to_json()`: a circuit's inputs, built in Rust, as the JSON
//! `xark prove --inputs` takes, keyed as declared (as in `inputs.example.json`).

use xark::prelude::*;
use xark::prover::ProveInputs;
use xark::{Choice, Country, Days};

#[input]
pub struct Holder {
    net_worth: u64,
    born: Days<1900, 2100>,
    nationality: Choice<Country>,
}

#[circuit]
pub fn wealthy(holder: Private<Holder>, min_worth: Public<u64>, salt: Private<[u8; 4]>) {
    require(holder.net_worth >= min_worth);
    let _ = (holder.born, holder.nationality, salt);
}

fn inputs() -> WealthyInputs {
    WealthyInputs {
        holder: Holder {
            net_worth: 1_000_000,
            born: "1990-01-01".parse().unwrap(),
            nationality: Country::US.into(),
        },
        min_worth: 500,
        salt: [1, 2, 3, 4],
    }
}

#[test]
fn inputs_are_the_json_prove_takes() {
    let json = inputs().to_json().unwrap();
    let value: serde_json::Value = serde_json::from_str(&json).unwrap();
    // Integers as strings, so a `u64` past 2^53 stays exact in any JSON reader.
    assert_eq!(
        value,
        serde_json::json!({
            "holder": { "net_worth": "1000000", "born": "1990-01-01", "nationality": "US" },
            "min_worth": "500",
            "salt": "0x01020304",
        }),
        "{json}"
    );
    // `--inputs` reads it back as the very leaves the Rust inputs prove with.
    let schema = xark_schema::Schema::parse(&WealthyInputs::schema()).unwrap();
    let read = schema.leaves(&value).unwrap();
    let want = inputs().into_inputs();
    assert_eq!(read.len(), want.len(), "{read:?}");
    for (name, fr) in want {
        assert_eq!(read.get(&name), Some(&fr), "{name}");
    }
}
