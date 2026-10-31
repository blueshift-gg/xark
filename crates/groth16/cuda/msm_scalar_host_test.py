#!/usr/bin/env python3
import random
import subprocess
import sys


FR = 21888242871839275222246405745257275088548364400416034343698204186575808495617


def main():
    executable = sys.argv[1]
    rng = random.Random(0x5343414C)
    valid = [0, 1, FR - 1]
    valid.extend(rng.randrange(FR) for _ in range(256))
    invalid = [FR, FR + 1, (1 << 256) - 1]
    invalid.extend(FR + rng.randrange(1, 1 << 32) for _ in range(32))
    cases = [(value, 1) for value in valid] + [(value, 0) for value in invalid]

    output = subprocess.run(
        [executable],
        input="".join(f"{value:064x}\n" for value, _ in cases),
        text=True,
        capture_output=True,
        check=True,
    ).stdout.splitlines()
    if len(output) != len(cases):
        raise SystemExit(f"probe returned {len(output)} rows, expected {len(cases)}")
    for index, ((_, expected), actual) in enumerate(zip(cases, output)):
        if actual != str(expected):
            raise SystemExit(f"scalar canonicality mismatch at case {index}")
    print(f"passed BN254 Fr canonicality: {len(valid)} valid, {len(invalid)} rejected")


if __name__ == "__main__":
    main()
