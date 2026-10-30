#!/usr/bin/env python3
import random
import subprocess
import sys


Q = 21888242871839275222246405745257275088696311157297823662689037894645226208583


def main() -> None:
    executable = sys.argv[1]
    edge = [0, 1, 2, Q - 2, Q - 1]
    cases = [(a, b) for a in edge for b in edge]
    cases.extend(((1 << bit) % Q, (1 << (253 - bit)) % Q) for bit in range(254))
    rng = random.Random(0x5841524B)
    cases.extend((rng.randrange(Q), rng.randrange(Q)) for _ in range(512))

    input_text = "".join(f"{a:064x} {b:064x}\n" for a, b in cases)
    output = subprocess.run(
        [executable], input=input_text, text=True, capture_output=True, check=True
    ).stdout.splitlines()
    if len(output) != len(cases):
        raise SystemExit(f"probe returned {len(output)} rows for {len(cases)} cases")

    for index, ((a, b), row) in enumerate(zip(cases, output)):
        got = tuple(int(value, 16) for value in row.split())
        expected = ((a + b) % Q, (a - b) % Q, (a * b) % Q)
        if got != expected:
            raise SystemExit(
                f"Fq mismatch at case {index}: a={a:x}, b={b:x}, "
                f"got={got}, expected={expected}"
            )
    for invalid in (Q, Q + 1, (1 << 256) - 1):
        rejected = subprocess.run(
            [executable],
            input=f"{invalid:064x} {0:064x}\n",
            text=True,
            capture_output=True,
            check=False,
        )
        if rejected.returncode == 0:
            raise SystemExit(f"noncanonical input was accepted: {invalid:x}")
    print(f"passed BN254 Fq oracle: {len(cases)} add/sub/mul pairs")


if __name__ == "__main__":
    main()
