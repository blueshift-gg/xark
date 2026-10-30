#!/usr/bin/env python3
import random
import subprocess
import sys


Q = 21888242871839275222246405745257275088696311157297823662689037894645226208583
GENERATOR = (1, 2)


def add(left, right):
    if left is None:
        return right
    if right is None:
        return left
    x1, y1 = left
    x2, y2 = right
    if x1 == x2 and (y1 + y2) % Q == 0:
        return None
    if left == right:
        slope = 3 * x1 * x1 * pow(2 * y1, -1, Q) % Q
    else:
        slope = (y2 - y1) * pow((x2 - x1) % Q, -1, Q) % Q
    x3 = (slope * slope - x1 - x2) % Q
    y3 = (slope * (x1 - x3) - y1) % Q
    return x3, y3


def multiply(point, scalar):
    result = None
    while scalar:
        if scalar & 1:
            result = add(result, point)
        point = add(point, point)
        scalar >>= 1
    return result


def encode_row(point, infinity_payload=(0, 0)):
    if point is None:
        x, y = infinity_payload
        infinity = 1
    else:
        x, y = point
        infinity = 0
    return f"{infinity} {x:064x} {y:064x}\n"


def main():
    executable = sys.argv[1]
    rng = random.Random(0x5841524B)
    valid = [None, GENERATOR, add(GENERATOR, GENERATOR)]
    valid.extend(multiply(GENERATOR, rng.randrange(1, Q)) for _ in range(32))
    cases = [(encode_row(point), point) for point in valid]
    invalid = [
        encode_row((0, 0)),
        encode_row((1, 1)),
        encode_row((Q, 2)),
        encode_row((1, Q)),
        encode_row(None, (1, 0)),
    ]

    output = subprocess.run(
        [executable],
        input="".join(row for row, _ in cases) + "".join(invalid),
        text=True,
        capture_output=True,
        check=True,
    ).stdout.splitlines()
    expected_count = len(cases) + len(invalid)
    if len(output) != expected_count:
        raise SystemExit(f"probe returned {len(output)} rows, expected {expected_count}")

    for index, ((_, point), row) in enumerate(zip(cases, output)):
        fields = row.split()
        expected = (0, 0) if point is None else point
        if fields != ["1", f"{expected[0]:064x}", f"{expected[1]:064x}"]:
            raise SystemExit(f"valid point conversion mismatch at case {index}: {row}")
    for index, row in enumerate(output[len(cases) :]):
        if row != "0":
            raise SystemExit(f"invalid point was accepted at case {index}: {row}")
    print(f"passed checked G1 input conversion: {len(cases)} valid, {len(invalid)} rejected")


if __name__ == "__main__":
    main()
