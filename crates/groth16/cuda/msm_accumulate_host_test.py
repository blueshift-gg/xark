#!/usr/bin/env python3
import random
import subprocess
import sys

from msm_g1_host_test import GENERATOR, INFINITY, Q, add, encode, multiply


def make_case(multiples, window_digits, bucket_count):
    points = []
    for multiple in multiples:
        point = multiply(GENERATOR, abs(multiple))
        if multiple < 0 and point is not None:
            point = (point[0], (-point[1]) % Q)
        points.append(point)
    csr_windows = []
    for digits in window_digits:
        members = [[] for _ in range(bucket_count)]
        for point_index, digit in enumerate(digits):
            if digit:
                members[digit].append(point_index)
        offsets = [0]
        indices = []
        for bucket_members in members:
            indices.extend(bucket_members)
            offsets.append(len(indices))
        csr_windows.append((offsets, indices))
    expected = INFINITY
    for window, digits in enumerate(window_digits):
        for point, digit in zip(points, digits):
            expected = add(expected, multiply(point, digit << (11 * window)))
    return points, csr_windows, expected


def encode_case(case):
    points, csr_windows, _ = case
    bucket_count = len(csr_windows[0][0]) - 1
    rows = [f"{len(points)} {len(csr_windows)} {bucket_count}"]
    rows.extend(
        f"{int(point is None)} "
        f"{(point[0] if point else 0):064x} "
        f"{(point[1] if point else 0):064x}"
        for point in points
    )
    for offsets, indices in csr_windows:
        rows.append(" ".join(map(str, offsets)))
        rows.append(" ".join(map(str, indices)))
    return " ".join(rows)


def main():
    executable = sys.argv[1]
    cases = [
        make_case([1, 2, 3], [[1, 2, 3]], 4),
        make_case([1, -1, 5, 2], [[2, 2, 0, 4]], 5),
        make_case([1], [[0]], 8),
        make_case([2, 3, 4, 5], [[7, 7, 7, 1]], 8),
        make_case([1], [[1], [1]], 2),
    ]
    rng = random.Random(0x5841524B)
    for _ in range(32):
        point_count = rng.randrange(0, 25)
        multiples = [rng.randrange(-100, 101) for _ in range(point_count)]
        window_digits = [
            [rng.randrange(16) for _ in range(point_count)]
            for _ in range(rng.randrange(1, 4))
        ]
        cases.append(make_case(multiples, window_digits, 16))
    payload = "\n".join(encode_case(case) for case in cases) + "\n"
    output = subprocess.run(
        [executable], input=payload, text=True, capture_output=True, check=True
    ).stdout.splitlines()
    if len(output) != len(cases):
        raise SystemExit(f"probe returned {len(output)} rows for {len(cases)} cases")
    for index, (line, case) in enumerate(zip(output, cases)):
        expected = encode(case[2]).split()
        if line.split() != expected:
            raise SystemExit(
                f"MSM bucket reduction mismatch at case {index}: "
                f"got={line.split()}, expected={expected}"
            )
    print(f"passed BN254 bucket accumulation/reduction oracle: {len(cases)} MSM cases")


if __name__ == "__main__":
    main()
