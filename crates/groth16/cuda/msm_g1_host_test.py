#!/usr/bin/env python3
import random
import subprocess
import sys
import tempfile


Q = 21888242871839275222246405745257275088696311157297823662689037894645226208583
GENERATOR = (1, 2)
INFINITY = None


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
        slope = (3 * x1 * x1) * pow(2 * y1, -1, Q) % Q
    else:
        slope = (y2 - y1) * pow((x2 - x1) % Q, -1, Q) % Q
    x3 = (slope * slope - x1 - x2) % Q
    y3 = (slope * (x1 - x3) - y1) % Q
    return x3, y3


def multiply(point, scalar):
    result = None
    addend = point
    while scalar:
        if scalar & 1:
            result = add(result, addend)
        addend = add(addend, addend)
        scalar >>= 1
    return result


def encode(point):
    if point is None:
        return "1 " + "0" * 64 + " " + "0" * 64
    x, y = point
    return f"0 {x:064x} {y:064x}"


def input_row(operation, left, right):
    left_inf = int(left is None)
    right_inf = int(right is None)
    lx, ly = left if left is not None else (0, 0)
    rx, ry = right if right is not None else (0, 0)
    return (
        f"{operation} {left_inf} {lx:064x} {ly:064x} "
        f"{right_inf} {rx:064x} {ry:064x}\n"
    )


def main() -> None:
    executable = sys.argv[1]
    rng = random.Random(0x5841524B)
    points = [multiply(GENERATOR, scalar) for scalar in (0, 1, 2, 3, 7, 19, 255)]
    points.extend(multiply(GENERATOR, rng.randrange(1, 1 << 180)) for _ in range(8))
    cases = []
    for point in points:
        cases.append((1, point, None, add(point, point)))
        cases.append((0, point, None, point))
        cases.append((0, None, point, point))
        cases.append((0, point, (point[0], (-point[1]) % Q) if point else None, None))
    for i in range(len(points) - 1):
        cases.append((0, points[i], points[i + 1], add(points[i], points[i + 1])))
    scalars = [0, 1, 2, Q // 2, Q - 1]
    scalars.extend(rng.randrange(Q) for _ in range(8))
    for point, scalar in zip(points, scalars):
        cases.append((2, point, (scalar, 0), multiply(point, scalar)))

    input_text = "".join(input_row(op, left, right) for op, left, right, _ in cases)
    with tempfile.TemporaryFile(mode="w+t") as input_file, tempfile.TemporaryFile(
        mode="w+t"
    ) as output_file:
        input_file.write(input_text)
        input_file.seek(0)
        subprocess.run(
            [executable],
            stdin=input_file,
            stdout=output_file,
            text=True,
            check=True,
        )
        output_file.seek(0)
        output = output_file.read().splitlines()
    if len(output) != len(cases):
        raise SystemExit(f"probe returned {len(output)} rows for {len(cases)} cases")

    for index, ((_, _, _, expected), row) in enumerate(zip(cases, output)):
        got = row.split()
        if got != encode(expected).split():
            raise SystemExit(
                f"G1 mismatch at case {index}: got={got}, expected={encode(expected)}"
            )
    print(f"passed BN254 G1 oracle: {len(cases)} double/mixed-add cases")


if __name__ == "__main__":
    main()
