"""Propose exact sign brackets using integer Bernstein subdivision."""

import argparse
from fractions import Fraction
from math import comb, factorial
import json
from pathlib import Path


GAPS = (1, 2, 3)


def rows_from_last_block(limit):
    rows = [[1]]
    for n in range(1, limit + 1):
        row = [0] * (n // 3 + 1)
        for size in range(1, n + 1):
            ways = comb(n, size)
            mark = int(size >= 3)
            for h, value in enumerate(rows[n - size]):
                row[h + mark] += ways * value
        rows.append(row)
    return rows


def evaluate_transformed(poly, s):
    """Sign of the homogenized evaluation at t = -s/(1-s)."""
    num = -s.numerator
    den = s.denominator - s.numerator
    value, power = poly[-1], 1
    for coefficient in poly[-2::-1]:
        power *= den
        value = value * num + coefficient * power
    return value


def split_location(poly, lo, hi):
    """Choose an interior dyadic split away from all exact roots."""
    for exp in range(1, len(poly) + 1):
        cut = lo + (hi - lo) / (1 << exp)
        value = evaluate_transformed(poly, cut)
        if value:
            return cut, exp, value > 0
    raise ValueError("Too many different interior splits vanish for the polynomial degree")


def variation(values):
    signs = [value > 0 for value in values if value]
    return sum(a != b for a, b in zip(signs, signs[1:]))


def trim(values):
    common = min((abs(x) & -abs(x)).bit_length() - 1 for x in values if x)
    return [x >> common for x in values] if common else values


def subdivide(values, exp):
    d = len(values) - 1
    left, right = [], []
    q = (1 << exp) - 1
    for level in range(d + 1):
        shift = exp * (d - level)
        left.append(values[0] << shift)
        right.append(values[-1] << shift)
        if q == 1:
            values = [a + b for a, b in zip(values, values[1:])]
        else:
            values = [q * a + b for a, b in zip(values, values[1:])]
    return trim(left), trim(right[::-1])


def isolate(poly):
    """Find sign brackets in the variable s where t = -s/(1-s)."""
    degree = len(poly) - 1
    initial = [(-1)**i * a * factorial(i) * factorial(degree - i) for i, a in enumerate(poly)]
    pending = [(Fraction(0), Fraction(1), trim(initial), 0)]
    intervals = []
    while pending:
        lo, hi, values, depth = pending.pop()
        count = variation(values)
        if count == 0:
            continue
        if count == 1:
            if values[0] * values[-1] >= 0:
                raise RuntimeError("A proposed interval has no strict sign change")
            intervals.append((lo, hi, values[0] > 0))
            continue
        if depth >= 150:
            raise RuntimeError("Unresolved Bernstein interval after 150 subdivisions")
        cut, exp, _ = split_location(poly, lo, hi)
        a, b = subdivide(values, exp)
        pending.append((cut, hi, b, depth + 1))
        pending.append((lo, cut, a, depth + 1))
    if len(intervals) != degree:
        raise RuntimeError(f"Located {len(intervals)} strict sign changes for degree {degree}")
    return intervals


def refine(poly, interval):
    lo, hi, positive = interval
    mid, _, sign = split_location(poly, lo, hi)
    return (mid, hi, sign) if sign == positive else (lo, mid, positive)


def to_inner(poly, bracket, target):
    while not (0 < bracket[0] < bracket[1] < 1 and bracket[1] - bracket[0] <= target):
        bracket = refine(poly, bracket)
    return bracket


def separate(rows, brackets, older, newer):
    """Refine only overlapping brackets of this pair of rows."""
    for _ in range(150):
        merged = sorted((lo, hi, n, k) for n in (older, newer)
                        for k, (lo, hi, _) in enumerate(brackets[n]))
        conflict = {(i, k) for a, b in zip(merged, merged[1:]) if a[1] >= b[0]
                    for _, _, i, k in (a, b)}
        if not conflict:
            return
        for rank, index in sorted(conflict):
            brackets[rank][index] = refine(rows[rank], brackets[rank][index])
    raise RuntimeError(f"Root brackets for ranks {older}, {newer} did not separate")


def negative_interval(bracket):
    lo, hi, _ = bracket
    lower, upper = -hi / (1 - hi), -lo / (1 - lo)
    return [lower.numerator, lower.denominator, upper.numerator, upper.denominator]


def generate(max_old, bits):
    rows = rows_from_last_block(max_old + max(GAPS))
    target = Fraction(1, 1 << bits)
    brackets = []
    for rank, polynomial in enumerate(rows):
        brackets.append([to_inner(polynomial, br, target) for br in isolate(polynomial)])
        if rank % 25 == 0:
            print("Isolated rank", rank, flush=True)
    for gap in GAPS:
        for rank in range(max_old + 1):
            separate(rows, brackets, rank, rank + gap)
    return {"format": "ordered-blocks-threshold-three-negative-brackets-v1", "cutoff": 3,
            "max_old_rank": max_old, "upper_rank": max_old + max(GAPS), "gaps": list(GAPS),
            "rows": [[negative_interval(b) for b in reversed(bs)] for bs in brackets]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("--max-old", type=int, default=239)
    parser.add_argument("--bits", type=int, default=32)
    args = parser.parse_args()
    if args.max_old < 0 or args.bits < 1:
        parser.error("Choose a nonnegative last old rank and a positive precision")
    result = generate(args.max_old, args.bits)
    args.output.write_text(json.dumps(result, separators=(",", ":")) + "\n")
    print("Wrote certified candidate intervals for ranks 0 through", result["upper_rank"], flush=True)


if __name__ == "__main__":
    main()
