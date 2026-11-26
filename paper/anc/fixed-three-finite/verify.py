"""Check the original rows, strict integer sign changes and every root order."""

import argparse
from fractions import Fraction
from hashlib import sha256
from math import comb
import json
from pathlib import Path


def require(condition, details):
    if not condition:
        raise ValueError(details)


def split_at_marked_blocks(limit):
    """Build [z^n] B^h V^(h+1) in exponential normalization."""
    choices = [[comb(n, s) for s in range(n + 1)] for n in range(limit + 1)]
    unmarked = [1]
    for n in range(1, limit + 1):
        value = n * unmarked[n - 1]
        if n >= 2:
            value += choices[n][2] * unmarked[n - 2]
        unmarked.append(value)
    marked_then_free = [sum(choices[n][b] * unmarked[n - b] for b in range(3, n + 1))
                        for n in range(limit + 1)]
    rows = [[value] for value in unmarked]
    col = unmarked
    for h in range(1, limit // 3 + 1):
        first = h * 3
        col = [0] * first + [sum(choices[n][s] * marked_then_free[s] * col[n - s]
                                 for s in range(3, n - first + 4))
                             for n in range(first, limit + 1)]
        for n in range(first, limit + 1):
            rows[n].append(col[n])
    return rows


def direct_labeled_row(n):
    """List each set partition by increasing least labels, then count its orders."""
    row = [0] * (n // 3 + 1)

    def visit(next_label, blocks):
        if next_label == n:
            count = sum(len(block) >= 3 for block in blocks)
            ways = 1
            for i in range(1, len(blocks) + 1):
                ways *= i
            row[count] += ways
            return
        for block in blocks:
            block.append(next_label)
            visit(next_label + 1, blocks)
            block.pop()
        blocks.append([next_label])
        visit(next_label + 1, blocks)
        blocks.pop()

    visit(0, [])
    return row


def cleared_eval(poly, x):
    """Compute the polynomial at a rational argument times its positive denominator power."""
    value = poly[-1]
    for i in range(len(poly) - 2, -1, -1):
        value = x.numerator * value + poly[i] * x.denominator ** (len(poly) - 1 - i)
    return value


def verify(path, required_max_old):
    raw = path.read_bytes()
    witness = json.loads(raw)
    require(witness["format"] == "ordered-blocks-threshold-three-negative-brackets-v1", "wrong format")
    require(witness["cutoff"] == 3 and witness["gaps"] == [1, 2, 3], "wrong cutoff or gaps")
    old_upper, limit = witness["max_old_rank"], witness["upper_rank"]
    require(type(old_upper) is int and old_upper == required_max_old and limit == old_upper + 3,
            "rank range differs from the requested certificate")
    require(len(witness["rows"]) == limit + 1, "missing or extra rows")
    rows = split_at_marked_blocks(limit)
    through = min(7, limit)
    for n in range(through + 1):
        require(rows[n] == direct_labeled_row(n), (n, "direct labeled counts disagree"))
    require(rows[:3] == [[1], [1], [3]], "incorrect initial constant rows")

    intervals = []
    max_den_bits = 0
    for n, encoded in enumerate(witness["rows"]):
        p = rows[n]
        degree = len(p) - 1
        require(degree == n // 3 and p[0] > 0 and p[-1] > 0, (n, "actual degree or edge"))
        require(len(encoded) == degree, (n, "number of brackets differs from actual degree"))
        row = []
        for i, entry in enumerate(encoded):
            require(len(entry) == 4 and all(type(v) is int for v in entry), (n, i, "invalid fraction"))
            a, b, c, d = entry
            require(b > 0 and d > 0, (n, i, "denominators must be positive"))
            lo, hi = Fraction(a, b), Fraction(c, d)
            require(lo < hi < 0 and (not row or row[-1][1] < lo), (n, i, "invalid negative bracket"))
            require(cleared_eval(p, lo) * cleared_eval(p, hi) < 0, (n, i, "endpoints lack strict opposite signs"))
            row.append((lo, hi))
            max_den_bits = max(max_den_bits, b.bit_length(), d.bit_length())
        intervals.append(row)

    checked = {"same_degree": 0, "degree_increase": 0, "constant_to_constant": 0, "constant_to_linear": 0}
    for gap in (1, 2, 3):
        for lower in range(old_upper + 1):
            upper = lower + gap
            p, q = intervals[lower], intervals[upper]
            case = (lower, upper)
            if not p:
                if not q:
                    checked["constant_to_constant"] += 1
                else:
                    require(len(q) == 1, (case, "the first positive degree must be one"))
                    checked["constant_to_linear"] += 1
                continue
            merged = sorted([(a, b, 0) for a, b in p] + [(a, b, 1) for a, b in q])
            require(all(a[1] < b[0] for a, b in zip(merged, merged[1:])), (case, "cross-row brackets overlap"))
            if len(q) == len(p):
                pattern = [0, 1] * len(p)
                checked["same_degree"] += 1
            else:
                require(len(q) == len(p) + 1, (case, "degree jump exceeds one"))
                pattern = [1, 0] * len(p) + [1]
                checked["degree_increase"] += 1
            require([which for _, _, which in merged] == pattern, (case, "strict root order fails"))

    row_bytes = (json.dumps(rows, separators=(",", ":")) + "\n").encode()
    return {"status": "PASS", "cutoff": 3, "max_old_rank": old_upper, "upper_rank": limit,
            "verified_rows": len(rows), "compared_pairs": sum(checked.values()), "pair_breakdown": checked,
            "total_strict_negative_brackets": sum(len(row) for row in intervals),
            "largest_denominator_bits": max_den_bits, "direct_labeled_enumeration_through": through,
            "first_rows": rows[:8], "integer_rows_sha256": sha256(row_bytes).hexdigest(),
            "certificate_sha256": sha256(raw).hexdigest()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witness", type=Path)
    parser.add_argument("--max-old", type=int, default=239)
    args = parser.parse_args()
    print(json.dumps(verify(args.witness, args.max_old), indent=2))


if __name__ == "__main__":
    main()
