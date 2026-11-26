# Four interlacing rows of ordered set partitions at threshold three

Bowen Zuo, East China University of Science and Technology.

Let \(P_n(t)\) count ordered partitions of \(n\) labels by the number of blocks of size at least three. For every \(n\ge0\), the rows \(P_n,\ldots,P_{n+3}\) pairwise strictly interlace, with simple negative roots and empty lists for constant rows. A uniform five-row window is ruled out by degree. [Seven-page paper](paper/main.pdf) · [LaTeX and exact certificates](paper/arxiv-source.zip) · [Original conjecture](https://www.symmetricfunctions.com/realRootedOpenProblems.htm#set-partitions-and-trees)

## Rebuild the paper and certificates

Use TeX Live 2026 and Python 3.10 or later. Set `PDFLATEX` if the executable is outside your path.

```sh
sha256sum --check SHA256SUMS
cd paper
python3 -B reproduce.py
python3 -B anc/fixed-three-astra/verify_disks.py
python3 -B anc/fixed-three-astra/verify_corner.py
python3 -B anc/fixed-three-finite/verify.py \
  anc/fixed-three-finite/intervals-239.json --max-old 239 \
  | cmp anc/fixed-three-finite/result-239.json -
```

The disk checker certifies 851 closed parameter intervals for the analytic proof beginning at lower rank 240. The finite checker verifies 720 ordered pairs from lower ranks 0 through 239, using 9,720 rational root brackets and exact integer coefficients. All three checkers use the Python standard library. The optional disk proposer uses mpmath.

## Verify the formal theorem

The top-level declarations are `OrderedPartitions.ThreePole.original_all`, `original_four_rows`, and `five_rows_fail`. They refer to the original ordered objects and encode complete strictly negative simple root arrays. [Statement map](verification/STATEMENT-MAP.md) · [Frozen inputs](verification/SOURCE-PINS.md)

Install Lean 4.33.1 using the pin in `formal/lean-toolchain`. Prepare clean external Lake packages at the commits in `formal/lake-manifest.json`, with their external compiled dependencies. Then run the following on a clean extraction of the formal project.

```sh
cd formal
python3 -B verify.py /absolute/path/to/locked/.lake/packages 1
```

The verifier checks the source closure and dependency lock, builds local modules with warnings as errors, audits transitive axioms and runs a separate kernel replay for every local module. One worker limits memory. The GitHub workflow prepares the same locked Mathlib dependencies and preserves its run receipts as artifacts.

Apache-2.0 applies to the original proof and verification code. The author retains copyright in the manuscript. See [NOTICE](NOTICE).
