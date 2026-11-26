# Spark cold verification

The exact frozen source ZIP was independently extracted into an empty local project on Linux ARM64. Lean 4.33.1 built all 300 local project modules with warnings treated as errors. The verifier cross-checked the local imports resolved by Lean and ran 300 separate `leanchecker` processes. The nine external Git checkouts matched the dependency lock. They were supplied through a separately located, version-locked external dependency cache.

The lexical source scan passed. The 335 source reports and 19 additional targeted reports used only `propext`, `Classical.choice` and `Quot.sound`. `module-receipts.tsv` and `axioms.tsv` contain the exact module digests and declarations. `STATEMENT-MAP.md` maps the all-size threshold-three window and its sharpness to the original rows.

- Source ZIP SHA-256 `bc62a9ca97e1637f6f4db3d1f2de4f05f90073b495ebb3804aac1975325a6c6c`
- Entry source SHA-256 `7ffb18414ef4bad7c5bc8c1450117f3f65893e7a63617e5a89415cfa8a863fdd`
- Cold log SHA-256 `d7b1e7ec31256a43e5da12d69ae4c41ee38e7bbfc9676f818137b0be9fb8256d`

Use `python3 -B run-cold.py /absolute/path/to/locked/.lake/packages --workers 2` next to the source ZIP to extract the project into a fresh temporary directory and verify it again. The README inside the ZIP also gives the commands for direct verification after extraction.
