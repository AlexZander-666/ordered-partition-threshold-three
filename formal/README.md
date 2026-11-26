# Four-row interlacing at threshold three

For every rank n and gap h from one through three, the rank-n and rank-(n+h) large-block polynomials of ordered labelled set partitions interlace strictly, with constant rows interpreted using empty root lists. Every block of size at least three contributes one power of the variable. The formal statement uses the original row, and its mathematical dependencies include an exact finite certificate and the oscillatory interval argument.

Extract the source archive into a fresh directory and run the following from that directory. The first argument names a separate directory of clean external packages at the commits in lake-manifest.json, with their compiled external dependencies. The final argument bounds simultaneous project build targets and kernel checks. Four workers are suitable for the DGX Spark used to prepare the archive.

    python3 -B verify.py /path/to/locked/.lake/packages 4

The verifier checks the complete local import closure, hashes of the source and supporting files, the external dependency locks and Lean version. It compiles all project modules from source with warnings as errors, resolves their imports through Lean, and queues a separate Lean kernel replay of each compiled object. The declarations named in audit-names.txt receive an additional transitive axiom audit.
