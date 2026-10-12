# Pompetzki exact matrix workspace

The workspace accepts fresh editable matrices A and B, computes in exact rational arithmetic, and displays the result in its Answer pane. Integers and fractions have no fixed 64-bit numerator limit in this Racket engine. Decimal and exponent inputs are rejected. The original pmp runtime continues to report overflow at its signed 64-bit boundary.

Operations are RREF; rank and nullity with kernel and image bases; a kernel basis; an image basis using original pivot columns; solving A x = b with a particular solution and a homogeneous basis, or an inconsistency result; determinant; inverse or a singularity result; transpose; addition; and multiplication. Rank-nullity is presented as the First Isomorphism Theorem.

Matrix input examples:

```text
[1/2, 1/3; 2/5, 3/7]

rows: 2
cols: 3
1 2 3
2 4 6

empty 0 3
zero 2 3
```

An empty matrix has zero rows or zero columns. `zero 2 3` explicitly specifies the 2-by-3 zero matrix. The 0-by-0 determinant is 1. Solving a consistent system sets free variables to zero for its displayed particular solution and supplies a basis for all homogeneous solutions.

File > Open loads a matrix into A or B. Save Answer and Export Answer require a new file path. Font controls adjust the three text panes. Unary operations use A; partially entered B data does not invalidate an operation that does not use B.

Build into a fresh directory, with Racket's `raco` on PATH:

```text
python build.py --output build-v1
```

This produces `MathWorkbench.exe` and `MathEngine.exe` on Windows. The release packager distributes their Racket runtime dependencies for use on a computer without an installed Racket. On Linux the names have no `.exe` suffix.

The CLI accepts a matrix file or a JSON batch. A batch is an array of objects with `id`, `op`, `a`, and optional `b`, where the matrix values are text. Its JSON results contain exact rational strings. For a single operation:

```text
MathEngine --op solve --a A.txt --b b.txt
MathEngine --batch jobs.json
```

This source derives from Local Grok Build's first matrix draft. `INITIAL-SOURCE-RECEIPT.json` records the four received source hashes. The separate corrected source repairs a malformed multiplication expression, determinant syntax, singular inverse rank reporting, unused B parsing, and input/CLI validation; it adds the font controls and rank-nullity presentation. The first draft remains in `repair/math-workbench`.

The independent Python Fraction oracle in `repair/workbench-oracle/verify.py` checks 849 generated cases, including exact determinant values computed by summing signed permutations. The source CLI and compiled Windows CLI each passed all 849 cases. The native GUI Compute callback passed eight Answer cases with an owned hidden frame; the test sends no simulated keystrokes and does not take user focus. Its save/export tests preserve existing file bytes.

The checked results are finite executable tests, with recorded source and executable hashes. They are not a proof that every possible matrix input will be handled correctly.
