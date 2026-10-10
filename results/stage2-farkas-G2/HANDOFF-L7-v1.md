# G2-farkas handoff to L7

Clock: 2026-10-09 20:21:24 -04:00.

L7 reads certificates. This lane does not write into L7.

## Index

Path: `C:\ClaudeOutput\pompetzki\lanes\G2-farkas\INDEX.tsv`

sha256: `1748722000B41608B1F9CD8CF4183A68CA9DE05FAF9F73BCDC99C73D04EDB621`

Rows: 1,180 data rows plus a header. Columns, tab-separated:

`id  class  n  m  path  sha256  max_num_bits  max_den_bits  has_certificate`

`path` is relative to `C:\ClaudeOutput\pompetzki\lanes\G2-farkas\`. `sha256` is the SHA-256 of that file, uppercase hex from Get-FileHash. `max_num_bits` is `(integer-length N)` where N is the largest absolute numerator in the sexp. `max_den_bits` is `(integer-length D)` where D is the largest denominator. An integer has denominator 1, and `(integer-length 1)` is 1. `has_certificate` is 1 when checker-v1.rkt returns CERT-OK, and 0 otherwise.

## Counts from corpus-counts-v1.txt, confirmed by checker-v1.rkt --batch corpus

| class | files | checker result |
|---|---:|---|
| dense | 132 | CERT-OK |
| cyclic | 13 | CERT-OK |
| pigeon | 4 | CERT-OK |
| transport | 8 | CERT-OK |
| l2d | 4 | CERT-OK |
| control | 19 | CONTROL-OK |
| mutant-sign | 334 | REJECT |
| mutant-perturb | 333 | REJECT |
| mutant-drop | 333 | REJECT |

Batch totals: files 1180, cert 161, control 19, reject 1000.

Dense coefficient range recorded in corpus-counts-v1.txt: minimum -41, maximum 45. Every dense entry is an integer in [-50, 50]. Largest numerator bit size in the index is 28. Largest denominator bit size is 3, from control witnesses.

## Format

Certificate sexp, the form read by L2D farkas-v1.rkt, farkas-v2.rkt, farkas-v3.rkt and by L7 src-r4/farkas7-v5.rkt:

`(farkas (A rows) (b vector) (y vector))`

Integers. checker-v1.rkt accepts a file only when each `y_i >= 0`, each column of `y^T A` is 0, and `y^T b < 0`, all in exact rationals. The stored certificates are integers.

Control sexp, no Farkas certificate:

`(integer-infeasible-rationally-feasible (A rows) (b vector) (x vector) (forced-var j))`

checker-v1.rkt returns CONTROL-OK when `A x <= b`, `x_j` is not an integer, and two opposing rows force `x_j` to that value. These 19 files are the rationally feasible controls. `has_certificate` is 0.

The four `corpus/l2d/` files are byte copies of `C:\ClaudeOutput\pompetzki\lanes\L2D\farkas\in\f1-1d.sexp`, `f2-2d.sexp`, `f3-2d.sexp`, and `f4-2d.sexp`.

## Source hashes

| file | sha256 |
|---|---|
| ORDER.md | 69DBB762E214159702006EE158BC9683DE17AAD22E4FF387FFB51922B0A26F12 |
| checker-v1.rkt | 464A6DC945276121C22186621B7F70D4DFC65627946773B1329B3DA87B431159 |
| generator-v3.rkt | F4891D584B22C8D2A4A8E39956455DCCA17D24F56C6564C5A66CF68392E0993E |
| index-v2.rkt | 39B5FE7EE417D06122C094D4C8ACFC70C0FA2AAD24B4C53AD7183CC4827AAF6C |
| corpus-counts-v1.txt | C62C4BF61DC7E0274921AD09CE127A1396DC57289A114A17FB79821877287BDE |

generator-v1.rkt and generator-v2.rkt are kept and do not load. generator-v3.rkt is the program that found the certificates: exact phase-1 simplex with a lexicographic ratio test, and Fourier-Motzkin with multiplier vectors on systems with `n <= 1`, or `n <= 2` and `m <= 16`, or `n <= 3` and `m <= 8`. The build printed `memory-records 1180 certificates 161 controls 19 mutants 1000` and then stopped because `pwsh` returned a non-zero status during hashing. The sexps were already written. sha256-lines-v2.txt is the hash list index-v2.rkt used.

## Corrupt witnesses

`corpus/mut/` has 1,000 files in the same sexp form. Each was rejected by checker-v1.rkt. Kinds: 334 sign flips of a positive multiplier, 333 perturbations of a multiplier by +1 or -1 on a nonzero row, 333 dropped rows whose multiplier was positive and whose row was nonzero. `has_certificate` is 0 on every mutant row. The index path is the mutant file, not a certificate.

## Judges already recorded, not re-run

`C:\ClaudeOutput\pompetzki\lanes\L2D\farkas\judge-run-1-FA.txt` records both judges on L2D's own emissions of the same four sample sexps that are copied in `corpus/l2d/`. Opening lines:

- `farkas/out/f1-1d.jdg`: pmp ACCEPT exit 0, 344485 ms; racket ACCEPT exit 0, 1343 ms. Final registry 783.
- `farkas/out/f4-2d.jdg`: pmp ACCEPT exit 0, 825431 ms; racket ACCEPT exit 0, 3237 ms. Final registry 794.
- `farkas/out/f1-1d-mut/f1-1d-drop-step.jdg`: pmp REJECT exit 1; racket REJECT exit 1.

L7 `STATUS-1911.txt` records farkas7-v4.rkt on those four certificates in one test file: Racket judge ACCEPT, pmp judge ACCEPT. This handoff does not repeat those runs.

## Next emission from this corpus

One new emission, not one of the four samples: `corpus/cyclic/cyclic-k02.sexp`,

`(farkas (A ((1 -1) (-1 1))) (b (-1 -1)) (y (1 1)))`.

`n = 2`, `m = 2`, `y^T b = -2`. Output directory for that run: `C:\ClaudeOutput\pompetzki\lanes\G2-farkas\jdg\`. The emitter is L2D `farkas-v3.rkt`. Both judges will be run on the emitted file, one process at a time, from `C:\ClaudeOutput\pompetzki\judge\`. A later handoff file will carry the verdicts.
