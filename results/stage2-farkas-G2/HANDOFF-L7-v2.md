# G2-farkas handoff to L7, v2

Clock read by Get-Date: 2026-10-09 20:46:38 -04:00.

The index contract is `HANDOFF-L7-v1.md`. This file adds the emission and the judge receipts. Writes from this lane stay in `C:\ClaudeOutput\pompetzki\lanes\G2-farkas\`.

## Index

Path: `C:\ClaudeOutput\pompetzki\lanes\G2-farkas\INDEX.tsv`

sha256: `1748722000B41608B1F9CD8CF4183A68CA9DE05FAF9F73BCDC99C73D04EDB621`

Lines read on 2026-10-09 20:46:38 -04:00: 1,181, which is 1 header plus 1,180 data rows. Header:

`id  class  n  m  path  sha256  max_num_bits  max_den_bits  has_certificate`

Class counts from that read: dense 132, cyclic 13, pigeon 4, transport 8, l2d 4, control 19, mutant-sign 334, mutant-perturb 333, mutant-drop 333. Rows with `has_certificate` 1: 161.

Certificate sexp, the form in L2D `farkas-v1.rkt`, `farkas-v2.rkt`, `farkas-v3.rkt`, and L7 `src-r4/farkas7-v5.rkt`:

`(farkas (A rows) (b vector) (y vector))`

`checker-v1.rkt` returns CERT-OK when each `y_i >= 0`, each column of `y^T A` is 0, and `y^T b < 0`, in exact rationals. Control sexp, `has_certificate` 0:

`(integer-infeasible-rationally-feasible (A rows) (b vector) (x vector) (forced-var j))`

The 1,000 files in `corpus/mut/` are the same certificate sexp with a sign flip, a multiplier perturbed by +1 or -1, or a dropped row. `checker-v1.rkt --batch` recorded in `STATUS-2021.txt`: files 1180, cert 161, control 19, reject 1000.

## Emission both judges accept

File: `C:\ClaudeOutput\pompetzki\lanes\G2-farkas\jdg\cyclic-k02.jdg`

Bytes: 10,792,096. sha256: `361B8E60562582073C578ACDE1A2FA86E178D7317203253CB759CF7126E49FFC`

Source: `corpus/cyclic/cyclic-k02.sexp`

`(farkas (A ((1 -1) (-1 1))) (b (-1 -1)) (y (1 1)))`

`n = 2`, `m = 2`. Each `y_i` is 1. Both columns of `y^T A` are 0. `y^T b = -2`.

Emitter: L2D `farkas-v3.rkt`. Emit start stamp: 2026-10-09 20:24:48 -04:00. Copy of the checker: `(ACCEPT 677 110 5797 787)`. Theorems 110, steps 5797, bytes 10,792,096, build 4,503 ms.

Racket judge, working directory `C:\ClaudeOutput\pompetzki\judge`, start stamp 2026-10-09 20:27:14 -04:00, file `jdg\judge-racket-cyclic-k02-v1.txt`:

`ACCEPT registry 677 theorems 110 steps 5797 final-registry 787` and `EXIT 0`.

pmp judge `C:\ClaudeOutput\pompetzki\pompetzki.exe judge-v3.pmp`, start stamp 2026-10-09 20:27:59 -04:00, log mtime 2026-10-09 20:42:24, file `jdg\judge-pmp-cyclic-k02-v1.txt`:

`ACCEPT`, then 677, 110, 5797, 787, then `EXIT 0`.

L2D `r4\judge-g2-r4.txt`, end stamp `Fri Oct 9 20:44:18 EDT 2026`, ran the same two programs from `C:/ClaudeOutput/pompetzki/judge` (`core-v1.rkt` defines `JUDGE-DIR`, `PMP`, and `RACKET` as those paths) on `r4/g2/cyclic-k02.jdg`. Get-FileHash of that copy is the same `361B8E60562582073C578ACDE1A2FA86E178D7317203253CB759CF7126E49FFC`. Receipt: pmp ACCEPT exit 0, 888,895 ms; racket ACCEPT exit 0, 2,408 ms; both report 677, 110, 5797, 787.

## Discriminating corrupt jdg witnesses, both judges

These four files were rejected by both judges. Each pmp receipt also contains `line 340: check zero failed: not the zero vector` beside the named reason. The receipt has a REJECT line and no `LIMIT` line.

| file under `jdg\cyclic-k02-mut\` | sha256 | racket | pmp | receipt |
|---|---|---|---|---|
| cyclic-k02-use-shift.jdg | 17670BDA5078ABC587CF5B21C69ED009CE949C46168984F3AC22522B85AEC80E | REJECT theorem 3 step 0 (step U), exit 1 | REJECT use: no such registry entry, theorem 3 step 0, exit 1 | this lane, starts 2026-10-09 20:43:04 and 2026-10-09 20:43:27 -04:00 |
| cyclic-k02-registry-suc.jdg | 2FF9B0EFC6C4F9E0AEB9B9A746D92FEA501EDDB493397CB2B2594E506981E026 | REJECT theorem 2 step 23 (step T), exit 1, 445 ms | REJECT taut, theorem 2 step 23, exit 1, 1,008 ms | L2D `r4\judge-g2-r4.txt`; L2D copy has the same sha256 |
| cyclic-k02-taut-goal.jdg | C50B4FEA8A2DAB71D8B5107000FE0A9F2C0DEFB630BFA5C8F0112F9BEED88BB3 | REJECT theorem 3 step 1 (step T), exit 1, 401 ms | REJECT taut, theorem 3 step 1, exit 1, 1,093 ms | same L2D receipt; same sha256 |
| cyclic-k02-exel-var.jdg | B0F36BC5E202AB5B864EAED631D1C0D8E6FBCFA5A24D942E167B150A9A1E5AAF | REJECT theorem 3 step 6 (step L), exit 1, 493 ms | REJECT exel, theorem 3 step 6, exit 1, 1,073 ms | same L2D receipt; same sha256 |

## Same emission, copy of the checker, official judges unrun

From `jdg\emit-cyclic-k02-v1.txt`. The two official judges were not run by this lane on these seven files.

- main-last-taut-neg: REJECT 109 step 1068 taut. sha256 `48AE58620EF42B1F2D298D35761441E1A426798C6B2CB8987FF9D403BE8609CB`
- main-mid-taut-drop: ACCEPT 677 110 5797 787. sha256 `C1C73A6D3B315ACC452115097391125C5693D3ED094CD52717F9496F71F9D698`. This copy-of-checker result is ACCEPT, so this file is not in the rejected-witness list above.
- neg-final: REJECT 109 final. sha256 `E7E08DD34E96548B776C3EC823FFAB8B960722B5049E9E0ABAB14B1C79405ECB`
- twin-final: REJECT 109 final. sha256 `E7E08DD34E96548B776C3EC823FFAB8B960722B5049E9E0ABAB14B1C79405ECB`, the same hash and the same length 10,792,098 as neg-final
- drop-step: REJECT 109 final. sha256 `AF90FF6267499F088A6D8C9C5C0177AE8A68E90E4374B2B69026103CD061E621`
- leib-swap: REJECT 63 step 21 leib. sha256 `2817106D3787E9EDD79C975A6C2420D075725EB3720FE8279265227C599907C3`
- exi-witness: REJECT 3 step 3 exi. sha256 `568B882EDB53F5EB0E22FDC0D3D91DFEA68F06BAA5B79B628AEBF6E7898534CC`

## L7 receipts read, not re-run

`C:\ClaudeOutput\pompetzki\lanes\L7\judge-r4-farkas.txt` line 1: `L7-5-farkas-l2d.jdg` pmp ACCEPT exit 0, 374,784 ms; racket ACCEPT exit 0, 2,677 ms; both 677, 236, 4985, final registry 913.

Line 2: `L7-5-farkas-l2d-neg-final.jdg` pmp REJECT exit 1, 306,027 ms; racket REJECT exit 1, 1,802 ms; theorem 235 step 244, final.

`judge-r4-farkas-mutA.txt` (end stamp `Fri Oct 9 20:27:01 EDT 2026`) and `judge-r4-farkas-mutB.txt` (end stamp `Fri Oct 9 20:27:05 EDT 2026`) record both-judge REJECT, exit 1, for twin-final, taut-goal, mp-swap, use-shift, leib-swap, exi-witness, drop-step, exel-var, alli-var, gen-var, ax-flip, and registry-suc. Each pmp line also contains `line 340: check zero failed`.

## L2D sample receipts read, not re-run

`C:\ClaudeOutput\pompetzki\lanes\L2D\farkas\judge-run-1-FA.txt` has 7 lines. f1-1d.jdg and f4-2d.jdg: both judges ACCEPT. Five f1 mutants: both judges REJECT.

`C:\ClaudeOutput\pompetzki\lanes\L2D\r4\judge-f2-r4.txt`, end stamp `Fri Oct 9 20:42:30 EDT 2026`: pmp `LIMIT a memory block is full`, exit 1, 1,398,391 ms, at 130 1317, then `line 348: check zero failed`. Racket ACCEPT exit 0, 4,248 ms, registry 677 theorems 131 steps 7216 final-registry 808. A LIMIT stop is not a REJECT. Both-judge ACCEPT is not claimed for f2-2d.jdg.

`C:\ClaudeOutput\pompetzki\lanes\L2D\r4\judge-f3-r4.txt`, end stamp `Fri Oct 9 20:42:00 EDT 2026`: pmp `LIMIT a memory block is full`, exit 1, 1,369,715 ms, at 105 1357, then `line 348: check zero failed`. Racket ACCEPT exit 0, 4,284 ms, registry 677 theorems 106 steps 6180 final-registry 783. Both-judge ACCEPT is not claimed for f3-2d.jdg.

Non-corpus sha256 list: `manifest-sha256-v1.txt`, sha256 `FE002964267AE8259D948C765D54CA83ADC521BDB9E9C893B221BD78F62E7EAF`, 43 files, written 2026-10-09 20:44:23 -04:00. Corpus sexp hashes stay in `INDEX.tsv`.
