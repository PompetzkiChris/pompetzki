# RESULTS

Lane G2-farkas. Clock read by Get-Date: 2026-10-09 20:47:44 -04:00. Recovery deadline stated in the order: 21:22:36 tonight. Reboot time stated in the order: 19:34:29 EDT.

## Format

One certificate sexp is used:

`(farkas (A rows) (b vector) (y vector))`

That is the form in L2D `farkas-v1.rkt`, `farkas-v2.rkt`, and `farkas-v3.rkt`, and the form read by L7 `src-r4/farkas7-v5.rkt`. No second format was written.

`checker-v1.rkt` accepts a certificate when every multiplier is an exact rational, every multiplier is `>= 0`, every column of `y^T A` is 0, and `y^T b < 0`. The stored certificates are integers. Bit size is `(integer-length N)` of the largest absolute numerator and `(integer-length D)` of the largest denominator. An integer has denominator 1, and `(integer-length 1)` is 1.

Control sexp, with no certificate:

`(integer-infeasible-rationally-feasible (A rows) (b vector) (x vector) (forced-var j))`

## Solver

`generator-v3.rkt` is the program that wrote the corpus. It searches with an exact phase-1 simplex: Dantzig entering column, lexicographic ratio test, exact rationals, artificial variables, pivot cap 20,000. The recorded `y` is that solution after clearing denominators and dividing by the gcd. Fourier-Motzkin with multiplier vectors runs when `n <= 1`, or `n <= 2` and `m <= 16`, or `n <= 3` and `m <= 8`. A positive-negative pair count above 3,000 returns `cap`. The build seed is `random-seed` 20261009, set after the selftest. The writer rejects a sexp whose text contains a decimal point. No floating-point value decides a certificate, a control, or a rejection.

The earlier run printed `SELFTEST-OK` and then `memory-records 1180 certificates 161 controls 19 mutants 1000`, and then exited 1 at `sha256: pwsh`. The sexp files were already written. `sha256-lines-v1.txt` is the empty file from that exit. `sha256-lines-v2.txt` is the later hash list, 1,180 lines. This recovery did not re-run `generator-v3.rkt build`, `checker-v1.rkt --batch`, or `index-v2.rkt`.

`generator-v1.rkt` and `generator-v2.rkt` are on disk. The earlier load of v1 failed on a duplicate `make-control` and a call to an unexported `farkas-parts`. The earlier load of v2 failed at line 747, `define: not allowed in an expression context`. Those two files were not edited and were not loaded again in this recovery.

`stats-v1.rkt` would re-solve the 161 certificates. It was not run. `solver-counts-v1.txt` does not exist. Fourier-Motzkin tried, certificate, and cap counts, and the pivot sum and pivot max, were held in the build's hash table and were not written.

## Corpus

`INDEX.tsv` was recounted at 2026-10-09 20:46:38 -04:00: 1,181 lines, header plus 1,180 data rows. Rows with `has_certificate` 1: 161.

| class | rows |
|---|---:|
| dense | 132 |
| cyclic | 13 |
| pigeon | 4 |
| transport | 8 |
| l2d | 4 |
| control | 19 |
| mutant-sign | 334 |
| mutant-perturb | 333 |
| mutant-drop | 333 |

Dense: `n` from 2 through 12 and `m` in 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 32, 40. That is 11 times 12 = 132. `corpus-counts-v1.txt` records dense coefficient minimum -41 and maximum 45. The generator forces dense entries into [-50, 50].

Cyclic `k` in 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 24. The system is `x_i - x_{i+1} <= -1` around the cycle, including `x_k - x_1 <= -1`. `cyclic-k02.sexp` is `(farkas (A ((1 -1) (-1 1))) (b (-1 -1)) (y (1 1)))`. Both multipliers are positive, both columns of `y^T A` are 0, and `y^T b = -2`.

Pigeon: `h` from 1 through 4, pigeons `p = h + 1`.

Transport, eight pairs, each with total supply below total demand: supplies `(3 4)` demands `(5 3)`; `(2 2)` and `(2 2 1)`; `(1 1 1)` and `(2 1 1)`; `(5 5 5)` and `(4 4 4 4)`; `(2 3 4)` and `(6 5)`; `(1 1 1 1)` and `(3 2)`; `(10 10)` and `(7 7 7)`; `(4 4 4 4)` and `(5 5 5 5)`.

Controls: 12 files with `n` from 1 through 12 and forced variable 0, plus 7 files with `n` from 2 through 8 and forced variable `n - 1`. The forced value cycles by `n mod 4` through 1/2, 1/3, 2/5, and -1/2. The build required the simplex status `infeasible` on the Farkas system and a feasible rational `x` with `A x <= b`. `has_certificate` is 0.

L2D: `corpus/l2d/` holds byte copies of `f1-1d.sexp`, `f2-2d.sexp`, `f3-2d.sexp`, and `f4-2d.sexp`. The build required the simplex certificate, after integer reduction, to equal the `y` in each file.

Mutants: indices 0 through 333 flip the sign of a positive multiplier (334). Indices 334 through 666 add +1 or -1 to a multiplier on a nonzero row (333). Indices 667 through 999 drop a nonzero row whose multiplier is positive (333). The build required `cert-fail-reason` to be nonempty before writing each one.

`STATUS-2021.txt` records `checker-v1.rkt --batch` on `corpus`: files 1180, cert 161, control 19, reject 1000. That batch was not repeated after the 19:34:29 EDT reboot.

`corpus-counts-v1.txt` records `num-bits-max` 28 and `den-bits-max` 3. The denominator bit size 3 is from a control witness.

## Judges on this lane's emission

`jdg\cyclic-k02.jdg`, 10,792,096 bytes, sha256 `361B8E60562582073C578ACDE1A2FA86E178D7317203253CB759CF7126E49FFC`. The L2D emitter printed that sha256 in lowercase. Get-FileHash matches it.

Emit start 2026-10-09 20:24:48 -04:00, L2D `farkas-v3.rkt`, exit 0. Theorems 110, steps 5,797, build 4,503 ms. Copy of the checker: `(ACCEPT 677 110 5797 787)`.

Racket judge from `C:\ClaudeOutput\pompetzki\judge`, start 2026-10-09 20:27:14 -04:00: `ACCEPT registry 677 theorems 110 steps 5797 final-registry 787`, `EXIT 0`.

pmp `judge-v3.pmp`, start 2026-10-09 20:27:59 -04:00, log mtime 2026-10-09 20:42:24: `ACCEPT`, counts 677, 110, 5797, 787, `EXIT 0`.

L2D `r4\judge-g2-r4.txt`, end stamp `Fri Oct 9 20:44:18 EDT 2026`, ran `pompetzki.exe judge-v3.pmp` and `racket\judge.rkt` from `C:/ClaudeOutput/pompetzki/judge` on a copy whose sha256 is the same value. pmp ACCEPT exit 0, 888,895 ms. Racket ACCEPT exit 0, 2,408 ms. Same counts, final registry 787.

Both judges agree on ACCEPT for this file.

## Discriminating jdg rejections

`jdg\cyclic-k02-use-shift.jdg`, sha256 `17670BDA5078ABC587CF5B21C69ED009CE949C46168984F3AC22522B85AEC80E`. Racket start 2026-10-09 20:43:04 -04:00: `REJECT theorem 3 step 0 (step U)`, `EXIT 1`. pmp start 2026-10-09 20:43:27 -04:00: `REJECT`, `use: no such registry entry`, theorem 3 step 0, `EXIT 1`. The pmp text also contains `line 340: check zero failed: not the zero vector`. There is no `LIMIT` line.

L2D `r4\judge-g2-r4.txt` records both official judges on three further files. Get-FileHash of each L2D copy equals the hash of the file in this folder:

- `cyclic-k02-registry-suc.jdg`, sha256 `2FF9B0EFC6C4F9E0AEB9B9A746D92FEA501EDDB493397CB2B2594E506981E026`. pmp REJECT taut, theorem 2 step 23, exit 1, 1,008 ms. Racket REJECT theorem 2 step 23 (step T), exit 1, 445 ms.
- `cyclic-k02-taut-goal.jdg`, sha256 `C50B4FEA8A2DAB71D8B5107000FE0A9F2C0DEFB630BFA5C8F0112F9BEED88BB3`. pmp REJECT taut, theorem 3 step 1, exit 1, 1,093 ms. Racket REJECT theorem 3 step 1 (step T), exit 1, 401 ms.
- `cyclic-k02-exel-var.jdg`, sha256 `B0F36BC5E202AB5B864EAED631D1C0D8E6FBCFA5A24D942E167B150A9A1E5AAF`. pmp REJECT exel, theorem 3 step 6, exit 1, 1,073 ms. Racket REJECT theorem 3 step 6 (step L), exit 1, 493 ms.

Each of those pmp lines also contains `line 340: check zero failed`.

Copy of the checker inside the emitter, for the seven files whose official judges were not run:

- main-last-taut-neg: REJECT 109 step 1068 taut
- main-mid-taut-drop: ACCEPT 677 110 5797 787
- neg-final: REJECT 109 final
- twin-final: REJECT 109 final
- drop-step: REJECT 109 final
- leib-swap: REJECT 63 step 21 leib
- exi-witness: REJECT 3 step 3 exi

`main-mid-taut-drop` is an ACCEPT from that copy of the checker. It is not in the rejected-witness list. `cyclic-k02-neg-final.jdg` and `cyclic-k02-twin-final.jdg` share sha256 `E7E08DD34E96548B776C3EC823FFAB8B960722B5049E9E0ABAB14B1C79405ECB` and length 10,792,098.

## L2D and L7 receipts read, not re-run

`C:\ClaudeOutput\pompetzki\lanes\L2D\farkas\judge-run-1-FA.txt`, 7 lines:

- f1-1d.jdg: pmp ACCEPT exit 0, 344,485 ms; racket ACCEPT exit 0, 1,343 ms; 677, 106, 5069, final 783
- f4-2d.jdg: pmp ACCEPT exit 0, 825,431 ms; racket ACCEPT exit 0, 3,237 ms; 677, 117, 6162, final 794
- f1-1d-drop-step.jdg: both REJECT exit 1, theorem 105 step 809, final
- f1-1d-exel-var.jdg: both REJECT exit 1, theorem 5 step 21
- f1-1d-exi-witness.jdg: both REJECT exit 1, theorem 52 step 28
- f1-1d-leib-swap.jdg: both REJECT exit 1, theorem 59 step 21
- f1-1d-main-last-taut-neg.jdg: both REJECT exit 1, theorem 105 step 803

`C:\ClaudeOutput\pompetzki\lanes\L2D\r4\judge-f2-r4.txt`, end stamp `Fri Oct 9 20:42:30 EDT 2026`: pmp `LIMIT a memory block is full`, exit 1, 1,398,391 ms, position 130 1317, then `line 348: check zero failed`. Racket ACCEPT exit 0, 4,248 ms, registry 677 theorems 131 steps 7216 final-registry 808. A LIMIT stop is not a REJECT. Both-judge ACCEPT is not claimed for `f2-2d.jdg`.

`C:\ClaudeOutput\pompetzki\lanes\L2D\r4\judge-f3-r4.txt`, end stamp `Fri Oct 9 20:42:00 EDT 2026`: pmp `LIMIT a memory block is full`, exit 1, 1,369,715 ms, position 105 1357, then `line 348: check zero failed`. Racket ACCEPT exit 0, 4,284 ms, registry 677 theorems 106 steps 6180 final-registry 783. Both-judge ACCEPT is not claimed for `f3-2d.jdg`.

L7 `judge-r4-farkas.txt`: `L7-5-farkas-l2d.jdg` pmp ACCEPT exit 0, 374,784 ms; racket ACCEPT exit 0, 2,677 ms; 677, 236, 4985, final 913. `L7-5-farkas-l2d-neg-final.jdg` both REJECT exit 1, theorem 235 step 244; pmp 306,027 ms; racket 1,802 ms.

L7 `judge-r4-farkas-mutA.txt`, end stamp `Fri Oct 9 20:27:01 EDT 2026`, both REJECT exit 1: twin-final theorem 235 step 244; taut-goal theorem 14 step 9; mp-swap theorem 20 step 42; use-shift theorem 14 step 1; leib-swap theorem 14 step 4; exi-witness theorem 20 step 37.

L7 `judge-r4-farkas-mutB.txt`, end stamp `Fri Oct 9 20:27:05 EDT 2026`, both REJECT exit 1: drop-step theorem 235 step 243; exel-var theorem 14 step 10; alli-var theorem 20 step 6; gen-var theorem 43 step 38; ax-flip theorem 37 step 26; registry-suc theorem 26 step 13.

L7 `STATUS-1911.txt` records an earlier both-judge ACCEPT of `farkas7-v4.rkt` on f1 through f4 in one test file: 236 theorems, 4,985 steps, final registry 913. The `judge-r4-farkas.txt` line above is the later receipt of `L7-5-farkas-l2d.jdg` with those same counts.

## Unfinished, with status

Fourier-Motzkin tried, certificate, and cap counts, and the pivot sum and pivot max: not written. `stats-v1.rkt` was not run, so the 161 certificates were not solved a second time.

Official `judge-v3.pmp` and `racket\judge.rkt` were not run by this lane on `cyclic-k02-main-last-taut-neg.jdg`, `cyclic-k02-main-mid-taut-drop.jdg`, `cyclic-k02-neg-final.jdg`, `cyclic-k02-twin-final.jdg`, `cyclic-k02-drop-step.jdg`, `cyclic-k02-leib-swap.jdg`, or `cyclic-k02-exi-witness.jdg`. The emitter's copy of the checker is the record for those seven, quoted above.

## Files and sha256

`manifest-sha256-v1.txt` sha256 `FE002964267AE8259D948C765D54CA83ADC521BDB9E9C893B221BD78F62E7EAF`, 4,348 bytes, 43 files, written 2026-10-09 20:44:23 -04:00. It lists every file in this folder except the `corpus\` tree and except files written after it. Columns are sha256, byte length, relative path.

`HANDOFF-L7-v2.md` sha256 `78F67EBB9B44D0D710B56B5835574C5DCEAA70CACF1AE1BF2440BE73BF08CE21`, 7,185 bytes. Hashed at 2026-10-09 20:47:44 -04:00, after the manifest.

The 1,180 corpus sexp hashes are column 6 of `INDEX.tsv` and the 1,180 lines of `sha256-lines-v2.txt`, in the order of `sha256-lines-v1.txt.paths.txt`. They were not hashed again for the manifest.

| sha256 | bytes | path |
|---|---:|---|
| 464A6DC945276121C22186621B7F70D4DFC65627946773B1329B3DA87B431159 | 5829 | checker-v1.rkt |
| C62C4BF61DC7E0274921AD09CE127A1396DC57289A114A17FB79821877287BDE | 221 | corpus-counts-v1.txt |
| 6B548BE8B7EDCB3895216E6E4F4A33BDCB0DB27791FCB423D7314431D2292180 | 34026 | generator-v1.rkt |
| FF7BE36D7874689D5CD2E30CF53451E87977B5F448AE5E61F14928322D65ABC7 | 33125 | generator-v2.rkt |
| F4891D584B22C8D2A4A8E39956455DCCA17D24F56C6564C5A66CF68392E0993E | 33201 | generator-v3.rkt |
| 0596C615C1EB3180E7FF548EFAAF7B0F9BB495D05697B846DD69B412F52AC361 | 1028 | grok-run.log |
| FC8A0B805D8EEB051DD011C4628E8179118147F4AE185F24257E188C61DD6603 | 4968 | HANDOFF-L7-v1.md |
| 7B251CC0354CCAD796312C94F46C839AB81BDEB377833A83F5F6D1B9E920D515 | 4324 | index-v1.rkt |
| 39B5FE7EE417D06122C094D4C8ACFC70C0FA2AAD24B4C53AD7183CC4827AAF6C | 4791 | index-v2.rkt |
| 1748722000B41608B1F9CD8CF4183A68CA9DE05FAF9F73BCDC99C73D04EDB621 | 156700 | INDEX.tsv |
| AF90FF6267499F088A6D8C9C5C0177AE8A68E90E4374B2B69026103CD061E621 | 10792087 | jdg\cyclic-k02-mut\cyclic-k02-drop-step.jdg |
| B0F36BC5E202AB5B864EAED631D1C0D8E6FBCFA5A24D942E167B150A9A1E5AAF | 10792096 | jdg\cyclic-k02-mut\cyclic-k02-exel-var.jdg |
| 568B882EDB53F5EB0E22FDC0D3D91DFEA68F06BAA5B79B628AEBF6E7898534CC | 10792096 | jdg\cyclic-k02-mut\cyclic-k02-exi-witness.jdg |
| 2817106D3787E9EDD79C975A6C2420D075725EB3720FE8279265227C599907C3 | 10792096 | jdg\cyclic-k02-mut\cyclic-k02-leib-swap.jdg |
| 48AE58620EF42B1F2D298D35761441E1A426798C6B2CB8987FF9D403BE8609CB | 10792098 | jdg\cyclic-k02-mut\cyclic-k02-main-last-taut-neg.jdg |
| C1C73A6D3B315ACC452115097391125C5693D3ED094CD52717F9496F71F9D698 | 10792092 | jdg\cyclic-k02-mut\cyclic-k02-main-mid-taut-drop.jdg |
| E7E08DD34E96548B776C3EC823FFAB8B960722B5049E9E0ABAB14B1C79405ECB | 10792098 | jdg\cyclic-k02-mut\cyclic-k02-neg-final.jdg |
| 2FF9B0EFC6C4F9E0AEB9B9A746D92FEA501EDDB493397CB2B2594E506981E026 | 10792096 | jdg\cyclic-k02-mut\cyclic-k02-registry-suc.jdg |
| C50B4FEA8A2DAB71D8B5107000FE0A9F2C0DEFB630BFA5C8F0112F9BEED88BB3 | 10792098 | jdg\cyclic-k02-mut\cyclic-k02-taut-goal.jdg |
| E7E08DD34E96548B776C3EC823FFAB8B960722B5049E9E0ABAB14B1C79405ECB | 10792098 | jdg\cyclic-k02-mut\cyclic-k02-twin-final.jdg |
| 17670BDA5078ABC587CF5B21C69ED009CE949C46168984F3AC22522B85AEC80E | 10792096 | jdg\cyclic-k02-mut\cyclic-k02-use-shift.jdg |
| 75904305F05B38DEFC0B44F46E90492C10E545DDC64DDF2F523CCF628E350E41 | 1488 | jdg\cyclic-k02.index.txt |
| 361B8E60562582073C578ACDE1A2FA86E178D7317203253CB759CF7126E49FFC | 10792096 | jdg\cyclic-k02.jdg |
| 8DF963540AE49B85CFBD25AAAD8904402844CFEACE8296C0020553ACEE6D152E | 1471 | jdg\cyclic-k02.manifest.txt |
| F663056E3F3D163888601D6DF20EDAEE7698A90D295BEED3791AF2BE8EE349EF | 28 | jdg\emit-cyclic-k02-START.txt |
| 6C13AFDCD683597936A24FEF87A5B1522FD6270392755783E026EB1AC663DAAC | 1497 | jdg\emit-cyclic-k02-v1.txt |
| 16DB64DC41C313B06632946AC60C85AC23947C18F4F2EAAD33FC10634EB8C79B | 28 | jdg\judge-pmp-cyclic-k02-START.txt |
| DC50D1D1D6515F15897B006B99B51C91314999E15AF60609337869FDAE629054 | 28 | jdg\judge-pmp-cyclic-k02-use-shift-START.txt |
| 1DCA4BFFAA1E27274769806827DB7ED675C18ED035C7237A1BD605D979969795 | 137 | jdg\judge-pmp-cyclic-k02-use-shift-v1.txt |
| 652DA4A2FF7E53C6B3D1D15AA444959BB0DE26A08E78E1655AB6213962D62810 | 132 | jdg\judge-pmp-cyclic-k02-v1.txt |
| 4138CCAF9EC079E2CFB28C3D0876A7635BD42DB565A7CCE42E9A3B1D25BC3A48 | 28 | jdg\judge-racket-cyclic-k02-START.txt |
| 52B44FBEC17E4D6DDFE9ACC3E497F2D6E4AB826723722868E41B101159D878A9 | 28 | jdg\judge-racket-cyclic-k02-use-shift-START.txt |
| F33E08B66DCFBE2FB30DCEF8AD8D5157291BC1CD8F749394C987CD9A86BD89C9 | 42 | jdg\judge-racket-cyclic-k02-use-shift-v1.txt |
| 2FAD9F82ED5FC6F5CD728F490EE2871061008089BED41383893DFEC27FF42CDF | 72 | jdg\judge-racket-cyclic-k02-v1.txt |
| 7018D9AD6596649937004318FB2D88BF488263370479CA8F12798E228D116400 | 9 | launch.start.txt |
| 69DBB762E214159702006EE158BC9683DE17AAD22E4FF387FFB51922B0A26F12 | 1602 | ORDER.md |
| E3B0C44298FC1C149AFBF4C8996FB92427AE41E4649B934CA495991B7852B855 | 0 | sha256-lines-v1.txt |
| 400E2507EEB0AC79357A5514EA89284F2A3EADDFE32C182324385F4006DF219B | 85557 | sha256-lines-v1.txt.paths.txt |
| 67ABD80E349EE79AE6A63E63DD6CB628A6F27D6C411B00142DAF70919DED12B3 | 82670 | sha256-lines-v2.txt |
| DBD83D9435F30DE5AA7169F47375FE5770F74DF9B62FD2F7376EBD772D335940 | 2609 | stats-v1.rkt |
| A2CF4080360130D59C7FC423AC259CD1CEA93F416384A56EAF6252D73FE0A707 | 557 | STATUS-1916.txt |
| 176001DBADB9E0DCBCBD93AE1C31FBDDF3CD8669FA0AB5B81BB7DA020EA7710B | 925 | STATUS-2021.txt |
| 8D063D578B593A71C5487EE1A5C1567452FA617B41F6125CA338156E20CE2DA1 | 929 | STATUS-2032.txt |
| FE002964267AE8259D948C765D54CA83ADC521BDB9E9C893B221BD78F62E7EAF | 4348 | manifest-sha256-v1.txt |
| 78F67EBB9B44D0D710B56B5835574C5DCEAA70CACF1AE1BF2440BE73BF08CE21 | 7185 | HANDOFF-L7-v2.md |

`RESULTS.md` and `STATUS.txt` are hashed in a later closure file. This file does not contain its own sha256.
