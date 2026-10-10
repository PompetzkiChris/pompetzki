# Lane L2D handoff R4 FINAL, written 20:45 (`date`), 2026-10-09

This supersedes HANDOFF-R4.md (20:30) where they differ. HANDOFF-R4.md stays as written; its hash lists are r4\sources-sha256-r4.txt, r4\inputs-sha256-r4.txt, r4\outputs-sha256-r4.txt and r4\judges-sha256-r4.txt.

## Verdicts added since 20:30
- **AG5 LRAT (cadical CNF/LRAT, deletion lines skipped) via lrat-v4.rkt.** Receipt r4\judge-ag5-r4.txt, both judges ACCEPT exit 0:
  - r4\ag5\php-5-4.jdg (pmp 62.9 s);
  - rand3-v20-s201 (299.5 s);
  - tseitin-cube (32.5 s);
  - tseitin-k33 (17.3 s);
  - tseitin-petersen (65.0 s).
  - Their LRAT-specific mutants are REJECT exit 1 by both judges as far as the run had reached at 20:45. The run continues and appends to that file.
- **G2 corpus cyclic-k02 via farkas-v3.rkt.** r4\g2\cyclic-k02.jdg: ACCEPT exit 0 by both judges (pmp 888.9 s, Racket 2.4 s). Three mutants: REJECT exit 1 by both. Receipt r4\judge-g2-r4.txt.
- **L8A inputs.** Receipt r4\judge-l8a-r4.txt.
  - r4\out\l8a-rank.jdg: ACCEPT by both (pmp 25.1 s).
  - r4\out\l8a-smith.jdg: ACCEPT by both (pmp 339.0 s).
  - 13 mutants: REJECT by both.
- **Farkas f3-2d and f2-2d.** Receipts r4\judge-f3-r4.txt and r4\judge-f2-r4.txt.
  - pmp: "LIMIT a memory block is full", exit 1. f3 stops at theorem 105, step 1357, after 1369.7 s; f2 at theorem 130, step 1317, after 1398.4 s.
  - Racket: ACCEPT exit 0.
  - These are resource stops of the pmp interpreter (bound 2 of lanes\FINDINGS-pmp-interpreter-bounds-20261009.md), not REJECTs and not ACCEPTs. f3-2d and f2-2d therefore do not count as accepted by both judges.

## Accepted by both judges (release list)
- **LRAT (11):**
  - lrat\out4\: php3-2, php4-3, php5-4, rand10-60, rand14-80, rand20-120;
  - r4\ag5\: php-5-4, rand3-v20-s201, tseitin-cube, tseitin-k33, tseitin-petersen.
- **Smith (4):**
  - certs\out2\: smith-2x2, smith-2x3, smith-3x3;
  - r4\out\: l8a-smith.
- **Rank over Q (6):**
  - certs\out2\: rank-3x3, rank-3x4;
  - certs\out3\: rank-2x3, rank-4x4, rank-2x2;
  - r4\out\: l8a-rank.
- **Pratt arithmetic checks (3):** certs\out2\: pratt-7, pratt-13, pratt-23.
- **Farkas (3):**
  - farkas\out\: f1-1d, f4-2d;
  - r4\g2\: cyclic-k02.
- **Arithmetic kernel (1):** kernel-test\kernel-all-1.jdg.
- **Receipts:** lrat\judge-run-2-A/B/C.txt, certs\judge-run-1-G1/G2/G3.txt, certs\judge-run-2.txt, farkas\judge-run-1-FA.txt, kernel-test\kernel-all-1.judge.txt, r4\judge-*-r4.txt.
- **Mutants:** every mutant with a pmp verdict is REJECT exit 1 by both judges, at the same theorem and step, with one exception, below.

## Rows that are not verdicts
- **r4\judge-mut-r4.txt.** The row for farkas\out\f1-1d-mut\f1-1d-neg-final.jdg reads "pmp OTHER exit -1". That is my stop of the process at 20:28. That run was stopped for good at 20:41; its other rows are real verdicts.
- **queue\runs\farkas_out_f3-2d.jdg.txt and farkas_out_f2-2d.jdg.txt.** 0 bytes, interrupted by the 19:30 outage. Kept as they are.

## Open (exact items)
1. **Pratt primality (not derived).** Lucas' theorem (or Pocklington's) in ZF on ω, with divisibility, congruence, multiplicative order and Fermat's little theorem. The Pratt files state the certificate's arithmetic checks, not "p is prime".
2. **L8A 64-bit Pratt sample (consumer_sample_pratt.sexp, p = 18446744073709551557): not emitted.** Its Bin numerals nest about 320 levels, beyond pmp's recursion bound (MAXRET 256, about 240 levels).
3. **Farkas f3-2d, f2-2d: no ACCEPT from pmp** (memory-block LIMIT). Either pmp's memory blocks grow, or the main Farkas theorem is split into lemmas with smaller lines (not done).
4. **Mutants not judged by pmp:**
   - all mutants of f2-2d and f3-2d;
   - f1-1d: exel-var, exi-witness and leib-swap were judged in farkas\judge-run-1-FA.txt; neg-final has no pmp verdict;
   - f4-2d: all mutants;
   - lrat\out4\rand20-120-mut: neg-final, registry-suc, rup-goal-neg, taut-goal, twin-final, use-shift;
   - the l8a-smith mutants other than taut-goal, registry-suc and cert-use-swap.
   - Racket rejects all of them; the copy of the checker in each emitter rejects all of them as well.
5. **Non-discriminating mutant.** r4\g2\cyclic-k02-mut\cyclic-k02-main-mid-taut-drop.jdg is a valid derivation (the dropped premise was unused). The copy of the checker accepts it; it is not a negative.
6. **No bridge between the two definitions of + and ·.** No ZF lemma relates Ad/Mu (from replay 95) to sigma1's Add/Mul.
7. **LRAT RAT steps** are refused by lrat-v4.rkt. Instances need at most 20 variables (statement depth 199 at n = 20).
8. **G1 Pratt corpus** not consumed: no certificate files in lanes\G1-pratt at 20:25.
