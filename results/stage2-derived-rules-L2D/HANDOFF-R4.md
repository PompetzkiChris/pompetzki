# Lane L2D handoff R4, written 20:30 (`date`), 2026-10-09

Lane folder: C:\ClaudeOutput\pompetzki\lanes\L2D. Session 1770f836-4cf0-4b24-a0d0-d2d9cf4a4b94.
After the 19:30 outage no L2D process was alive (checked 20:18). Interrupted files are kept as they are:
queue\runs\farkas_out_f3-2d.jdg.txt and queue\runs\farkas_out_f2-2d.jdg.txt (both 0 bytes, no verdict).
Runs restarted once, into r4\.

## Judges (every verdict below comes from both)
- pmp: C:\ClaudeOutput\pompetzki\pompetzki.exe judge-v3.pmp FILE, run from C:\ClaudeOutput\pompetzki\judge\.
- Racket: "C:\Program Files\Racket\racket.exe" racket\judge.rkt FILE.
- SHA-256: r4\judges-sha256-r4.txt
  - judge-v3.pmp bf147194…6ce7
  - judge.rkt d6cf694c…79ca
  - pompetzki.exe ccf83592…3bec
- Driver: racket lrat-v4.rkt judge FILE... -- RUN.txt. It runs both judges and writes one row per file: verdict, exit code, milliseconds, full one-line output.
- ACCEPT means exit 0. REJECT means exit 1 with "REJECT" in the output.
- A row "pmp OTHER exit -1" is a process I stopped. It is not a verdict, and it is not a LIMIT.

## Hashes
- Sources: r4\sources-sha256-r4.txt
- Inputs (certificates, CNF, LRAT, including AG5, L8A and G2 inputs): r4\inputs-sha256-r4.txt
- Emitted JDG1 files: r4\outputs-sha256-r4.txt
- Registry of every file: the first 677 entries of replay-all.jdg (AX0 ++ DEF0 of RpInit.v), checked against RpInit.v per file; see the "registry: OK" line in each *.manifest.txt.
- Every theorem has hypotheses [] and every final statement is closed.

## Accepted by both judges, with receipts
| family | files (ACCEPT pmp exit 0 and Racket exit 0) | receipt |
|---|---|---|
| LRAT | lrat\out4\: php3-2, php4-3, php5-4, rand10-60, rand14-80, rand20-120 | lrat\judge-run-2-A.txt, -B.txt, -C.txt |
| Smith | certs\out2\: smith-2x2, smith-2x3, smith-3x3 | certs\judge-run-1-G1.txt |
| Smith (L8A input) | r4\out\l8a-smith.jdg (L8A consumer_sample_smith.sexp, 4x4, D = diag(1,1,1,55)) | r4\judge-l8a-r4.txt |
| rank | certs\out2\: rank-3x3, rank-3x4; certs\out3\: rank-2x3, rank-4x4, rank-2x2 (full rank) | certs\judge-run-1-G2.txt, certs\judge-run-2.txt |
| rank (L8A input) | r4\out\l8a-rank.jdg (L8A consumer_sample_rank.sexp, 6x6, rank 4) | r4\judge-l8a-r4.txt |
| Pratt checks | certs\out2\: pratt-7, pratt-13, pratt-23 | certs\judge-run-1-G2.txt, certs\judge-run-1-G3.txt |
| Farkas | farkas\out\: f1-1d, f4-2d | farkas\judge-run-1-FA.txt |
| arithmetic kernel | kernel-test\kernel-all-1.jdg (70 theorems, 2,331 steps) | kernel-test\kernel-all-1.judge.txt (pmp 36.9 s, Racket 0.5 s) |

Mutant (corrupt derivation or corrupt statement) receipts, from the same run files:
- LRAT: 78 mutants, all REJECT by both.
- Smith, rank, Pratt: 103 mutants, all REJECT by both.
- Farkas f1/f4: 5 mutants, all REJECT by both.
- L8A: 5 mutants, all REJECT by both.
- r4\judge-mut-r4.txt: 3 more Farkas mutants REJECT by both.
- In every one of these REJECTs, both judges name the same theorem and step (tools\results-v5.rkt counts it).

Certificate-level negatives come from the emitter's exact check before any derivation is written:
- certs-v3.rkt refuses a certificate when U A V ≠ D, the matrix is not unimodular, D is not diagonal or not divisible, the minor is singular, or A K ≠ 0.
- farkas-v3.rkt refuses y with a negative entry, yᵀA ≠ 0 or yᵀb ≥ 0.
- lrat-v4.rkt refuses an unknown or satisfied hint, a non-unit hint, or a proof that never reaches the empty clause.
- These are refusals by the untrusted emitter, not judge verdicts.

## Running at 20:30 (results go to these files; verdicts are not in yet)
- r4\judge-f3-r4.txt (Farkas f3-2d, 18 MB) and r4\judge-f2-r4.txt (Farkas f2-2d, 18 MB): started 20:18.
- r4\judge-g2-r4.txt: G2 corpus cyclic-k02 through farkas-v3.rkt, 10.8 MB, with 3 mutants.
- r4\judge-ag5-r4.txt: AG5 cadical LRAT for php-5-4, tseitin-petersen, tseitin-k33, rand3-v20-s201, tseitin-cube through lrat-v4.rkt (deletion lines skipped), with 3 LRAT-specific mutants each. All five already pass the copy of the checker.

## What each theorem states (details: tools\RESULTS-template-v2.md)
- LRAT:
  - [S] for S = all x1<2 … all xn<2 not (C1 and … and Cm), in sigma1's bounded-sentence language and translation, the conjunction balanced.
  - One T step per LRAT hint; RUP only.
- Smith, rank, Pratt:
  - forall w p g o (Om(w) & Pr(p,w,w) & CapS(g,p,w) & Emp(o) → E_1 & … & E_M).
  - Each E_i is an exact integer identity Σ ±a_k b_k = c, a product a·b = c, a sum a + b = c, or n ≠ 0, over binary numerals Bin_n.
  - Addition Ad and multiplication Mu are defined from the replay's recursion theorem (replay 95).
- Farkas: forall w p g o (Ctx → forall coefficient numerals (Bin → forall u v w' ∈ ω (w' ≠ 0 → not (Row_1 & … & Row_m))))). This states that A x ≤ b has no rational solution, with x = (u − v)/w'.

## Open (exact items)
1. **Pratt.** "p is prime" is not derived. The files derive the certificate's arithmetic checks only.
   - Missing ZF lemmas: Lucas' theorem (or Pocklington's) on ω, with divisibility, congruence, order of an element, and Fermat's little theorem.
   - L8A's 64-bit sample (pratt 18446744073709551557) is not emitted. A 64-bit Bin numeral nests about 320 levels, beyond pmp's limit (about 240 levels; MAXRET 256 in pompetzki.asm). One 10-bit multiplication check already costs 11,456 steps and 14 MB.
2. **Farkas f3-2d, f2-2d, G2 cyclic-k02.** pmp verdicts pending; see "Running".
3. **Not judged by pmp:** the f2-2d and f3-2d mutants, the remaining f1-1d and f4-2d mutants, six rand20-120 mutants, and the rest of the l8a-smith mutants. f1-1d-neg-final has no pmp verdict: I stopped that process at 20:28.
4. **Non-discriminating mutant.** r4\g2\cyclic-k02-mut\cyclic-k02-main-mid-taut-drop.jdg is still a valid derivation (the dropped premise was unused). The copy of the checker ACCEPTs it. It is not counted as a negative.
5. **Two definitions not bridged.** No equivalence lemma between Ad/Mu (recursion theorem) and sigma1's Add/Mul (finite functions). The arithmetic statements use Ad/Mu.
6. **LRAT RAT steps** are refused by lrat-v4.rkt.
7. **G1 Pratt corpus** (lanes\G1-pratt) not consumed: no certificate file found there at 20:25, only generators.
8. **Size.** CNFs need n ≤ 20 variables (statement depth 199 at n = 20). Numeral entries were kept below 2^7 in the certificates emitted by L2D; the L8A Smith input reaches 55.

## Commands
- racket lrat-v4.rkt emit CNF LRAT OUT.jdg
- racket certs-v3.rkt emit CERT.sexp OUT.jdg
- racket farkas-v3.rkt emit CERT.sexp OUT.jdg
- racket lrat-v4.rkt judge FILE... -- RUN.txt
