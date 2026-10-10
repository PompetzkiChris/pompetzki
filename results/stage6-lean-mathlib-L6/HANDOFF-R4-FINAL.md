# Lane L6 handoff R4 FINAL, written 21:02 (`date`)

This file corrects and completes HANDOFF-R4.md (20:26). Everything listed under "Release" has complete terminal receipts with exit codes. Lane folder: `C:\ClaudeOutput\pompetzki\lanes\L6`.

## Corrections to HANDOFF-R4.md

- §4 commands:
  - `emit2.rkt` started 19:25:04 (`r2\out\files-emit.start.txt`); its last output was written at 19:30.
  - The first judge run (`judge-par.rkt`) started 20:19:52.
- That first judge run was stopped at about 20:30 by this session's background-task time limit, not by a judge. Its four pmp processes ended at 598.4 s with exit 1 and printed no verdict. Note: `r2\out\judge-r4-STOPPED.txt`.
- All verdicts below come from the rerun, one command per file, started 20:30.

## Release

Judges, both run from `C:\ClaudeOutput\pompetzki\judge\`:
- `..\pompetzki.exe judge-v3.pmp FILE`
- `"C:\Program Files\Racket\racket.exe" racket\judge.rkt FILE`

| file (lane-relative) | sha256 | pmp (receipt, times) | Racket (receipt `r2\out\r4-racket.txt`) |
|---|---|---|---|
| out\L6-nat.jdg (round 1) | a9894a405c97705d8016f63082d22a5604c89e379f51dd84ee2c00e414b1f1ac | ACCEPT exit 0, 850,090 ms (`out\judge-run.txt`, 18:20:59–18:35:54) | ACCEPT exit 0, 3,317 ms; 345 theorems, 37,714 steps, registry 677→1022 |
| r2\out\files\L6-pt.jdg | ac411929df10d79528ea3542c48558f8fb5541d587efa3c152359a510e517dcd | ACCEPT exit 0, 20:30:20–20:41:10 (`r2\out\r4-pmp-L6-pt.txt`); 286 theorems, 30,735 steps, 677→963 | ACCEPT exit 0, 2,532 ms |
| r2\out\files\L6-int-1.jdg | a65622f51d7e92870d3962675a21e857af1a6be6f020bab5add8bc604dfd6b1b | ACCEPT exit 0, 20:30:22–20:43:20; 254 theorems, 27,452 steps, 677→931 | ACCEPT exit 0, 2,620 ms |
| r2\out\files\L6-int-2.jdg | 971c76497220f705afa1163e508c5fcadfe7e646f914adcb08d23296b95696b5 | ACCEPT exit 0, 20:30:24–20:46:57; 161 theorems, 18,462 steps, 677→838 | ACCEPT exit 0, 2,772 ms |
| r2\out\files\L6-int-3.jdg | ee8cd8a55fbf719a63f24ec16c3135315fc583c68bd81de0fac20dc0c9cca5f6 | ACCEPT exit 0, 20:30:26–20:48:32; 157 theorems, 18,509 steps, 677→834 | ACCEPT exit 0, 3,088 ms |
| r2\out\files\L6-int-4.jdg | cc971243ad4cf7409d52b10e80cc704619397ca5590c87c210e94287b96322b7 | ACCEPT exit 0, 20:41:22–21:01:36; 139 theorems, 16,001 steps, 677→816 | ACCEPT exit 0, 3,320 ms |

Every final registry is ≤ 1,091 and every numeral is ≤ 2, so none of these runs is near a pmp resource bound. No run produced a LIMIT.

### Mutants

- **Round 1:** 10 mutants in `out\mut\`, REJECT exit 1 from both judges (`out\judge-run.txt`).
- **Round 2:** 28 mutants in `r2\out\files\mut\`, REJECT exit 1 from both judges. In every case both judges name the same theorem and step.
  - Racket judge: all 28 (`r2\out\r4-racket.txt`, 20:43:32–20:44:13).
  - pmp:
    - 25 early-failing mutants (`r2\out\r4-pmp-mutants.txt`, 20:44:19–20:45:06);
    - `L6-pt-neg-final` (theorem 285 step 82, 20:45:11–20:52:30);
    - `L6-pt-swap-final` (285/82, 20:48:41–20:55:14);
    - `L6-pt-drop-step` (285/81, 20:48:43–20:55:16).

### Receipts (sha256)

| file | sha256 |
|---|---|
| r4-pmp-L6-pt.txt | b4dbdb9af9c44583fd64d7e49f13a4ed0f3c1a354bcd213df51b99e1f558946d |
| r4-pmp-L6-int-1.txt | 23491909d73f99a44c52edb04eb2c081682b7bf58862974c24224f8f0244e33a |
| r4-pmp-L6-int-2.txt | 4585bcfe9c9fec3679fb9199e3fe39b348468b7087344eef810d26fb53a1dc3e |
| r4-pmp-L6-int-3.txt | ff33e123a97b53bd77c2db5458b2364f91efe9bcb462e3e3ccb541326010be69 |
| r4-pmp-L6-int-4.txt | f592cf096b30221f674ce722d4aa8cba5369a0b2f64613961be56c5c260d38a2 |
| r4-pmp-mutants.txt | 92b61c3d58c75494f0591ffc1c54ef81abe98755ca02dd7457a9530ed73742f9 |
| r4-pmp-L6-pt-neg-final.txt | 5138c3cedc5e15a3ceb58ea828c1df1192054b4a07406c0e23b519f329ef8f56 |
| r4-pmp-L6-pt-swap-final.txt | b8821bdb10697a30112159c854945aed4bc600e365915012baac81e762dfedff |
| r4-pmp-L6-pt-drop-step.txt | 465a3e76bca1cd5681ad10e5d9111bd6621789532fc6246aba9929069548a26d |
| r4-racket.txt | 2bc3c3cad877a4c66af4ee2d27d88081474dd2e8e676c102c76d3eb650b89156 |

All of these are in `r2\out\`.

### Indexes and lists (sha256)

| file | sha256 |
|---|---|
| files\L6-pt.index.txt | c953ba4a10f2d7ea1c62d4a4b5496bad8902cf4a456641a9da73e80e6fbe0312 |
| files\L6-int-1.index.txt | c445555e8d44d5834ae59d34e6bd1c579920e4b96e09d4bf84bcd1155398c815 |
| files\L6-int-2.index.txt | 1be00a7457f632c9b2e5897154103aadc93ca41609d4263ed458bdf1542e0c0d |
| files\L6-int-3.index.txt | 6362cc8a682e1d360b25e8631b3120080e769d2ef64a004c8ec0977fe692c2bb |
| files\L6-int-4.index.txt | 8ab1af85a9c9feb310cbbed115a82ec27abb04688f0e654b636261a6f43c4ec2 |
| files\proofterm-class.tsv | 4b263b46628f05116a5d9127ca5f40911c0b0586191e0a25e1fe942df16c8c21 |
| queue-classification-r4.tsv | c5403425608587f7520c9282ebb2c90b11b723153b9f6480368ad904dfdf8137 |
| new-env-names-r2-r4.txt | d219ae5e30a1e866c8a87837ea85e7c741269175d278892d238be8d705257772 |

All of these are in `r2\out\`. Sources: §5 of HANDOFF-R4.md (round 2) and `out\sources-sha256.txt` (round 1, unchanged).

## What the release contains, by category

- **Round 1:** 252 ℕ statements of the `import Mathlib` environment (9 Mathlib, 243 Init), derived from hints.
- **ℤ:** 210 further statements of the Mathlib environment over ℤ, derived by ring normalization and cancellation over the pair encoding (DESIGN in HANDOFF-R4 §3). Names: `r2\out\new-env-names-r2-r4.txt`.
- **Proof terms:** 93 derivations that follow Lean's proof terms (class 1), keys `PT:<Lean name>` in L6-pt.jdg. Per-name status: `proofterm-class.tsv`.
- **AG2 queue**, all 7,658 declarations with the category and exact blocking construct per line (`queue-classification-r4.tsv`):

| category | count |
|---|---:|
| translated + derived | 6 |
| translated, no derivation yet | 6 |
| not translatable | 7,646 |

## Open (exact names)

1. **ZF derivation of the ℤ pair encoding's adequacy.** Not derived: ℤ as the quotient set (ℕ×ℕ)/≈, and the equivalence of a translated statement with the statement over that set.
2. **Queue declarations translated, not derived:**
   - `Int.eq_zero_or_eq_zero_of_mul_eq_zero`
   - `Int.nonneg_or_nonpos_of_mul_nonneg`
   - `Int.mul_nonneg_of_nonneg_or_nonpos`
   - `Int.mul_nonneg_iff`
   - `Nat.two_mul_ne_two_mul_add_one`
   - `Nat.not_exists_sq`
3. **Queue declarations not translatable: 7,646**, with their constructs in the TSV.
   - 5,244 of them are generic lemmas (a binder over a Sort).
   - The instantiation at ℤ/ℕ (`lean\L6Export3.lean`) was interrupted at 19:30 and not rerun.
4. **ℤ statements derived during the attempts but not in a judged file:**
   - 26 over 1.5 MB, including `Int.mul_assoc`, `Int.mul_add`, `Int.add_mul`;
   - 13 in emit groups 5–6.
5. **Translated ℤ/ℕ statements with no derivation:** 284 of the 532 attempt candidates (`r2\out\attempts\all.tsv`, status FAIL).
6. **Proof terms outside class 1:** 159 of the 252, with the reason per name in `proofterm-class.tsv`.
   - These include every proof by structural recursion (`Nat.brecOn` with private `match`), e.g. `Nat.zero_add`, `Nat.succ_add`, `Nat.add_comm`, `Nat.add_assoc`, `Nat.mul_comm`, `Nat.left_distrib`, `Nat.mul_assoc`.
   - Class 2 (`congrArg`, `Eq.mpr`, `rfl` with δι, `brecOn`) is not built.
7. **Translation table:** the minimality half of `Nat.le` is not derived.

## Interrupted files kept in place, not part of the release

- `lean\export3-run.log` (0 bytes)
- `lean\export3-run.start.txt`
- `r2\out\files\L6-int-4.rows.txt` (NUL-filled; `L6-int-4.index.txt` records the same theorems)
- `r2\out\files\manifest.txt` (ends in NUL bytes)
- `r2\out\judge-r4.console.txt`, `r2\out\judge-r4.start.txt`, `r2\out\judge-r4.end.txt` (the stopped run)
