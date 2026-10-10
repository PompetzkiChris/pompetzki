# Stage 6 (lane L6): Lean 4 / Mathlib statements as ZF theorems over ω — results, 2026-10-09

Written 18:36 (`date`). Design: `DESIGN.md`.

## Result

- **`out\L6-nat.jdg`: ACCEPT, exit 0, from both judges.** Both were run from `C:\ClaudeOutput\pompetzki\judge\`:
  - `pompetzki.exe judge-v3.pmp`: ACCEPT, exit 0, 850.1 s, output `677 345 37714 1022`.
  - `racket\judge.rkt`: ACCEPT, exit 0, 3.3 s, output `registry 677 theorems 345 steps 37714 final-registry 1022`.
- **252 statements from the environment of `import Mathlib` are closed ZF theorems in that file, each under its Lean name.**
  - 9 are declared in Mathlib's own modules:
    - `LT.lt.nat_succ_le`, `Nat.succ_pos'`, `Nat.of_le_succ`, `Nat.two_le_iff`, `Nat.two_lt_of_ne` (Mathlib.Data.Nat.Init)
    - `Nat.le_succ_iff_eq_or_le` (Mathlib.Data.Nat.SuccPred)
    - `Mathlib.Tactic.Ring.add_pos_left`, `Mathlib.Tactic.Ring.add_pos_right` (Mathlib.Tactic.Ring.Common)
    - `Pell.asq_pos` (Mathlib.NumberTheory.PellMatiyasevic)
  - 243 are declared in Lean's core library, which Mathlib imports and uses as its ℕ API: Init.Data.Nat.Basic 156, Init.Data.Nat.Lemmas 51, Init.Prelude 25, Init.Grind.Offset 5, Init.Omega.Int 2, Init.Data.Nat.Mod 2, Init.Core 2.
  - List with registry index, module and statement: `out\STATEMENTS.md`. Index with the ZF formula of every theorem: `out\L6-nat.index.txt`.
- **All 10 mutated copies: REJECT, exit 1, from both judges.** In every case both judges name the same theorem and step.
- **Registry:** 677 entries, equal entry for entry to AX0 (7) ++ DEF0 (670) of `RpInit.v`. Checked with `sigma1.rkt check-registry` (`out\check-registry.txt`); no entry carries hypotheses.
- **Hypotheses:** every theorem claims `[]`. By `Replay3.check_batch_ok` and `RpInitOk.REG0_ok` (as in `sigma1\RESULTS.md`), each accepted statement S has `prov Gam (tof S)`, where Gam is ZFC with the registered definitions.

## The file

| | |
|---|---|
| file | `out\L6-nat.jdg`, 14,399,840 bytes, sha256 `a9894a405c97705d8016f63082d22a5604c89e379f51dd84ee2c00e414b1f1ac` |
| theorems | 345: 71 prelude (theorems of Theorem 29's replay, with dependencies, checked again), 22 lemmas, 252 Lean/Mathlib statements |
| steps | 37,714 (1,822 of them in the prelude) |
| steps by kind | T 16,897 · U 7,149 · S 3,930 · Z 2,925 · L 2,583 · E 1,484 · V 1,360 · H 706 · Y 437 · G 222 · M 21 (`out\step-kinds.txt`) |
| tautology tests | largest 1,199 calls of taut_bf; 281,148 in all (copy of the checker) |
| proofs by induction on ω | 14: `Nat.zero_add`, `Nat.succ_add`, `Nat.add_comm`, `Nat.add_assoc`, `Nat.zero_mul`, `Nat.succ_mul`, `Nat.mul_comm`, `Nat.left_distrib`, `Nat.mul_assoc`, `Nat.le_add_right`, `Nat.add_left_cancel`, `Nat.add_lt_add_iff_left`, `Nat.mul_le_mul_left`, `Nat.mul_lt_mul_of_pos_left` |

The 22 lemmas (zfnat.rkt and engine.rkt):
- `(Uq k)`, `(Graph k)`, `(Rec k)`, `(FinOfRec k)`, `(Tot k)`, `(Zero k)`, `(Step k)` for k = add, mul: the theory of sigma1's Add and Mul on ω (DESIGN.md §5).
- `(NumEx n)`, `(NumUq n)` for n = 0, 1, 2 (sigma1.rkt's numerals).
- `SucIn`, `SucMem`.

The 71 prelude theorems are the replay theorems the derivations use, with their dependencies. Among them:
- L:IndLem, L:RecThm, L:OmTr, L:SucUq, L:SucInj, L:SucNe, L:NoSelf, L:NoTwo, L:EmpNo, L:EmpUq, L:ZeroW, L:SucW, L:PrEx, L:PrMem, L:MemApp;
- H:NatW, H:OrdT3, H:OrdTr, H:OmOrd0, H:SucEx, H:EmpEx, H:SubE;
- K:OmEx;
- Z:EqSym, Z:EqTr, Z:OprEx, Z:Kur1, Z:Kur2, Z:FncApp, Z:RngApp, Z:TotApp.

## Judge results (`out\judge-run.txt`; run 18:20:59 to 18:35:54, at most 4 judge processes at a time)

| file | pmp | pmp time | Racket | Racket time | where both judges stop |
|---|---|---:|---|---:|---|
| L6-nat.jdg | ACCEPT, exit 0 | 850.1 s | ACCEPT, exit 0 | 3.3 s | — (345 theorems, 37,714 steps) |
| mut/L6-nat-neg-final | REJECT, exit 1 | 882.1 s | REJECT, exit 1 | 4.2 s | theorem 344 step 215: the last line is not the statement |
| mut/L6-nat-swap-final | REJECT, exit 1 | 881.8 s | REJECT, exit 1 | 3.8 s | theorem 344 step 215: the last line is not the statement |
| mut/L6-nat-drop-step | REJECT, exit 1 | 850.2 s | REJECT, exit 1 | 3.6 s | theorem 344 step 214: the last line is not the statement |
| mut/L6-nat-taut-goal | REJECT, exit 1 | 2.6 s | REJECT, exit 1 | 0.5 s | theorem 30 step 0: taut: not a tautology |
| mut/L6-nat-use-shift | REJECT, exit 1 | 3.4 s | REJECT, exit 1 | 0.6 s | theorem 30 step 100: taut: not a tautology |
| mut/L6-nat-leib-swap | REJECT, exit 1 | 3.1 s | REJECT, exit 1 | 0.6 s | theorem 30 step 16: leib: not Leibniz's law |
| mut/L6-nat-exi-witness | REJECT, exit 1 | 3.5 s | REJECT, exit 1 | 0.6 s | theorem 30 step 58: exi: not an existential introduction |
| mut/L6-nat-exel-var | REJECT, exit 1 | 3.1 s | REJECT, exit 1 | 0.7 s | theorem 30 step 23: exel: side conditions fail |
| mut/L6-nat-sep-instance | REJECT, exit 1 | 4.1 s | REJECT, exit 1 | 0.7 s | theorem 30 step 3: ax: not an axiom shape (the Separation instance negated) |
| mut/L6-nat-registry-suc | REJECT, exit 1 | 1.8 s | REJECT, exit 1 | 0.7 s | theorem 1 step 7: taut: not a tautology (definition of Suc altered in the registry) |

- The mutations:
  - Theorem 344 is `Nat.mul_self_inj`, the last statement.
    - `neg-final` negates its statement.
    - `swap-final` gives it the statement of theorem 343.
    - `drop-step` removes its last step.
  - Theorem 30 is the first theorem after the prelude, `(Graph add)`.
- The generator's copy of the checker agrees on all 11 files (`out\manifest.txt`).

## Times (`date` and the run logs)

| what | start | end | duration |
|---|---|---|---|
| Lean export (`lean\L6Export.lean`, one Lean process under `abschluss-verify\lean.lock`, owner L6) | 17:36:24 | 17:37:30 | 66 s |
| emit (`racket lean2zf.rkt emit out`) | 18:19:14 | 18:20:41 | 87 s; derivations 13.8 s, the rest is mutants and checker copies |
| both judges, 11 files | 18:20:59 | 18:35:54 | 14 min 55 s |

## From Lean to the judge (numbers per stage)

- **Lean.**
  - 476,096 theorems in the environment of `import Mathlib` (v4.28.0, Lean v4.28.0).
  - 381 of them use only the constants of the slice: ℕ, = ≠ ≤ < ≥ >, + *, succ, numerals, and the connectives. They are in `lean\export-nat.sexp`.
- **Statement translation** (`leanstmt.rkt`; full list in `notes\translate-all.txt`):
  - 336 of the 381 are first-order over ℕ.
  - 45 are refused: 26 quantify over predicates ℕ → Prop (induction principles), 18 use `=` between propositions, 1 uses `False`.
- **Derivation.**
  - 252 statements have scripts in `scripts.rkt`, and all 252 derive. `out\scripts-run.txt` has steps and milliseconds per statement.
  - The other 84 translated statements have no script yet. Most of them are:
    - existential conclusions (`Nat.exists_eq_add_of_le`, `Nat.even_or_odd'`);
    - linear arithmetic with constant factors (the 10 `Ordnode.Valid'` lemmas);
    - parity (`Nat.two_mul_ne_two_mul_add_one`).

## What the theorems say

- The ZF statement of each Lean statement is its translation by the table of DESIGN.md §4.
- That table is sigma1.rkt's `tr`, unchanged, plus `∀x:ℕ ↦ ∀x (Nat(x) → …)`.
- Example: `Nat.add_zero`, ∀n:ℕ, n + 0 = n, is registry entry 754:
  ∀x0 (Nat(x0) → ∃x1 (Emp(x1) ∧ ∃x2 (Add(x0,x1,x2) ∧ x2 = x0))), with Add written out as sigma1's formula.
- So these theorems use the same Add and Mul as Stage 2's files. The defining equations of Lean's `Nat.add` and `Nat.mul` are in the batch as `Nat.add_zero`, `Nat.add_succ`, `Nat.mul_zero` and `Nat.mul_succ`.

## Not done in this slice

- **Proof terms.** Lean's proof terms are not translated. Only the statement comes from Mathlib; the derivation is made by `engine.rkt` from hints. The plan for proof terms is DESIGN.md §6.
- **The translation table is not checked by the judge.** Evidence for it inside the batch:
  - the recursion equations of + and *;
  - the constructors of ≤ (`Nat.le_refl`, `Nat.le_step`).
  - The minimality of ≤ (the least relation closed under refl and step) is not derived.
- **Int.** Designed (DESIGN.md §2), not built.
- **Universes beyond ℕ.** None used. Hypothesis entries for inaccessibles are designed, not built.
- **Size.**
  - Every line repeats the assumptions it needs, and those hold the full Add/Mul formulas.
  - A first build with the whole context in every line was 31.3 MB for the same 252 statements (dev run 2). The minimal-context layer brought it to 14.4 MB.
  - A pmp run on an earlier 27.7 MB build (218 statements) was stopped by me after 8 min 43 s without a verdict: `notes\dev\run1-pmp-STOPPED.txt`.

## Files

| file | what |
|---|---|
| `lean\L6Export.lean`, `lean\export-nat.sexp`, `lean\export-run.*` | the Lean side and its output |
| `leanstmt.rkt` | Lean `Expr` into the statement language |
| `zfcore.rkt` | lines 23–353 of `sigma1\sigma1.rkt` copied verbatim (formulas, checker copy, JDG1 reader/writer) |
| `zfbatch.rkt` | registry, prelude import by replay name, theorem stack, context layer with minimal contexts, induction on ω |
| `zfnat.rkt` | Add and Mul on ω (DESIGN.md §5) |
| `engine.rkt` | translation, numerals, values, bridges, congruence closure, case splits, induction driver |
| `scripts.rkt` | the 252 scripts |
| `lean2zf.rkt` | emit and judge commands |
| `tools\judge-par.rkt` | both judges, at most 4 processes |
| `out\` | the batch, index, STATEMENTS.md, manifest, mutants, judge results |
| `notes\` | development runs and listings (replay theorem names, registry, translations) |

- sha256 of the sources used for `out\`: `out\sources-sha256.txt`. Three of them:
  - zfcore.rkt `34423126…eb343f`
  - engine.rkt `53ca6df0…5cbb6a`
  - scripts.rkt `20f2af1e…d2471a`
- All source files were last written before the emit started (18:19:14).

## Reproduce

```
cd C:\ClaudeOutput\pompetzki\lanes\L6
racket lean2zf.rkt emit DIR                  (DIR new; the result equals out\L6-nat.jdg byte for byte)
racket tools\judge-par.rkt DIR DIR\judge.txt
```
