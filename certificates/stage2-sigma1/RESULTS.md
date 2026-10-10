# Stage 2: arithmetic of ω as ZF derivations for the pmp judge — results, 2026-10-09

Written 17:25 (`date`).
- **Generator:** `sigma1.rkt` (82,114 bytes, sha256 `7d3ff29ca288d952ba7526940c3728aaa1bc202323311cb29b3409a4b4ff3337`), Racket v9.3 [cs], exact integers only.
- **Judge run:** 16:37:32 to 17:24:54 (`date`, files `judge-run-1.start.txt` / `.end.txt`); rows in `judge-run-1.txt`.

## Result

- **All 7 emitted files: ACCEPT, exit 0, from both judges:**
  - `pompetzki.exe judge-v3.pmp FILE`, run from `judge\`;
  - `racket\judge.rkt FILE`.

  Together they hold 1,656 theorems, 53,069 steps. Of the theorems, 154 are copied from the replay as prelude (counted once per file) and 1,502 are generated.
- **All 70 mutated copies: REJECT, exit 1, from both judges.** In every case both judges name the same theorem and step.
- **Registry of every file:** 677 entries, identical entry for entry to `AX0 ++ DEF0` of `forcing-src/general/RpInit.v`. The check parses the Rocq source directly, not through `rocq2jdg.rkt`. No entry carries hypotheses; the 29 placeholder hypotheses of the replay registry are left out.
- **The generator's own copy of `sstep`/`check_thm` agrees:** ACCEPT on all 7 files with the judges' counts, REJECT on all 70 mutants at the judges' theorem and step.

## What soundness gives (Replay3.v)

- `check_batch_ok`: `reg_ok reg → check_batch reg ts = true → reg_ok (reg ++ map ent ts)`.
- `reg_ok` asks of every entry `(d, h)`: `prov (AH h) (tof d)`, with `AH h` = Gam plus the placeholder hypotheses named in `h`.
- Gam (Ax.v) = the seven axioms, every Separation and Collection instance, and the definitions of Data.v (`DefAx Dall`, every renaming).
- `RpInitOk.REG0_ok` proves `reg_ok` for `REG0 = AX0 ++ DEF0 ++ hypotheses`. The registry here is its first 677 entries, a prefix. `nth_error` of a prefix agrees with `REG0`, so the prefix is `reg_ok`. This one-line step is not a separate Rocq lemma.
- Every theorem here claims hypotheses `[]`. So each accepted statement `S` satisfies `prov Gam (tof S)`: ZF with the registered definitions.
- No new definition enters a registry, because Gam fixes the definitions to `Dall`. Addition and multiplication are therefore written out as ZF formulas over the registered symbols.
- Still owed (Codex): that the bytes of `judge-v3.pmp` compute `check_batch`. Until then the pmp verdicts rest on the judge's agreement with the Racket copy and with this generator's copy.

## Definitions

Registered symbols used (Data.v, registry entries from replay-all.jdg):

| symbol | body |
|---|---|
| `Emp1(x)` (p17) | ∀d ¬ d∈x |
| `Suc2(s,y)` (p18) | ∀d (d∈s ↔ d∈y ∨ d=y) |
| `Opr3(p,a,b)` (p8) | the Kuratowski pair, through `Sng2`, `Upr3` |
| `App3(f,x,y)` (p9) | ∃d (d∈f ∧ Opr3(d,x,y)) |
| `Fnc1(f)` (p10) | ∀a b c (App3(f,a,b) ∧ App3(f,a,c) → b=c) |
| `Om1(w)` (p20) | w is inductive and contained in every inductive set |
| `Nat1(n)` (p72) | ∃w (Om1(w) ∧ n∈w) |

Formulas built from them, with no new symbols:

- **Numerals.** N₀(x) := Emp(x); N_{n+1}(x) := ∃y (N_n(y) ∧ Suc(x,y)).
- **Add(x,y,z)** := ∃f [Fnc(f) ∧ ∀o (Emp(o) → App(f,o,x)) ∧ ∀i (i∈y → ∃a App(f,i,a)) ∧ ∀i j a b (i∈y ∧ Suc(j,i) ∧ App(f,i,a) ∧ App(f,j,b) → Suc(b,a)) ∧ App(f,y,z)].
- **Mul(x,y,z)** is the same with App(f,o,o) at the empty set and Add(a,x,b) as the step.
- For x, y ∈ ω these say exactly z = x+y and z = x·y: f is the finite function i ↦ x+i (resp. i·x) on {0,…,y}.
- **Sentences.** The language: terms n, x, S t, t+u, t·u; relations =, <, ≤; connectives ¬ ∧ ∨ → ↔; bounded quantifiers ∀x<t, ∃x<t, ∀x≤t, ∃x≤t; and `some x` = ∃x ∈ ω. Translation is term by term:
  - a numeral n gives ∃u (N_n(u) ∧ K(u));
  - t+s gives ∃u (Add(a,b,u) ∧ K(u));
  - < gives ∈;
  - ∀x<t φ gives ∀x (x∈b → φ);
  - `some x φ` gives ∃x (Nat(x) ∧ φ).
- A true sentence gets [s]. A false one gets ¬[s], the translation of the true sentence ¬s.

## How each derivation is made

- **Context.** Inside a theorem, the frame variables 0..N stand for the numerals: Chain(N) = Emp(v₀) ∧ Suc(v₁,v₀) ∧ … ∧ Suc(v_N,v_{N−1}). Every line reads Chain(N) → φ.
- **Lemmas,** built on demand and reused by `U`:
  - NumEx, NumUq: v_n is N_n, and the only one.
  - In, NotIn: v_k ∈ v_n iff k < n, through Foundation (L:NoSelf, L:NoTwo).
  - Ne: v_i ≠ v_j.
  - MemChar: d ∈ v_n ↔ d = v₀ ∨ … ∨ d = v_{n−1}.
  - NatNum: v_n ∈ ω.
  - FinSet: finite sets {q₀,…,q_m} exist.
  - Fin, FinEx, FinUq: the finite function, and existence and uniqueness of Add/Mul values.
- **Chain elimination.** At the end the chain is removed by `exel` on v_N … v₁ with H:SucEx, and on v₀ with EmpEx (from the axiom of Infinity). The statement is closed.
- **Prelude.** 28 hypothesis-free theorems of Theorem 29's replay are copied with their dependencies and checked again in every file that uses them:
  - Z: EqSym, EqTr, UprEx, SngEx, SngUq, UprUq, OprEx, SngIn, SngMem, UprIn, UprMem, OprMem, UprExS, UprExT, Kur1, Kur2, FncApp, EqSymD;
  - L: NoSelf, NoTwo, SucUq, MemApp, EmpUq, ZeroW, SucW;
  - H: SucEx;
  - K: AddEx, OmEx.
- **Axioms reached by `U`.** Extensionality, Pairing, Union, Infinity, Foundation. Separation instances appear as axiom steps inside the prelude. Power Set and Choice are not used.
- **Tautology cost.** Every disjunction in a tautology step has single-atom disjuncts, so the judges' Shannon expansion stays linear. The largest tautology step needed 401 `taut_bf` calls (05).

## The files (`out\`)

| layer | statements |
|---|---|
| 01-numerals | ∃x N_n(x); ∀x∀y (N_n(x) → N_n(y) → x=y); ∀w∀x (Om(w) → N_n(x) → x∈w) — n = 0..12 |
| 02-membership | ∀x∀y (N_k(x) → N_n(y) → x∈y) for k<n, and → ¬x∈y for k≥n — k, n = 0..9 (100) |
| 03-distinct | ∀x∀y (N_n(x) → N_m(y) → ¬x=y) — n ≠ m ≤ 9 (90) |
| 04-bounded | ∀y (N_n(y) → ∀x (x∈y ↔ N₀(x) ∨ … ∨ N_{n−1}(x))) — n = 0..9; 12 bounded-quantifier sentences |
| 05-arithmetic | ∀x∀z (N_a(x) → (Suc(z,x) ↔ N_{a+1}(z))) a = 0..9; ∀x y z (N_a(x) → N_b(y) → (Add(x,y,z) ↔ N_{a+b}(z))) a+b ≤ 8 (45); the same for Mul, a, b ≤ 3 (16) |
| 06-sentences | 21 chosen and 40 random bounded sentences (exact LCG, seed 20261009): 35 true, 26 false |
| 07-sigma1 | 5 true Σ₁ sentences, witnesses found by search below 1000 |

- Each `.index.txt` lists every theorem with its key and statement. In those listings an implication whose antecedent is a conjunction prints as `(A → ¬B) ∨ C`, which reads (A ∧ B) → C.
- `manifest.txt` has sizes, sha256 and the copy-of-checker verdicts.

## Judge results

| file | theorems (prelude) | steps (prelude) | bytes | pmp | pmp time | Racket | Racket time |
|---|---:|---:|---:|---|---:|---|---:|
| 01-numerals.jdg | 73 (7) | 1679 (129) | 244938 | ACCEPT, exit 0 | 7.9 s | ACCEPT, exit 0 | 0.2 s |
| 02-membership.jdg | 226 (13) | 4168 (188) | 517549 | ACCEPT, exit 0 | 20.6 s | ACCEPT, exit 0 | 0.3 s |
| 03-distinct.jdg | 248 (10) | 4076 (146) | 496222 | ACCEPT, exit 0 | 20.1 s | ACCEPT, exit 0 | 0.2 s |
| 04-bounded.jdg | 90 (13) | 1596 (188) | 251800 | ACCEPT, exit 0 | 11.4 s | ACCEPT, exit 0 | 0.2 s |
| 05-arithmetic.jdg | 432 (24) | 20508 (366) | 3019857 | ACCEPT, exit 0 | 269.6 s | ACCEPT, exit 0 | 0.8 s |
| 06-sentences.jdg | 364 (25) | 13904 (390) | 3270867 | ACCEPT, exit 0 | 233.4 s | ACCEPT, exit 0 | 0.7 s |
| 07-sigma1.jdg | 223 (27) | 7138 (502) | 1461004 | ACCEPT, exit 0 | 141.2 s | ACCEPT, exit 0 | 0.4 s |

sums: pmp 704443 ms, Racket 3151 ms over the originals

| mutant | pmp | Racket | Racket's location | pmp's reason |
|---|---|---|---|---|
| 01-numerals-drop-step | REJECT, exit 1 | REJECT, exit 1 | theorem 72 step 81 (final: last line is not the statement) | 72 81: the last line is not the statement renamed by sig |
| 01-numerals-exel-var | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 5 (step L) | 1 5: exel: the side conditions of existential elimination fail |
| 01-numerals-exi-witness | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 3 (step E) | 1 3: exi: the formula is not an existential introduction |
| 01-numerals-leib-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 32 step 2 (step Z) | 32 2: leib: the formula is not Leibniz's law for the given formula |
| 01-numerals-mp-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 8 (step M) | 1 8: mp: the second line is not an implication |
| 01-numerals-neg-final | REJECT, exit 1 | REJECT, exit 1 | theorem 72 step 82 (final: last line is not the statement) | 72 82: the last line is not the statement renamed by sig |
| 01-numerals-registry-suc | REJECT, exit 1 | REJECT, exit 1 | theorem 6 step 23 (step T) | 6 23: taut: not a tautology |
| 01-numerals-taut-goal | REJECT, exit 1 | REJECT, exit 1 | theorem 0 step 0 (step T) | 0 0: taut: not a tautology |
| 01-numerals-twin-final | REJECT, exit 1 | REJECT, exit 1 | theorem 72 step 82 (final: last line is not the statement) | 72 82: the last line is not the statement renamed by sig |
| 01-numerals-use-shift | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 8 (step M) | 1 8: mp: the antecedent differs from the first line |
| 02-membership-drop-step | REJECT, exit 1 | REJECT, exit 1 | theorem 225 step 46 (final: last line is not the statement) | 225 46: the last line is not the statement renamed by sig |
| 02-membership-exel-var | REJECT, exit 1 | REJECT, exit 1 | theorem 10 step 5 (step L) | 10 5: exel: the side conditions of existential elimination fail |
| 02-membership-exi-witness | REJECT, exit 1 | REJECT, exit 1 | theorem 10 step 3 (step E) | 10 3: exi: the formula is not an existential introduction |
| 02-membership-leib-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 11 step 3 (step Z) | 11 3: leib: the formula is not Leibniz's law for the given formula |
| 02-membership-mp-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 10 step 8 (step M) | 10 8: mp: the second line is not an implication |
| 02-membership-neg-final | REJECT, exit 1 | REJECT, exit 1 | theorem 225 step 47 (final: last line is not the statement) | 225 47: the last line is not the statement renamed by sig |
| 02-membership-registry-suc | REJECT, exit 1 | REJECT, exit 1 | theorem 12 step 7 (step T) | 12 7: taut: not a tautology |
| 02-membership-taut-goal | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 2 (step T) | 1 2: taut: not a tautology |
| 02-membership-twin-final | REJECT, exit 1 | REJECT, exit 1 | theorem 225 step 47 (final: last line is not the statement) | 225 47: the last line is not the statement renamed by sig |
| 02-membership-use-shift | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 0 (step U) | 1 0: use: no such registry entry |
| 03-distinct-drop-step | REJECT, exit 1 | REJECT, exit 1 | theorem 247 step 46 (final: last line is not the statement) | 247 46: the last line is not the statement renamed by sig |
| 03-distinct-exel-var | REJECT, exit 1 | REJECT, exit 1 | theorem 3 step 5 (step L) | 3 5: exel: the side conditions of existential elimination fail |
| 03-distinct-exi-witness | REJECT, exit 1 | REJECT, exit 1 | theorem 15 step 3 (step E) | 15 3: exi: the formula is not an existential introduction |
| 03-distinct-leib-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 3 step 1 (step Z) | 3 1: leib: the formula is not Leibniz's law for the given formula |
| 03-distinct-mp-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 15 step 8 (step M) | 15 8: mp: the second line is not an implication |
| 03-distinct-neg-final | REJECT, exit 1 | REJECT, exit 1 | theorem 247 step 47 (final: last line is not the statement) | 247 47: the last line is not the statement renamed by sig |
| 03-distinct-registry-suc | REJECT, exit 1 | REJECT, exit 1 | theorem 2 step 7 (step T) | 2 7: taut: not a tautology |
| 03-distinct-taut-goal | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 2 (step T) | 1 2: taut: not a tautology |
| 03-distinct-twin-final | REJECT, exit 1 | REJECT, exit 1 | theorem 247 step 47 (final: last line is not the statement) | 247 47: the last line is not the statement renamed by sig |
| 03-distinct-use-shift | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 0 (step U) | 1 0: use: no such registry entry |
| 04-bounded-drop-step | REJECT, exit 1 | REJECT, exit 1 | theorem 89 step 42 (final: last line is not the statement) | 89 42: the last line is not the statement renamed by sig |
| 04-bounded-exel-var | REJECT, exit 1 | REJECT, exit 1 | theorem 3 step 5 (step L) | 3 5: exel: the side conditions of existential elimination fail |
| 04-bounded-exi-witness | REJECT, exit 1 | REJECT, exit 1 | theorem 3 step 3 (step E) | 3 3: exi: the formula is not an existential introduction |
| 04-bounded-leib-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 4 step 3 (step Z) | 4 3: leib: the formula is not Leibniz's law for the given formula |
| 04-bounded-mp-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 3 step 8 (step M) | 3 8: mp: the second line is not an implication |
| 04-bounded-neg-final | REJECT, exit 1 | REJECT, exit 1 | theorem 89 step 43 (final: last line is not the statement) | 89 43: the last line is not the statement renamed by sig |
| 04-bounded-registry-suc | REJECT, exit 1 | REJECT, exit 1 | theorem 6 step 7 (step T) | 6 7: taut: not a tautology |
| 04-bounded-taut-goal | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 2 (step T) | 1 2: taut: not a tautology |
| 04-bounded-twin-final | REJECT, exit 1 | REJECT, exit 1 | theorem 89 step 43 (final: last line is not the statement) | 89 43: the last line is not the statement renamed by sig |
| 04-bounded-use-shift | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 0 (step U) | 1 0: use: no such registry entry |
| 05-arithmetic-drop-step | REJECT, exit 1 | REJECT, exit 1 | theorem 431 step 54 (final: last line is not the statement) | 431 54: the last line is not the statement renamed by sig |
| 05-arithmetic-exel-var | REJECT, exit 1 | REJECT, exit 1 | theorem 3 step 5 (step L) | 3 5: exel: the side conditions of existential elimination fail |
| 05-arithmetic-exi-witness | REJECT, exit 1 | REJECT, exit 1 | theorem 5 step 1 (step E) | 5 1: exi: the formula is not an existential introduction |
| 05-arithmetic-leib-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 3 step 1 (step Z) | 3 1: leib: the formula is not Leibniz's law for the given formula |
| 05-arithmetic-mp-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 9 step 8 (step M) | 9 8: mp: the second line is not an implication |
| 05-arithmetic-neg-final | REJECT, exit 1 | REJECT, exit 1 | theorem 431 step 55 (final: last line is not the statement) | 431 55: the last line is not the statement renamed by sig |
| 05-arithmetic-registry-suc | REJECT, exit 1 | REJECT, exit 1 | theorem 2 step 7 (step T) | 2 7: taut: not a tautology |
| 05-arithmetic-taut-goal | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 2 (step T) | 1 2: taut: not a tautology |
| 05-arithmetic-twin-final | REJECT, exit 1 | REJECT, exit 1 | theorem 431 step 55 (final: last line is not the statement) | 431 55: the last line is not the statement renamed by sig |
| 05-arithmetic-use-shift | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 0 (step U) | 1 0: use: no such registry entry |
| 06-sentences-drop-step | REJECT, exit 1 | REJECT, exit 1 | theorem 363 step 28 (final: last line is not the statement) | 363 28: the last line is not the statement renamed by sig |
| 06-sentences-exel-var | REJECT, exit 1 | REJECT, exit 1 | theorem 47 step 46 (step L) | 47 46: exel: the side conditions of existential elimination fail |
| 06-sentences-exi-witness | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 1 (step E) | 1 1: exi: the formula is not an existential introduction |
| 06-sentences-leib-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 24 step 3 (step Z) | 24 3: leib: the formula is not Leibniz's law for the given formula |
| 06-sentences-mp-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 49 step 10 (step M) | 49 10: mp: the second line is not an implication |
| 06-sentences-neg-final | REJECT, exit 1 | REJECT, exit 1 | theorem 363 step 29 (final: last line is not the statement) | 363 29: the last line is not the statement renamed by sig |
| 06-sentences-registry-suc | REJECT, exit 1 | REJECT, exit 1 | theorem 20 step 4 (step T) | 20 4: taut: not a tautology |
| 06-sentences-taut-goal | REJECT, exit 1 | REJECT, exit 1 | theorem 0 step 0 (step T) | 0 0: taut: not a tautology |
| 06-sentences-twin-final | REJECT, exit 1 | REJECT, exit 1 | theorem 363 step 29 (final: last line is not the statement) | 363 29: the last line is not the statement renamed by sig |
| 06-sentences-use-shift | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 0 (step U) | 1 0: use: no such registry entry |
| 07-sigma1-drop-step | REJECT, exit 1 | REJECT, exit 1 | theorem 222 step 41 (final: last line is not the statement) | 222 41: the last line is not the statement renamed by sig |
| 07-sigma1-exel-var | REJECT, exit 1 | REJECT, exit 1 | theorem 71 step 57 (step L) | 71 57: exel: the side conditions of existential elimination fail |
| 07-sigma1-exi-witness | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 1 (step E) | 1 1: exi: the formula is not an existential introduction |
| 07-sigma1-leib-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 35 step 3 (step Z) | 35 3: leib: the formula is not Leibniz's law for the given formula |
| 07-sigma1-mp-swap | REJECT, exit 1 | REJECT, exit 1 | theorem 73 step 10 (step M) | 73 10: mp: the second line is not an implication |
| 07-sigma1-neg-final | REJECT, exit 1 | REJECT, exit 1 | theorem 222 step 42 (final: last line is not the statement) | 222 42: the last line is not the statement renamed by sig |
| 07-sigma1-registry-suc | REJECT, exit 1 | REJECT, exit 1 | theorem 31 step 4 (step T) | 31 4: taut: not a tautology |
| 07-sigma1-taut-goal | REJECT, exit 1 | REJECT, exit 1 | theorem 0 step 0 (step T) | 0 0: taut: not a tautology |
| 07-sigma1-twin-final | REJECT, exit 1 | REJECT, exit 1 | theorem 222 step 42 (final: last line is not the statement) | 222 42: the last line is not the statement renamed by sig |
| 07-sigma1-use-shift | REJECT, exit 1 | REJECT, exit 1 | theorem 1 step 0 (step U) | 1 0: use: no such registry entry |

counts: #hash((file/ACCEPT/ACCEPT . 7) (mutant/REJECT/REJECT . 70))

## Sentences proved (06, 07; 04 has 12 more in its index)

**Chosen (06):**
- 2+3 = 5
- ¬(2+2 = 5)
- 3·4 = 12
- 2·3 < 4+3
- S(S(1 + 2·2)) = 7
- ∀x<4 ∃y<5 S x = y
- ¬∀x<5 x<4
- ∃x≤3 x+x = 6
- ∀x≤3 x·x ≤ 9
- (3<5) ↔ ¬(5<3)
- ¬∃x<5 2x = 7
- ∀x<2+1 x² < S(2·2)
- commutativity of + on 3×3
- commutativity of · on 3×3
- ∀x<3 x·2 = x+x
- every n<6 is 0 or a successor
- every n<7 is even or odd
- 5 has only trivial factorizations below 6
- 4 has a nontrivial factorization
- ∃x<10 x² = 9
- ∀x,y<4 (x<y → x+1 < y+1)

**Random (06):** 40 sentences with up to three nested bounded quantifiers. They are listed with their truth values in `out\06-sentences.index.txt`.

**Σ₁ (07):**
- ∃x x² = 16
- ∃x∃y (1<x<y ∧ xy = 6)
- ∀n<4 ∃m n+n = m
- ∃p (4<p ∧ ∀a≤p ∀b≤p (ab = p → a = 1 ∨ b = 1)), with p = 5
- ∃x (1<x ∧ x+2 = 2x)

## Command line

`racket sigma1.rkt sentence "SEXP" OUT.jdg` derives one sentence. Five such files were written to `cli\` at 16:39. The judges have not been run on them yet.
- ∀x<6 ∃y<13 x+x = y
- ∃x<7 (2<x ∧ x² = x+12)
- ∀x,y<5 (x+y = 4 → x ≤ 4)
- ∀x<5 x² < 10, which is false and is derived as its negation
- the Σ₁ sentence ∃n (0<n ∧ n² = 2n)

## Not done in Stage 2

- **The universal theorem.** The Rocq theorem "for every true bounded sentence s, prov Gam [s]" is not proved. Each instance here is derived and checked; that is not the universal statement.
- **The derived rules.** Rank–nullity, Smith, Gröbner, Nullstellensatz, LRAT, Pratt and Farkas are not yet posted as derivations.
- **False Σ₁ sentences.** Their negations are Π₁, and a finite witness search does not derive them.
- **Defined symbols.** Statements carry the registered symbols. Elim.v's substitution removes them, but it is proved there for ⊥ only.

## Reproduce

```
racket sigma1.rkt emit DIR
racket sigma1.rkt judge DIR RESULTS.txt
racket sigma1.rkt check-registry FILE
```
