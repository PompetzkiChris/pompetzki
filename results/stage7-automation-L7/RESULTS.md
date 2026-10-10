# Lane L7, Stage 7: automation emitters for the pmp judge — results, 2026-10-09

Written 18:46 (`date`).

The emitters are untrusted programs. Each writes JDG1 files. A derivation counts only when both judges ACCEPT its file:
- `pompetzki.exe judge-v3.pmp FILE`;
- `racket\judge.rkt FILE`.

Both run from `C:\ClaudeOutput\pompetzki\judge\`.

## Result

- **Six files written, all ACCEPT, exit 0, from both judges:**
  - 1 for equality reasoning (Racket emitter);
  - 1 for equality chains (emitter written in pmp);
  - 2 for tautologies: the split file and a control file of single steps;
  - 1 for quantifiers;
  - 1 for the general laws of Add and Mul on ω.
- **The mutated copies all REJECT, exit 1, from both judges.** The counts are in the table below.
- **The general laws of ω are accepted.**
  - What is proved, for all x, y, z ∈ ω: commutativity and associativity of Add and of Mul, distributivity, and 0 + y = y, S x + y = S(x + y), 0 · y = 0, S x · y = x · y + y.
  - Add and Mul are sigma1's ZF formulas, not new symbols.
  - Each law is proved once, by induction over ω through `L:IndLem` (replay theorem 39).
  - This lifts Stage 2 from instances to the general laws.
- **Registry of every file:** 677 entries, identical entry for entry to `AX0 ++ DEF0` of `RpInit.v`, none with hypotheses. sigma1's own parse of the Rocq source checks this.
- **Every theorem claims hypotheses `[]`.**
  - By `Replay3.check_batch_ok` and `RpInitOk.REG0_ok`, as in sigma1/RESULTS.md, each accepted statement S has `prov Gam (tof S)`.
  - The pmp verdicts rest on `judge-v3.pmp` computing `check_batch`. Codex still owes that theorem.
- **Reproduction.** All six .jdg files and all 42 mutants were written a second time, from `src\` into an empty folder. They came out byte for byte identical (sha256 and cmp).

## The emitters

All Racket modules require `src\l7core-v1.rkt`. That file is a copy of `sigma1\sigma1.rkt`, with these parts:
- the format;
- the copy of Replay2.v's step semantics and `check_batch`;
- the registry and the prelude import;
- the lemmas on demand, the tactics, the mutants, the registry check and the judge runner.

It adds:
- the replay theorems by name (`rp "L:IndLem"`, read from the comments of `RpB0.v` .. `RpB10.v`);
- the natural-deduction macros `fa-i` (∀-introduction, step H or G), `ex-e` (∃-elimination, L), `fa-e` (∀-elimination, V or S) and `ex-i` (∃-introduction, E);
- the vacuous box B(φ) = ∀φ↑:
  - Y gives φ → B(φ), and V gives B(φ) → φ;
  - to the Shannon test B(φ) is one atom;
- `hsyl`: hypothetical syllogism by K, S and three M, with no tautology test;
- `lemma!` and `emit-file!`.

Each emitter checks every step with this copy as it writes it.

### 1. Equality (`src\eq-v1.rkt`, driver `src\emit-eq-v4.rkt`; `src\eqchain-v1.pmp`)

- **Chains.** The input is x0 ~ x1 ~ … ~ xn, each link in either orientation, and the output is x0 = xn.
  - Each link is one Leibniz step (`Z`) and one tautology step. The tautology step's atoms are those of the hypothesis conjunction and two equations.
  - The file holds chains of length 1, 2, 3, 5, 8, 13, 21, 34 and 55, each with random orientations (exact LCG).
- **Congruence closure** over the registered symbols that are functional relations:
  - the symbols: Suc, Sng, Upr, Opr, Emp, and App under Fnc;
  - the closure is a union-find that keeps a proof line H → v = rep(v) for every variable;
  - merges come from the hypothesis equations, from functionality (two atoms with congruent inputs have equal outputs) and from injectivity (Kuratowski pairs; successor);
  - each merge is justified by Leibniz rewriting of the second atom's arguments and a replay lemma: `L:SucUq`, `Z:SngUq`, `Z:UprUq`, `L:OprUq`, `L:EmpUq`, `Z:Kur1`, `Z:Kur2`, `L:SucInj`, `Z:FncApp`; symmetry and transitivity come from `Z:EqSym` and `Z:EqTr`;
  - goals are equations, or any atom P(…) / x ∈ y congruent to a hypothesis atom;
  - the statements are (h1 ∧ … ∧ hk) → goal.
- **Instances:**
  - successor ladders forward (6) and backward through injectivity (6);
  - towers of pairs forward (5) and backward (5);
  - App chains under Fnc with a Sub goal (5);
  - one mixed instance (Emp, Sng, Upr, Suc, ∈);
  - 40 random instances (12 variables, 14 atoms, exact LCG; the goal is a congruent pair not among the hypothesis equations).
  - The emitter declines a goal that does not follow by congruence.
- **In pmp: `eqchain-v1.pmp`.**
  - It copies the registry bytes (lines 3..679 of replay-all.jdg) itself.
  - It writes the chain theorems for n = 1..40 with the same steps, in its own dform spelling.
  - Run: `pompetzki.exe eqchain-v1.pmp OUT.jdg` (0.8 s, 318,352 bytes).
  - Its mutants come from `src\mut-file-v1.rkt`.

### 2. Tautologies (`src\taut-v1.rkt`, `taut-v2.rkt`, `taut-v3.rkt`, driver `src\emit-taut-v1.rkt`)

- **The cost rule.** The judges' test (`taut_bf`) always branches on the leftmost atom. A step costs the size of that decision tree.
- **The hybrid emitter.**
  - It measures the cost of the single step with a capped copy of `taut_bf`.
  - Within the budget (2000 calls) it writes that step.
  - Otherwise it splits on the atom whose two restrictions are smallest, using the judges' own simplification mkN / mkI.
  - Every node σ of its tree (a conjunction of literals) gets the line σ → B(φ):
    - leaf: σ → φ (the test assigns σ's atoms first, since they are leftmost), then [σ → φ, φ → B(φ)] σ → B(φ);
    - inner node: [σ ∧ p → B(φ), σ ∧ ¬p → B(φ)] σ → B(φ);
    - root: B(φ), then V and M give φ.
  - B(φ) is one atom to the test, so the inner steps stay linear in |σ|.
- **Measured.** These numbers come from the copy of the test.
  - Where the leftmost order is bad and another order is small, the split removes the blow-up. Family clauses-em n = (a1∨b1) ∧ … ∧ (an∨bn) ∨ (q ∨ ¬q):
    - n = 16: 393,211 calls as one step against 8 steps of at most 7 calls each;
    - n = 20, 24, 28: more than 1,000,000 calls as one step against at most 7 per step.
  - Where every order is exponential, the split only bounds the step. conj-perm 10, a conjunction of 10 clauses implies its reverse: 4,093 calls in one step against 17 steps, the largest 2,053.
  - That largest step exceeds the budget. The boxing step tests φ under σ once more, so a step can reach about twice the budget.
  - Pigeonhole, random unsatisfiable 3-CNF and reversed implication chains are cheap in the judges' order (at most 521 calls). The emitter writes them as one step.
- **The control file** `L7-2-direct-control.jdg` holds clauses-em 8, 12, 16 and conj-perm 6, 8 as single steps:
  - pmp: 102.8 s for these 5 theorems;
  - pmp: 20.7 s for the whole split file of 17 theorems.

### 3. Quantifiers (`src\pnx-v1.rkt`, `src\pnx-extra-v2.rkt`, driver `src\emit-pnx-v3.rkt`)

- **Lemma generators**, for formulas B, R, P, C given at run time. Each writes the lines of one equivalence, with a fresh frame variable for the binder:
  - congruence under ∀ and ∃ (G, the distribution axiom, M);
  - ¬∀B ↔ ∃¬B and ¬∃B ↔ ∀¬B;
  - (∀B → R) ↔ ∃(B → R) and (∃B → R) ↔ ∀(B → R);
  - (P → ∀C) ↔ ∀(P → C) and (P → ∃C) ↔ ∃(P → C);
  - in each, x is not free in R and P (de Bruijn shift).
- **The emitter.**
  - It proves f ↔ π(f) for any formula f over the registered symbols, π(f) being a prenex form.
  - There are no Skolem functions; ∃ stays ¬∀¬.
  - The matrix has no double negations; that cleanup is also proved by congruence under each binder.
- **The file:** 7 hand-picked formulas and 40 random formulas (exact LCG, depth 4, at least one quantifier each); the prefixes have up to 6 quantifiers. The manifest lists every f and π(f).

### 4. The laws of ω (`src\omega-base-v1.rkt`, `src\omega-kind-v5.rkt`, `src\omega-laws-v3.rkt`, driver `src\emit-omega-v2.rkt`)

**Definitions.** These are sigma1's, unchanged. Op is Add or Mul.
- Body_Add(f,x,y,z) = Fnc(f) ∧ ∀o (Emp(o) → App(f,o,x)) ∧ ∀i (i∈y → ∃a App(f,i,a)) ∧ ∀i j a b (i∈y ∧ Suc(j,i) ∧ App(f,i,a) ∧ App(f,j,b) → Suc(b,a)) ∧ App(f,y,z).
- Add(x,y,z) = ∃f Body_Add(f,x,y,z).
- Mul is the same with App(f,o,o) at the empty set and Add(a,x,b) as the step.
- C(z,z') stands for Suc(z',z) (Add) and for Add(z,x,z') (Mul).
- z0 stands for x (Add) and for o (Mul).

**Induction schema** (`ind!`). For a formula φ(n) with parameters it proves, once per φ:

  (∀o (Emp o → φ(o)) ∧ ∀n (Nat n → (φ(n) → ∀m (Suc(m,n) → φ(m))))) → ∀n (Nat n → φ(n)).

- Take w with Om(w) from Nat(n).
- Form the set h = {d ∈ w : φ(d)} with a Separation instance (a Y step).
- `L:IndLem` gives Sub(w,h).
- `L:ZeroW`, `L:SucW` and `H:NatW` supply its premises.

**Basic lemmas:**
- SngFun: Sng(f,p) ∧ Opr(p,u,v) → (App(f,i,a) ↔ u = i ∧ v = a);
- UnFun: f ∪ {p} as App;
- NatZero: Emp(o) → Nat(o);
- NatTr: natural numbers are transitive (`H:NatOrd`, `H:OrdTrans`, `H:TrE`).

**Recursion lemmas, each for Add and for Mul:**
- Base: Emp(o) → ∃f (Body(f,x,o,z0) ∧ Dm(f,o)), with f = {(o,z0)}.
  - Dm(f,y) = ∀i a (App(f,i,a) → i ∈ y ∨ i = y) is the exact domain.
- Step: Body(f,x,y,z) ∧ Dm(f,y) ∧ Suc(y',y) ∧ C(z,z') ∧ Opr(p,y',z') ∧ g = f ∪ {p} → Body(g,x,y',z') ∧ Dm(g,y').
- Ex: ∀y ∈ ω ∀x ∈ ω ∃z ∈ ω ∃f (Body(f,x,y,z) ∧ Dm(f,y)), by induction on y. Its step uses `H:SucEx` or Tot_Add, `Z:OprEx` and `K:AddEx`.
- Tot: ∃z ∈ ω Op(x,y,z).
- Uq: Op(x,y,z1) ∧ Op(x,y,z2) → z1 = z2. It needs Nat y for Add, and Nat x, Nat y for Mul.
  - The proof is an induction on k: k ≤ y → f(k) = g(k).
- S: Op(x,y,z) ∧ Suc(y',y) ∧ C(z,z') → Op(x,y',z').
- Z: Op(x,o,z0).
- Zinv: Op(x,o,z) → z = z0.
- Sinv: Op(x,y',z') ∧ Suc(y',y) → ∃z ∈ ω (Op(x,y,z) ∧ C(z,z')).
- NatOp: Op(x,y,z) → Nat z.

**The laws.** Each is a free-variable theorem and also its universal closure (`(Closed …)` in the index). All variables are in ω, i.e. every one carries Nat.
- AddZL: Emp(o) → Add(o,y,y). In arithmetic: 0 + y = y.
- AddSL: Suc(x',x) ∧ Add(x,y,z) ∧ Suc(z',z) → Add(x',y,z'). In arithmetic: S x + y = S(x + y).
- AddComm: Add(x,y,z) → Add(y,x,z).
- AddAssoc: Add(x,y,u) ∧ Add(u,z,v) ∧ Add(y,z,w) → Add(x,w,v). In arithmetic: (x + y) + z = x + (y + z).
- MulZL: Emp(o) → Mul(o,y,o). In arithmetic: 0 · y = 0.
- MulSL: Suc(x',x) ∧ Mul(x,y,z) ∧ Add(z,y,v) → Mul(x',y,v). In arithmetic: S x · y = x · y + y.
- MulComm: Mul(x,y,z) → Mul(y,x,z).
- DistL: Add(y,z,s) ∧ Mul(x,s,p) ∧ Mul(x,y,a) ∧ Mul(x,z,b) → Add(a,b,p). In arithmetic: x(y + z) = xy + xz.
- MulAssoc: Mul(x,y,a) ∧ Mul(a,z,p) ∧ Mul(y,z,b) → Mul(x,b,p). In arithmetic: (xy)z = x(yz).

**Size.** 56 generated theorems, 1,543 generated steps, plus 46 replay theorems copied as prelude (817 steps). The largest tautology step needed 335 calls.

**For comparison:** sigma1's `05-arithmetic.jdg` proves the instances a + b ≤ 8 and a, b ≤ 3 with 20,508 steps.

## Axiom trace

Computed with `src\axtrace-v1.rkt`. It follows U steps through the earlier theorems and classifies Y steps as Separation or Collection.

| file | axioms reached |
|---|---|
| L7-4-omega-laws.jdg | Extensionality, Pairing, Union, Infinity, Foundation, Separation instances, definitions |
| L7-1-equality.jdg | Extensionality, Pairing, Foundation, Separation instances, definitions |
| L7-1-eqchain-pmp.jdg, L7-2-*.jdg, L7-3-quantifiers.jdg | none: logic only |

Power Set, Choice and Collection are not used in any file.

## Mutants

`src\mutants-v1.rkt` mutates each kind of step at the first candidate. If the copy of the checker accepts the change, it moves on to the next candidate, up to 200.
- On the equality file, sigma1's first-candidate rule gave a still-correct derivation for use-shift: the shifted registry entry fed a premise the tautology step did not need. The search fixes that.

`src\mutants-v2.rkt` writes a mutated copy only when the copy of the checker rejects it.
- registry-suc (the definition of Suc2 changed) was not written for the files that use no registry entry: L7-1-eqchain-pmp, L7-2-*, L7-3-quantifiers.
- Kinds with no candidate step in a file are absent from that file's list.

The kinds:
- neg-final, twin-final (a false statement), drop-step: on the last theorem;
- taut-goal (the goal negated);
- mp-swap;
- use-shift (registry index + 1);
- leib-swap (the equation reversed);
- exi-witness (witness + 1);
- exel-var, alli-var, gen-var (variable + 1);
- ax-flip (axiom negated);
- registry-suc.

## Judge results

Run with `src\judge-run-v1.rkt`, one row per file: pmp first, then Racket.

The wall-clock windows (`date`):
- ω laws (judge-omega-1.txt): 17:56:51 to 18:00:57
- equality (judge-eq-1.txt): 18:02:37 to 18:13:38
- quantifiers (judge-quant-1.txt): 18:32:40 to 18:35:48
- tautologies and control (judge-taut-1.txt): 18:32:44 to 18:41:03
- pmp chain file (judge-pmpchain-1.txt): 18:36:06 to 18:45:37

| file | pmp | pmp time | Racket | Racket time | Racket's count (registry, theorems, steps, final registry) |
|---|---|---:|---|---:|---|
| L7-4-omega-laws.jdg | ACCEPT, exit 0 | 46.0 s | ACCEPT, exit 0 | 0.6 s | 677, 102, 2360, 779 |
| L7-1-equality.jdg | ACCEPT, exit 0 | 117.8 s | ACCEPT, exit 0 | 0.5 s | 677, 98, 7057, 775 |
| L7-1-eqchain-pmp.jdg | ACCEPT, exit 0 | 137.9 s | ACCEPT, exit 0 | 0.7 s | 677, 40, 1720, 717 |
| L7-2-tautologies.jdg | ACCEPT, exit 0 | 20.7 s | ACCEPT, exit 0 | 0.6 s | 677, 17, 79, 694 |
| L7-2-direct-control.jdg | ACCEPT, exit 0 | 102.8 s | ACCEPT, exit 0 | 0.8 s | 677, 5, 5, 682 |
| L7-3-quantifiers.jdg | ACCEPT, exit 0 | 40.1 s | ACCEPT, exit 0 | 0.8 s | 677, 47, 10690, 724 |

sums over these files: pmp 465522 ms, Racket 4370 ms

| mutant | pmp | Racket | pmp: theorem step, reason | Racket: theorem step (rule) |
|---|---|---|---|---|
| mut/L7-4-omega-laws-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 101 6: the last line is not the statement renamed by sig | 101 6 (final: last line is not the statement) |
| mut/L7-4-omega-laws-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 14 10: exel: the side conditions of existential elimination fail | 14 10 (step L) |
| mut/L7-4-omega-laws-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 20 37: exi: the formula is not an existential introduction | 20 37 (step E) |
| mut/L7-4-omega-laws-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 14 4: leib: the formula is not Leibniz's law for the given formula | 14 4 (step Z) |
| mut/L7-4-omega-laws-mp-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 20 42: mp: the second line is not an implication | 20 42 (step M) |
| mut/L7-4-omega-laws-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 101 7: the last line is not the statement renamed by sig | 101 7 (final: last line is not the statement) |
| mut/L7-4-omega-laws-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 26 13: taut: not a tautology | 26 13 (step T) |
| mut/L7-4-omega-laws-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 14 9: taut: not a tautology | 14 9 (step T) |
| mut/L7-4-omega-laws-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 101 7: the last line is not the statement renamed by sig | 101 7 (final: last line is not the statement) |
| mut/L7-4-omega-laws-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 14 1: spec: the line has no leading All to instantiate | 14 1 (step S) |
| mut/L7-1-equality-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 97 102: the last line is not the statement renamed by sig | 97 102 (final: last line is not the statement) |
| mut/L7-1-equality-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 2: leib: the formula is not Leibniz's law for the given formula | 0 2 (step Z) |
| mut/L7-1-equality-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 97 103: the last line is not the statement renamed by sig | 97 103 (final: last line is not the statement) |
| mut/L7-1-equality-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 7: taut: not a tautology | 11 7 (step T) |
| mut/L7-1-equality-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 1: taut: not a tautology | 0 1 (step T) |
| mut/L7-1-equality-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 97 103: the last line is not the statement renamed by sig | 97 103 (final: last line is not the statement) |
| mut/L7-1-equality-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 12 15: taut: not a tautology | 12 15 (step T) |
| mut/L7-1-eqchain-pmp-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 39 81: the last line is not the statement renamed by sig | 39 81 (final: last line is not the statement) |
| mut/L7-1-eqchain-pmp-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 2: leib: the formula is not Leibniz's law for the given formula | 0 2 (step Z) |
| mut/L7-1-eqchain-pmp-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 39 82: the last line is not the statement renamed by sig | 39 82 (final: last line is not the statement) |
| mut/L7-1-eqchain-pmp-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 1: taut: not a tautology | 0 1 (step T) |
| mut/L7-1-eqchain-pmp-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 39 82: the last line is not the statement renamed by sig | 39 82 (final: last line is not the statement) |
| mut/L7-2-direct-control-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 0: the theorem has no lines | 4 0 (final: no lines) |
| mut/L7-2-direct-control-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 1: the last line is not the statement renamed by sig | 4 1 (final: last line is not the statement) |
| mut/L7-2-direct-control-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0: taut: not a tautology | 0 0 (step T) |
| mut/L7-2-direct-control-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 1: the last line is not the statement renamed by sig | 4 1 (final: last line is not the statement) |
| mut/L7-2-tautologies-ax-flip.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0: ax: not an axiom shape | 0 0 (step Y) |
| mut/L7-2-tautologies-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 16 1: the last line is not the statement renamed by sig | 16 1 (final: last line is not the statement) |
| mut/L7-2-tautologies-mp-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 7: mp: the second line is not an implication | 1 7 (step M) |
| mut/L7-2-tautologies-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 16 2: the last line is not the statement renamed by sig | 16 2 (final: last line is not the statement) |
| mut/L7-2-tautologies-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 1: taut: not a tautology | 0 1 (step T) |
| mut/L7-2-tautologies-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 16 2: the last line is not the statement renamed by sig | 16 2 (final: last line is not the statement) |
| mut/L7-3-quantifiers-alli-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 28: alli: the side conditions of universal introduction fail | 0 28 (step H) |
| mut/L7-3-quantifiers-ax-flip.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 5: ax: not an axiom shape | 0 5 (step Y) |
| mut/L7-3-quantifiers-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 46 103: the last line is not the statement renamed by sig | 46 103 (final: last line is not the statement) |
| mut/L7-3-quantifiers-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 25: exel: the side conditions of existential elimination fail | 0 25 (step L) |
| mut/L7-3-quantifiers-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 58: exi: the formula is not an existential introduction | 2 58 (step E) |
| mut/L7-3-quantifiers-gen-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 6: mp: the antecedent differs from the first line | 0 6 (step M) |
| mut/L7-3-quantifiers-mp-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 6: mp: the second line is not an implication | 0 6 (step M) |
| mut/L7-3-quantifiers-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 46 104: the last line is not the statement renamed by sig | 46 104 (final: last line is not the statement) |
| mut/L7-3-quantifiers-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0: taut: not a tautology | 0 0 (step T) |
| mut/L7-3-quantifiers-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 46 104: the last line is not the statement renamed by sig | 46 104 (final: last line is not the statement) |

counts: files 6 (6 ACCEPT by both), mutants 42 (42 REJECT by both)


## Not done here

- **Linear arithmetic with Farkas certificates, and polynomial identities.** The release-day table lists these for L7; they were not part of this session's brief.
  - Polynomial identities over ω are the next use of the laws above: normalisation by AddComm, AddAssoc, DistL, MulComm and MulAssoc, applied as lemma instances.
  - Farkas certificates are also in L2D's list.
- **Formulas that are exponential in every split order** (conj-perm). The split bounds each step, at about twice the budget, but not the total. A Hilbert-style mode (∧/∨ manipulation by K, S, C and M only, without the tautology test) is not written.
- **Order, cancellation and subtraction** on ω are not derived.
- **The laws are stated relationally** over sigma1's formulas, with Nat hypotheses. No function symbols.
- **pmp.** Only the chain emitter is written in pmp; the rest is Racket.

## Reproduce

```
cd C:\ClaudeOutput\pompetzki\lanes\L7\src
racket emit-omega-v2.rkt DIR
racket emit-eq-v4.rkt DIR
racket emit-pnx-v3.rkt DIR
racket emit-taut-v1.rkt DIR
..\..\..\pompetzki.exe eqchain-v1.pmp DIR\L7-1-eqchain-pmp.jdg
racket mut-file-v1.rkt DIR\L7-1-eqchain-pmp.jdg DIR L7-1-eqchain-pmp
racket judge-run-v1.rkt RESULTS.txt DIR\*.jdg DIR\mut\*.jdg
```

`src\superseded\` keeps the earlier versions unchanged:
- omega-kind v1..v4: v1 stopped mid-step, v2..v4 had parenthesis and premise faults;
- omega-laws v1, v2;
- emit-omega v1;
- emit-eq v1..v3;
- pnx-extra v1: its counter used `box`, which l7core exports as the vacuous ∀;
- emit-pnx v1, v2.

## Files

- `src\axtrace-v1.rkt` (1610 bytes, sha256 `ebd2ec5f4202c73306421a29f48c19951917e8efd682851a3e1becf70c95787a`)
- `src\dump-v1.rkt` (189 bytes, sha256 `6d5b065bf8412ed4c5e77355025972c561391443e4ed3ba549638e7bd53df72f`)
- `src\emit-eq-v4.rkt` (3650 bytes, sha256 `e1521c8608d867cd14e41f3dc747f3aa61e3fe5015b552c7ef31d7d63b1721ec`)
- `src\emit-omega-v2.rkt` (936 bytes, sha256 `cd79a02a1edaf73aca276ea33af5f283b7c5ef7281eda0e87830365af07398c1`)
- `src\emit-pnx-v3.rkt` (2204 bytes, sha256 `5eacbfea8e9bcc863a7fe24c546eb27fad1876f278c3565a88534ec9ea939c39`)
- `src\emit-taut-v1.rkt` (3115 bytes, sha256 `e5d5553e6bb008ef117bf27921f07fae68c9c898cc6dcb0cbbb565f5145491f8`)
- `src\eq-v1.rkt` (14243 bytes, sha256 `cd1fb74d59d0acbe6bd31573b779597cc4951afb3364080bb8161ea3f6f1bd04`)
- `src\judge-run-v1.rkt` (972 bytes, sha256 `b7620f5d573b4a131f48f0bb496ed5376d56b423dc2c42815ca42e95ac49e851`)
- `src\l7core-v1.rkt` (60687 bytes, sha256 `7827b3781a02fa24285b12e8422810adfdf506ca1144e2dd6e761a870b53d087`)
- `src\mut-file-v1.rkt` (1804 bytes, sha256 `733058bef7ff86ee634bdb666ff2f9d831595023a9f4ed2503b5df95a28249d3`)
- `src\mutants-v1.rkt` (6075 bytes, sha256 `ab79425cf21197b9082ae4a1eb44fb825dab72fa4781a1af7ae6b7d66c151551`)
- `src\mutants-v2.rkt` (2460 bytes, sha256 `7aad50168c0660e1ad6892c83a7207b140b6b648d568622e8d5c196e120b51f1`)
- `src\omega-base-v1.rkt` (8560 bytes, sha256 `9ed06e26293545cc2e9949fa672bdefbabfd9cb302521b87d9cd785fa60f87f7`)
- `src\omega-kind-v5.rkt` (22515 bytes, sha256 `760c26abf397f45717c3ad254486b39fc58821727a93bfd81b75fc989aa55d43`)
- `src\omega-laws-v3.rkt` (20250 bytes, sha256 `f875f0a85572de1a12cf5c70002941c8d00aa64b5eecdd0bcc5573fa06eddac1`)
- `src\parencheck.rkt` (607 bytes, sha256 `f8ebd1356ed1072b05f029f8879a8d2244ad086c64549b6c66225225b81dcd44`)
- `src\pnx-extra-v2.rkt` (2993 bytes, sha256 `8328439f819d04f5bc510ea6442aa510810ebdb1ca5c59eaa1d02a78e8ab7203`)
- `src\pnx-v1.rkt` (7778 bytes, sha256 `984eafceab6c331e6c7cedd915df319090c3523886119aab1663803398bf7c53`)
- `src\sigma1-copy.rkt` (82114 bytes, sha256 `7d3ff29ca288d952ba7526940c3728aaa1bc202323311cb29b3409a4b4ff3337`)
- `src\tables-v2.rkt` (3171 bytes, sha256 `056dc0cd8e74d5bc2ad6bc2937af43fa8017ab000a017ec5bac6e18a5a39cf43`)
- `src\taut-v1.rkt` (5700 bytes, sha256 `061047dd519ee608dff39f1c42e1826df0c30f723b66689165d79663ef633cc1`)
- `src\taut-v2.rkt` (566 bytes, sha256 `21d6825bbbb2fe243e62620f162f4acace322451cc4cf4a63496edb61856f77a`)
- `src\taut-v3.rkt` (2255 bytes, sha256 `0cd5ff76c78fb207c7379bf27d4f0a815198bcc0657a00f178f032741c2f4068`)
- `src\eqchain-v1.pmp` (3900 bytes, sha256 `c12b986d18c27493cd7e66d9465d1e681d70b8dd701afd6761a6c6a41c0c67cf`)

- `out\L7-1-eqchain-pmp.jdg` (318352 bytes, sha256 `8fdb1ca3160d5e56e2177fe80ad0158ca5f77d845312c77e0a1b6fd981ab7ad8`)
- `out\L7-1-equality.jdg` (514790 bytes, sha256 `289f44b94ef64cf8ef66dabdd73ea4d2009d6b75b8e11d27db5b345d01930fb3`)
- `out\L7-2-direct-control.jdg` (55792 bytes, sha256 `b4c034a5acd79b4940805149fa247fd29f41a95ca6cef38bbbcbc5f18895bb9c`)
- `out\L7-2-tautologies.jdg` (125938 bytes, sha256 `f42eaffa7ce095682201264962656c76e6e0226f1bbf359316cf247c03317ee7`)
- `out\L7-3-quantifiers.jdg` (765862 bytes, sha256 `f925e0b804fb854ea66241fbe13a61d01df05e829484024a94cacfc8a0fa4535`)
- `out\L7-4-omega-laws.jdg` (1223241 bytes, sha256 `fdcaa25b28d9be7d97b7ab34998a35f519e736de2892de3ccf5e8d484f60bc14`)

- `out\*.index.txt`, `out\*.manifest.txt`: every theorem with key and statement; sizes, hashes, the copy of the checker, the mutants
- `judge-*.txt` (rows), `judge-*.start.txt` / `.end.txt` (`date`), `judge-tables.md` (tables-v2.rkt from the rows)
- `src\superseded\`: earlier versions, unchanged

