# Stage 6: Lean 4 / Mathlib into ZF derivations for the pmp judge — design

Lane L6 of the release-day orders, 2026-10-09. Written 18:13 (`date`).

## 1. Trust boundary

- The judge is the only authority. A Mathlib statement counts when a JDG1 file holding its ZF translation is accepted by both judges, run from `C:\ClaudeOutput\pompetzki\judge\`:
  - `pompetzki.exe judge-v3.pmp FILE`
  - `racket\judge.rkt FILE`
- The registry of every file is the first 677 entries of `judge\replay-all.jdg`: the seven axioms of the kernel table (Extensionality, Pairing, Union, Power Set, Infinity, Foundation, Choice) and the 670 definitions of `RpInit.v` (`AX0 ++ DEF0`). No hypothesis entry is used. Every theorem claims hypotheses `[]`.
- By `Replay3.check_batch_ok` and `RpInitOk.REG0_ok` (as in `sigma1\RESULTS.md`), an accepted statement S satisfies `prov Gam (tof S)`. Gam (Ax.v) is ZFC: the seven axioms, every Separation and Collection instance, and the registered definitions.
- Untrusted, all of it: the Lean exporter, the Lean side generally, the statement translator, the proof engine, the scripts. A defect in any of them shows up as a REJECT. It cannot produce an accepted false theorem.
- Not covered by the judge, and stated as such: whether the ZF formula is the meaning of the Lean statement. That is the translation table of section 4. It is fixed, short, and printed next to every theorem in the index file.

## 2. Lean's type theory in ZF (the general plan)

The model is the standard set-theoretic one for the calculus of inductive constructions with a hierarchy of universes (Werner 1997; Carneiro, *The type theory of Lean*, 2019).

**Universes.**
- `Prop` is interpreted as {∅, {∅}}. A proposition is a truth value, and a proof is ∅ when the value is {∅}. This gives proof irrelevance and impredicativity at once.
- `Sort (u+1)` = `Type u` is interpreted as V_κu, with κ0 < κ1 < … inaccessible cardinals.
- ZFC does not prove that an inaccessible exists. A theorem whose interpretation needs `Type u` with u ≥ 1 as a set therefore carries hypotheses "κ0, …, κu are inaccessible". In JDG1 these are hypothesis entries of the registry, as the replay already does with its placeholder hypotheses. The theorem lists their numbers in its `hyps` field, so the axiom trace of every posting shows which universes it used.
- Statements about ℕ need no universe beyond V_ω+1, so they need no hypothesis. All theorems of this slice have `hyps = []`.

**Dependent types.**
- Π(x:A), B x is interpreted as the set of functions f with domain [A] and f(x) ∈ [B](x). These are App/Fnc/Dom of the registry.
- λ is interpreted as its graph, and application as App.
- Σ-types and structures are interpreted as pairs (Opr).
- `Eq` is ZF equality.
- `Quot` is the set of equivalence classes, and `Quot.sound` is extensionality.
- `Classical.choice` is the axiom of Choice (entry 6).

**Inductive types as least fixed points.**
- A strictly positive inductive type with constructors c1 … cn is interpreted as the least set closed under the interpreted constructors. It is built by transfinite recursion up to a regular cardinal above the arities; for finitary types, ω.
- The recursor is interpreted as the unique function satisfying the recursor equations, by recursion on the construction stage. Its existence and uniqueness are a ZF theorem per type, of the shape of L:RecThm and H:RecUq for ω.
- `Nat` is ω (K:OmEx, L:OmUq), with `zero` ↦ ∅ (Emp) and `succ` ↦ Suc.
- `Nat.rec` is interpreted through L:RecThm (recursion on ω), which is a hypothesis-free theorem of the Theorem 29 replay.
- `Int` (planned, not in this slice): `Int.ofNat` | `Int.negSucc` as the tagged sum {∅}×ω ∪ {{∅}}×ω, with operations defined by cases on the tags and theorems proved through those cases.
- Inductive predicates are interpreted as the least relation closed under their rules. `Nat.le` (rules `refl`, `step`) is the least such relation on ω, which is ∈ ∪ =. `Nat.lt n m` unfolds to `n+1 ≤ m`, which is ∈.

**Definitions.**
- The registry cannot grow: Gam fixes the definitions to `Dall`. Every Lean definition is therefore unfolded into a ZF formula over the registered symbols, as Stage 2 did for Add and Mul.
- Recursive definitions become relations whose existence and uniqueness are proved once, as general theorems over ω (section 5).

## 3. Export from Lean

- `lean4export` is not on this machine, and downloads need Christopher's yes. The export reads the `.olean` files through Lean itself.
- `lean\L6Export.lean` imports Mathlib (v4.28.0, as built in `C:\ClaudeOutput\abschluss\lean\AbschlussCore`) and walks `env.constants`. For every theorem whose type uses only the constants of the slice, it writes the type as an s-expression of `Lean.Expr`: `bvar`, `const`, `app`, `pi`, `lam`, `lit`.
- It ran once, 17:36:24–17:37:30, under the machine-wide lock `abschluss-verify\lean.lock` (owner L6).
  - 476,096 theorems in the environment.
  - 381 statements in the slice, in `lean\export-nat.sexp`.
- The same walk can write proof terms (`ConstantInfo.value`). This slice does not use them (section 6).

## 4. Statement translation (leanstmt.rkt, engine.rkt `tr`)

Lean (after reading `Expr`) into the statement language, then into ZF by sigma1.rkt's `tr`, extended by one clause:

| Lean | statement language | ZF formula (DSL of sigma1.rkt) |
|---|---|---|
| `∀ (x : ℕ), P` | `(nall x P)` | `∀x (Nat(x) → [P])`, with Nat(x) = ∃w (Om(w) ∧ x ∈ w) (registered p72) |
| `∃ x : ℕ, P` (`Exists`) | `(some x P)` | `∃x (Nat(x) ∧ [P])`, as sigma1's `some` |
| `P → Q` (non-dependent, Prop domain) | `(imp P Q)` | `[P] → [Q]` |
| `¬`, `∧`, `∨`, `↔` | `not and or iff` | the connectives |
| `@Eq ℕ a b` | `(= a b)` | `[a] = [b]` |
| `@Ne ℕ a b` | `(not (= a b))` | `¬([a] = [b])` |
| `@LE.le ℕ instLENat a b`, `GE.ge b a` | `(<= a b)` | `[a] ∈ [b] ∨ [a] = [b]` |
| `@LT.lt ℕ instLTNat a b`, `GT.gt b a` | `(< a b)` | `[a] ∈ [b]` |
| `@HAdd.hAdd ℕ ℕ ℕ (instHAdd ℕ instAddNat) a b` | `(+ a b)` | `∃u (Add(a,b,u) ∧ K(u))` |
| `@HMul.hMul ℕ ℕ ℕ (instHMul ℕ instMulNat) a b` | `(* a b)` | `∃u (Mul(a,b,u) ∧ K(u))` |
| `Nat.succ a` | `(S a)` | `∃u (Suc(u,a) ∧ K(u))` |
| `@OfNat.ofNat ℕ n (instOfNatNat n)` | `n` | `∃u (N_n(u) ∧ K(u))`, sigma1's von Neumann numeral |

- Terms are translated by continuation K, exactly as sigma1.rkt's `wrap`.
- Add and Mul are sigma1.rkt's formulas, built by the same code (`fin-f`, copied into zfnat.rkt): Add(x,y,z) says that a finite function f with f(0) = x and f(i+1) = S(f(i)) on {0,…,y} has f(y) = z. Mul is the same with f(0) = 0 and f(i+1) = f(i)+x.
- Every instance argument must be the canonical one shown in the table; anything else is refused. 336 of the 381 exported statements translate. The 45 refused ones quantify over predicates (`P : ℕ → Prop`, the induction principles) or use `=` between propositions.

**Why the table is the meaning (and how far that is checked).**
- Lean's `Nat.add` is defined by `n + 0 = n` and `n + succ m = succ (n + m)`; `Nat.mul` by `n * 0 = 0` and `n * succ m = n * m + n`. These four equations are themselves in the batch, as the ZF theorems `Nat.add_zero`, `Nat.add_succ`, `Nat.mul_zero`, `Nat.mul_succ` over Add and Mul.
- Together with existence and uniqueness of values (Tot, Uq below), they determine Add and Mul on ω: the recursion theorem gives exactly one function with these equations.
- For ≤, the constructors `Nat.le.refl` (as `Nat.le_refl`) and `Nat.le.step` (as `Nat.le_step`) are in the batch.
- Not yet derived: the minimality half for ≤ (every relation closed under refl and step contains ∈ ∪ =).

## 5. ZF theory of ω behind the slice (zfnat.rkt)

- General theorems, each a schematic JDG1 theorem (open in its frame variables, instantiated by `U` with a renaming).
- Proved from L:RecThm, L:IndLem and the ordinal facts of the replay (H:OrdTr, H:OrdT3, H:OmOrd0, L:OmTr, H:NatW, …). Those replay theorems are copied into each file with their dependencies, and are checked again there.
- The theorems, for k = add and k = mul, with R(a,b) = Suc(b,a) for add and Add(a,x,b) for mul:

| key | statement |
|---|---|
| `(Uq k)` | Om(w) [∧ x∈w for mul] ∧ y∈w ∧ k(x,y,z) ∧ k(x,y,z') → z = z' (induction on ω) |
| `(Graph k)` | Om(w) ∧ x∈w → ∃g (Fnc g ∧ Dom(g,w) ∧ Rng(g,w) ∧ ∀a b (App(g,a,b) → R(a,b))) (Separation on w×w) |
| `(Rec k)` | Om(w) ∧ x∈w → ∃F (Fnc F ∧ Dom(F,w) ∧ Rng(F,w) ∧ F(∅) = x or ∅ ∧ ∀i a j b (F(i)=a ∧ Suc(j,i) ∧ F(j)=b → R(a,b))) (L:RecThm) |
| `(FinOfRec k)` | the recursion function gives values: Om(w) ∧ RecBody(F) ∧ y∈w ∧ App(F,y,z) → k(x,y,z) |
| `(Tot k)` | Om(w) ∧ x∈w ∧ y∈w → ∃z (z∈w ∧ k(x,y,z)) |
| `(Zero k)` | Om(w) ∧ x∈w ∧ Emp(o) → Add(x,o,x) / Mul(x,o,o) |
| `(Step k)` | Om(w) ∧ x∈w ∧ y∈w ∧ k(x,y,z) ∧ Suc(s,y) ∧ R(z,z') → k(x,s,z') |
| `(InW k)` | Om(w) ∧ x∈w ∧ y∈w ∧ k(x,y,z) → z∈w |

- Induction over ω (`induct` in zfbatch.rkt) works inside a derivation. A Separation instance {x ∈ w | φ(x)} is introduced as a `Y` step; the shape is checked by the judges' `isSep`. L:IndLem then gives w ⊆ {x ∈ w | φ(x)}.
- Numerals use sigma1.rkt's NumEx and NumUq: a chain v0 … vn with Emp(v0) and Suc(vk+1, vk).

## 6. Proofs: what this slice does and what the full translator does

**This slice.**
- Only the statement comes from Mathlib.
- The derivation is made by `engine.rkt`:
  - It takes w with Om(w) (K:OmEx) and introduces the variables, using Nat(x) ↔ x ∈ w (H:NatW).
  - It gives every term a value in w with its defining relation in the context (Tot, H:SucEx, H:EmpEx).
  - It proves the formula over the values from hints (earlier theorems of the batch, ZF lemmas, the induction hypothesis), using:
    - congruence closure for equality, with proofs from Z:EqTr, Z:EqSym, Leibniz and the Uq theorems;
    - canonical forms of atoms;
    - case splits on equality atoms;
    - the copy of the checker's tautology test.
  - It bridges back to sigma1's translation with the uniqueness theorems: ∃u (R(…,u) ∧ K(u)) ↔ K(value).
- A hint is a pointer to an earlier theorem. The judges check every line.

**The full translator (next slices).**
- It reads proof terms as well (`ConstantInfo.value`).
- Each kernel typing judgment Γ ⊢ t : A becomes a ZF theorem [Γ] → [t] ∈ [A]. For A : Prop this says that [A] holds.
- The kernel rules become ZF lemma schemes about the interpretation, proved once per shape:
  - β, δ (unfolding a definition into its formula), ι (recursor equations, from the RecThm/RecUq theorems of each inductive type), η, and proof irrelevance (both proofs are ∅).
- Lean's elaborated proofs are large, so the realistic path is mixed: translate the term where it is small, and re-derive with the engine where a tactic produced a large term (`omega`, `simp`, `decide`). The judge accepts either kind of derivation.

## 7. Encoding limits met

- **No new definitions.** Every statement carries the full Add/Mul formulas: Add is about 60 formula nodes, and Mul contains Add.
- **Context in every line.** Lines repeat the context, which holds the value facts with these formulas. This is what makes the file large; see RESULTS.md for the bytes and the judge times.
- A later version can keep a smaller context per line: a line needs only the assumptions its tautology uses. The judges' semantics allow this unchanged.
- **Tautology steps.** Shannon expansion in the judges is exponential in the worst case. The engine checks each tautology with its copy before emitting it. The largest test is listed in the manifest.
