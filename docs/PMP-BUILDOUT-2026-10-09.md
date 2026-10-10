# pmp as the only judge: build-out, 2026-10-09

Decided in conversation on 2026-10-09: pmp is the only judge. Rocq is used once, for the theorem that the checker's acceptance implies derivability, and then leaves the posting path. Racket is a second copy of the checker and writes nothing. Lean, Rocq libraries, Metamath, papers and agents supply candidates only. The method (exact linear algebra, certificate per run, Finite Data Principle, Theorem 21.1) is Christopher Pompetzki's.

## Stages

1. **Judge v0.** `LG_CHECK` (lib/logic.pmp) made identical, rule for rule, to `prov` (forcing-src/general/Prov.v), its ZFC axiom table identical to `ZFsym`/`ZFpure` (Elim.v). One canonical derivation format, earlier theorems cited by the hash of statement and derivation. Rocq theorem through PmpFull: acceptance implies `prov ZFpure φ`. Done when coqchk reports no axioms and the mutation suite is refused.
2. **Σ₁-completeness for `prov` over ZF**, proved once in Rocq: every true bounded statement about ω is derivable. Integer checks become ZFC theorems through it. Derived rules posted once each: rank–nullity (nonzero minor + integer kernel basis), Smith (UAV = D), Gröbner and Nullstellensatz cofactors, LRAT, Pratt, Farkas.
3. **Racket copy** of the checker, written from the rule text by a different session.
4. **Native checker image**, separate from the language: static Linux ELF at a fixed address (read, write, exit), run under WSL. x86-64 semantics for the instructions it uses in Rocq, theorem about the bytes; the model cross-checked against execution.
5. **Supply from Metamath set.mm** (Hilbert-style ZFC, public domain); export of our derivations to Metamath format for checking by the Metamath verifiers.
6. **Supply from Lean/Mathlib** through an untrusted translator to ZFC derivations; universes as ZFC + inaccessibles in the trace.
7. **Automation as untrusted pmp programs** that emit derivations (tautologies, equality chains, linear arithmetic with Farkas certificates, polynomial identities, rank certificates).
8. **The 5090** through `extern` into a CUDA DLL; searchers only.
9. **The Book in pmp**: The Process as the append-only ledger, hash chain, document numbers, axiom trace (Theorem 23), negative ledger, period close; the desk on `window.pmp`. Cost fields from the certificate counts.
10. **Public release**: image and sha256, Rocq theorem source, derivation format, accepted certificates, Windows and Linux.

## Stage 1, first comparison (read only, 2026-10-09)

`lib/logic.pmp` (2,540 lines, twenty-eighth cut) against `Prov.v`, `Syn.v`, `Kal.v`, `Elim.v`:

- **Logical rules: the same family.** `LG_CHECK` has k, s, c, mp, gen, inst, dist, vac, refl, leib; `prov` has p_k, p_s, p_c, p_mp, p_gen, p_inst, p_dist, p_vac, p_refl, p_leib and p_ax.
- **Syntax differs.** `LG_CHECK`: Polish notation, named variables, arithmetic terms (0, S, +, *, sub, pf, pfx, quotes), `inst t` for a term t substitutable for x. `prov`: de Bruijn indices, variables as the only terms (`Mem`, `Eqv`, `Pr`, `Neg`, `Imp`, `All`), `p_inst` instantiates by a variable. In ZFC mode the alignment is a map from named variables to de Bruijn indices, with inst restricted to variables.
- **`taut` is already covered.** `Kal.v` proves `ptaut_prov`: the decidable tautology test implies `prov A (pinst s p)`. The truth-table rule is a derived rule whose soundness exists.
- **Rules that stay out of the judge.** ind, pa1–pa7, eval over arithmetic terms, d2, d3, false, and the terms pf and pfx belong to the arithmetic theory T of the Gödel chapters (Theorems 12–14). d2 and d3 are justified as "true of this very checker", which uses the checker's own correctness as a rule. Integer evaluation returns in stage 2 through Σ₁-completeness, as ZF statements about ω.
- **ZFC mode** (`ck_mode 2`): `ax NAME` from a table, `sep` and `coll` schema instances. To be made equal to `ZFsym` (Elim.v) and `ZFpure` (no predicate symbols). Predicate symbols introduced by definitions ("cited by name in ZFC mode") need a definitional-extension step: expansion, or a conservativity theorem in Rocq.
- **First edits (not made yet):** a judge mode that accepts exactly `prov` + `ZFsym` + `taut` and refuses the T rules; an emitter that writes each accepted line as the Rocq `form` term; then the PmpFull proof.
