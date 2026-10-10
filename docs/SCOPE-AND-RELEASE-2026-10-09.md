# Scope of the one system and the release, 2026-10-09 (written 17:15 by `date`)

## 1. The one system (the Monolith) and where each part stands

| Part | Role | State today |
|---|---|---|
| pmp judge (`judge-v3.pmp` under `pompetzki.exe`) | the only judge of the Book | ACCEPTs Theorem 29's replay (4,551 theorems, 139,194 steps) and today's 7 Stage 2 files; REJECTs every mutant tried |
| Rocq theorem for the judge | acceptance ⇒ `prov` | `Replay3.v`: `check_batch` sound, coqchk done. That the bytes of `judge-v3.pmp` compute `check_batch`: in progress (Codex), not proved |
| Racket copy (`racket/judge.rkt`) | second implementation | agrees on every file so far |
| Native judge (`judge-v3.exe`, pmpc) | speed | 0.57 s for the full replay (4.1 µs per step); interpreter 5.8 ms per step; Codex's v6 voting build 1.8 s |
| Stage 2, Σ₁ (`sigma1/sigma1.rkt`) | arithmetic of ω as ZF theorems | done today in Racket: 7 files, 1,656 theorems, 53,069 steps; Rocq "once" proof not done; derived rules (rank–nullity, Smith, Gröbner, Nullstellensatz, LRAT, Pratt, Farkas) not posted |
| Stage 4, native image theorem | x86-64 semantics, theorem about the bytes | not started |
| Stage 5, Metamath set.mm | supply + export | not started |
| Stage 6, Lean/Mathlib → ZF translator | supply | not started; 0 Mathlib theorems judged by pmp |
| Stage 7, automation | derivation emitters | `sigma1.rkt` is the first one |
| Stage 8, 5090 | searchers | not wired to pmp |
| Stage 9, the Book in pmp | ledger, axiom trace, negative ledger | `lib/ledger.pmp`, cockpit plans 1–3 exist; not wired to judge postings |
| Stage 10, public release | images, sources, receipts | not done; last dist builds 2026-09-17/18/23/24 |
| Lean side (AbschlussCore, agent postings) | earlier ledger | on Lean v4.28.0, which has 3 known kernel exploits; every posting carries "replay on a fixed kernel owed" |

## 2. How much of mathematics is formalized

Numbers read today are marked (2026-10-09); the others are my estimates with their bounds.

- **Denominator, known mathematics.** zbMATH Open indexes about 4.5–5 million documents (estimate). At 5–20 stated results per document that is 2×10⁷ to 10⁸ statements, undergraduate to research.
- **Formalized in any system.**
  - Mathlib: 290,317 theorems and 137,995 definitions (2026-10-09).
  - AFP, set.mm, Mizar, HOL Light and the Rocq libraries together: roughly 0.5–1 million more lemmas (estimate), overlapping Mathlib heavily.
  - Named results done in Lean 4 (2026-10-09): Fermat's Last Theorem, the Four Colour theorem, Feit–Thompson. Kepler is done in HOL Light/Isabelle (Flyspeck); its Lean 4 port is 55% complete by its own report.
- **Fractions.**
  - Undergraduate core: 80–95% formalized somewhere (estimate).
  - Research literature as statements: 0.1–1% (estimate).
  - Judged by pmp, the only measure that counts here: 4,551 + 1,537 generated theorems, all inside ZF. That is under 10⁻⁴ of the statement count.
- **Open problems.** There is no fixed denominator: new ones are posed every week. Under the Book's rule an open entry closes by a proof, a refutation or an independence result. The one entry closed by pmp so far is half of CH: Theorem 29 gives Con(ZFC) → Con(ZFC + ¬CH*). Gödel's half through L is owed.

## 3. Length to cover the known corpus with pmp as judge

- **Checking length.** Mathlib through a translator would give 290k theorems at an estimated 10³–10⁵ Hilbert steps each, so 3×10⁸ to 3×10¹⁰ steps. At the native judge's 4.1 µs per step that is 20 minutes to 34 hours of checking.
- **Building length.** The translator (Lean's type theory into ZF plus universes as inaccessibles), the derived rules, and the set.mm import are each long programs that are not written yet. The literature beyond the libraries enters through freezes, statement by statement.

## 4. Release today: what is ready, and what it may claim

Ready for release, all files on disk:
- `pompetzki.exe`, `judge-v3.pmp`, `racket/judge.rkt`, the JDG1 format, `rocq2jdg.rkt`.
- `Replay2.v`, `Replay3.v`, `RpInitOk.v` and the coqchk receipts.
- `replay-all.jdg` (Theorem 29).
- `sigma1/` with its files, mutants and judge results.

What the release may claim:
- `check_batch` is sound for `prov` (Rocq).
- Two independent implementations agree on 4,551 + 1,656 theorems and on every mutant.
- Not yet: that the pmp bytes compute `check_batch`. Codex's proof is open; the release states it as owed.

Steps to release: finish the 15 remaining judge runs (about 10 minutes); write RESULTS.md; then a release folder with a sha256 manifest and README; then publication, which needs Christopher's yes and the place.
