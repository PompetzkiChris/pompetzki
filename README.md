# Pompetzki — the pmp judge, release 2026-10-10

A judge for machine-checked mathematics, by Christopher Pompetzki.

- **What it checks.** `judge/judge-v3.pmp` checks derivations in a Hilbert calculus for first-order logic with equality over ZF: the function `check_batch` of `rocq/Replay2.v`.
- **What it runs on.** pmp, Christopher Pompetzki's exact linear-algebra language. `bin/windows/pompetzki.exe` and `bin/linux/pompetzki` (static x86-64) are its interpreters.
- **Second copy.** `judge/racket/judge.rkt` is an independent implementation of the same function, written from the rule text.
- **Native image.** `bin/linux/jdgchk` is a static Linux ELF of the checker (reads a JDG1 file on stdin).
- **Proved in Rocq 9.1.0, coqchk `Axioms: <none>`:** `check_batch` accepts only derivable theorems (`rocq/Replay3.v`: `check_thm_ok`, `check_batch_ok`; registry `RpInitOk.REG0_ok`).

The method — exact linear algebra, one certificate per run, the Finite Data Principle, Theorem 21.1 — is Christopher Pompetzki's.

## Run it

Windows (PowerShell), from the repository root:

```
cd judge
..\bin\windows\pompetzki.exe judge-v3.pmp ..\certificates\theorem29\replay-all.jdg
racket racket\judge.rkt ..\certificates\theorem29\replay-all.jdg
```

Linux (or WSL):

```
cd judge
../bin/linux/pompetzki judge-v3.pmp ../certificates/theorem29/replay-all.jdg
racket racket/judge.rkt ../certificates/theorem29/replay-all.jdg
../bin/linux/jdgchk < ../certificates/theorem29/replay-all.jdg
```

Both judges print `ACCEPT` with registry 706, theorems 4,551, steps 139,194, final registry 5,257, exit 0. A refused file prints `REJECT` with the theorem and step, exit 1. Format: `docs/JDG1-FORMAT.md`. Soundness argument: `docs/SOUNDNESS.md`. More commands: `docs/QUICKSTART.md`.

**Resource stops are not refusals.** The pmp interpreter stops with `gosub: too deep` on formulas nesting numerals above 38, and with `LIMIT a memory block is full` on registries above 1,091 entries. On those files the Racket judge ACCEPTs; the pmp stop is a resource limit of the interpreter, not a REJECT.

## Results in this release

Every certificate below was accepted by both judges, and every mutated copy listed was refused by both, at the recorded times on 2026-10-09. Each folder holds its own `RESULTS.md` with the commands, exit codes, times and hashes.

| Result | Where | Checked |
|---|---|---|
| **Theorem 29**: Con(ZFC) → Con(ZFC + ¬CH*), forcing | `certificates/theorem29/replay-all.jdg` (4,551 theorems, 139,194 steps); Rocq sources in `rocq/` | both judges ACCEPT; coqchk `Axioms: <none>` |
| **Cohen's half over the plain CH statement**: `AlignCH.con_zfc_con_notch_plain : prov (GamE (Neg ch)) Bot -> prov ZFpure Bot` | `results/ch-theorem29-plain-CH-LCH/` | both judges ACCEPT the alignment file; coqchk clean |
| **Σ₁-completeness, proved once in Rocq**: `bounded_complete` (every true closed bounded sentence about ω is derivable in Gam, every false one is refuted) and `sigma1_complete` | `results/stage2-rocq-sigma1-complete-L2R/` | coqchk `Axioms: <none>` |
| **Conservativity of definitions**: `gam_pure_conservative : syms f = [] -> prov Gam f -> prov ZFpure f` | `results/stage1-conservativity-CX3/` | recursive coqchk `Axioms: <none>` |
| **Arithmetic of ω as ZF theorems** (numerals, membership, n ≠ m, bounded quantifiers, +, ·, true bounded and Σ₁ sentences) | `certificates/stage2-sigma1/` (7 files, 1,656 theorems, 53,069 steps; 70 mutants) | both judges ACCEPT; all mutants REJECT |
| **Derived rules**: LRAT, Smith normal form, rank–nullity over Q, Pratt primality, Farkas infeasibility | `results/stage2-derived-rules-L2D/` (19 originals) | 19 × both ACCEPT; 186 mutants × both REJECT at the same theorem and step |
| LRAT corpus (CaDiCaL, 35 instances) | `results/stage2-lrat-AG5/` | 35 LRAT ACCEPT; 3 JDG files both judges ACCEPT |
| Pratt corpus: all 78,498 primes below 10⁶, 2³¹−1, 2⁶¹−1, 2⁸⁹−1, the 10 largest primes below 2⁶⁴ | `results/stage2-pratt-G1/` (index and hashes; JDG for 7, 13, 23) | checker accepts every certificate; 1,000 composites and 1,000 mutations refused |
| Farkas certificate `cyclic-k02` | `results/stage2-farkas-G2/` | both judges ACCEPT |
| **Lean/Mathlib statements as ZF theorems**: 252 statements of the `import Mathlib` environment (9 from Mathlib modules, 243 from Lean core `Init`) under their Lean names | `results/stage6-lean-mathlib-L6/L6-nat.jdg` (345 theorems, 37,714 steps) | both judges ACCEPT |
| **Automation**: emitters for equality, equality chains (written in pmp), tautologies, quantifiers; the general laws of + and · on ω proved once by induction | `results/stage7-automation-L7/out/` (6 files, 42 mutants) | both judges ACCEPT; 42/42 mutants REJECT |
| **RTX 5090 through pmp `extern`**: CUDA DLL, exact integer rank, kernel and Smith form, every GPU result rechecked exactly | `results/stage8-gpu-rank-smith-L8G/` (`rn6x8`, `tri5`, `smith3`; 30 mutants) | both judges ACCEPT; 30/30 mutants REJECT |
| **Metamath set.mm map**: 167 `ax-`/`df-` labels of the 5,757-assertion class-free cohort of set.mm (50,912 assertions) mapped to the registry | `results/stage5-metamath-AG12/` | 10 route-check files, both judges ACCEPT |

## The ten stages

The build-out plan is `docs/PMP-BUILDOUT-2026-10-09.md`.

| # | Stage | In this release | Owed |
|---|---|---|---|
| 1 | Judge v0 and its Rocq theorem | `check_batch` sound for `prov` (Replay3, coqchk none); Gam → ZFpure for pure formulas (CX3); `judge/mut` refused by both judges | the Rocq theorem that the bytes of `judge-v3.pmp`, run under the pmp semantics, compute `check_batch`. Until it is closed a pmp verdict rests on its agreement with the Racket copy |
| 2 | Σ₁-completeness and derived rules | Σ₁-completeness in Rocq; ω arithmetic; LRAT, Smith, rank–nullity, Pratt, Farkas posted | Gröbner and Nullstellensatz posted through the judge |
| 3 | Racket copy | done; agrees on every file here | — |
| 4 | Native checker image | `bin/linux/jdgchk` | the Rocq theorem about the image's bytes (x86-64 semantics) |
| 5 | Metamath set.mm | registry map of the class-free cohort | import of set.mm proofs; export to Metamath format |
| 6 | Lean/Mathlib | 252 statements as ZF theorems, re-derived | translation of Lean proof terms; Int; universes as inaccessibles |
| 7 | Automation | 6 emitters, 1 written in pmp | the remaining emitters as pmp programs |
| 8 | The 5090 | rank / kernel / Smith through `extern` | the other certificate families on the GPU |
| 9 | The Book in pmp | — | ledger and desk wired to judge postings |
| 10 | Public release | this repository | Windows and Linux binaries, sources, format, receipts: included |

Gödel's half of CH is reduced in Rocq, kernel-checked, to the obligations O1–O11 (`results/ch-theorem29-plain-CH-LCH/`, `results/stage2-rocq-sigma1-complete-L2R/RESULTS-2.md`); it is not closed, so the independence of CH over ZFC is not claimed.

## Layout

| Folder | Content |
|---|---|
| `bin/` | `windows/pompetzki.exe`, `linux/pompetzki`, `linux/jdgchk` |
| `judge/` | `judge-v3.pmp`, `racket/judge.rkt`, `rocq2jdg.rkt` (untrusted converter), fault cases `mut/` |
| `rocq/` | the calculus, the checker, its soundness and Theorem 29 |
| `certificates/` | Theorem 29 and the Stage 2 arithmetic files, with mutants |
| `results/` | one folder per result after the first release, each with its `RESULTS.md` |
| `docs/` | format, soundness, quickstart, build-out plan, scope, receipts |

`MANIFEST.sha256` lists every file with its SHA-256 (`sha256sum -c MANIFEST.sha256`).

## License

The original Pompetzki code and documentation: MIT (`LICENSE`), copyright Christopher Pompetzki. Third-party material keeps its license: Metamath set.mm CC0-1.0, Lean and Mathlib Apache-2.0 (`licenses/`).
