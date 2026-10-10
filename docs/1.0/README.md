# Abschluss 1.0

Abschluss is one system for the mathematician who keeps machine-checked mathematics as books, by Christopher
Pompetzki. This is release 1.0.0 (tag `v1.0.0`) of `PompetzkiChris/pompetzki`, 2026-10-10.

The name is the accounting close and the closure of a set. Good proofs are good bookkeeping and closing.

## What Abschluss is

| Part | What it is |
|---|---|
| The cockpit, `Abschluss.exe` | ERP-style books for machine-checked mathematics on Windows x64, written in pmp. Every action is a click. |
| The pmp language | Christopher Pompetzki's exact linear-algebra language. `pompetzki.exe` (Windows, in this zip) and `pompetzki` (static Linux x86-64, in `v2026.10.10`) are its interpreters. Integers are exact. |
| The pmp judge, `judge\judge-v3.pmp` | Checks derivations in a Hilbert calculus for first-order logic with equality over ZF: the function `check_batch` of `Replay2.v`. Input format: JDG1. |
| The Racket second judge, `judge\racket\judge.rkt` | An independent implementation of the same function, written from the rule text. |
| The Book ledger, `lib\ledger.pmp` | The Book's ledger: tables, status rules, materiality, aging, trial balance, costs. |

### The cockpit

The cockpit keeps the books the way an accountant keeps them.

- **Ledgers.** General ledger: Lean 4 projects. Subledgers: **Computed** (C) and **Certified** (K) from pmp Process
  logs, **Proved** (P) from Rocq checks. Token usage by the models is the money.
- **Documents.** One document per source event, each with a number:

  | Kind | Letter | One per |
  |---|---|---|
  | Lean commit | G | commit touching `.lean` files |
  | pmp run | K (with claims) or C (without) | `==== run` block in a Process log |
  | Rocq check | P | check job |
  | Reversal | R | reversal |
  | Period close | A | closed period |

- **Statuses.** Each status is a word and a color: Closed, Certified, Proved (green); Computed, Checked, Reversed
  (grey); Unpriced, Qualified, Annotation, Impaired (yellow); Open, Rejected, Incomplete, Error (red). A line is green
  only after a kernel or a pmp rule has accepted it.
- **Screens.** The design names 13: Cockpit (tasks with lights), Journal, Document, General ledger, Open items (with
  materiality, age and aging buckets 0–7, 8–30, 31–90, over 90 days), Trial balance, Axioms, Bill of materials,
  Costs, Vendors, Jobs, Periods, Settings. Every figure drills down to the source lines that produce it. Built so
  far: plan 1, every configured pmp Process log read as documents (Journal, Document, Open items, Trial balance),
  each figure equal to the run's certificate and confirmed by an independent Racket reading; plan 2, Jobs, Run
  again and the Rocq check job; plan 3, reversal, period close, export, Periods and Settings.
- **Period close.** Closes the project's earliest open month; months close in order, and only ended months. It writes
  `ledger\periods\<project>-<yyyymm>.txt`: the trial balance, the tasks with their lights, every document number
  with its source sha256, the reversals, the interpreter names and the configuration file. It is disabled, with its
  reason, while a task is red. Documents of a closed period show locked.
- **Reversals.** The reason is picked from a list of five (wrong statement, wrong certificate, superseded, refuted by
  counterexample, run in error), with an optional note. The reversal is a new file in `ledger\reversals\`; the
  document becomes Reversed.
- **Exports.** The current grid as a new TSV file in `exports\`.
- **Nothing is overwritten.** The cockpit opens every file it writes with `CREATE_NEW`. Corrections are reversal
  documents. Saving the settings writes a new `config\config-<yyyymmddhhmmss>.txt`; the newest applies.

The cockpit reads and reports. It does not yet post pmp claims into Lean. Design:
`abschluss/docs/specs/2026-09-27-cockpit-design.md` in `Abschluss-1.0-source.zip`.

## What is in the download

| Asset | Content |
|---|---|
| `Abschluss-1.0-windows-x64.zip` | the cockpit, the pmp interpreter, the pmp judge and the Racket judge (`judge\`), the judge selftest `judge\selftest.cmd`, Theorem 29's certificate `judge\replay-all.jdg`, a sample configuration (`config-sample\`) |
| `Abschluss-1.0-source.zip` | the sources |
| `Abschluss-1.0-results.zip` | the results and their receipts |
| `SHA256SUMS.txt` | the SHA-256 of each asset |

The 1.0 zip carries no Linux binaries. The Linux interpreter `pompetzki` and the native checker `jdgchk` are in the
`v2026.10.10` release.

Earlier releases on the same repository:

- `v2026.10.10`, the pmp judge release: <https://github.com/PompetzkiChris/pompetzki/releases/tag/v2026.10.10>
- `coo-final-v2-20261009`, a prerelease: <https://github.com/PompetzkiChris/pompetzki/releases/tag/coo-final-v2-20261009>
- `deadline-snapshot-20261010`, a prerelease snapshot of the work as it stood:
  <https://github.com/PompetzkiChris/pompetzki/releases/tag/deadline-snapshot-20261010>

## Install

<!--OPTIONAL:installer-->
Run `Install-Abschluss.exe`.

Or unzip `Abschluss-1.0-windows-x64.zip` into a folder and run `Abschluss.exe` from there.

The Racket judge and the selftest need Racket (`racket.exe`).

## Verify the download

Windows (cmd or PowerShell), in the download folder:

```
certutil -hashfile Abschluss-1.0-windows-x64.zip SHA256
```

Compare the printed hash with the line for that file in `SHA256SUMS.txt`.

Linux or WSL:

```
sha256sum -c SHA256SUMS.txt --ignore-missing
```

<!--OPTIONAL:verifier-->
`abschluss-verify.exe` checks the downloaded assets against `SHA256SUMS.txt`.

## Selftest

<!--OPTIONAL:selftest-->
Run `judge\selftest.cmd` (Windows, needs Racket): both judges run on the fault cases of `judge\mut\` and the Racket judge on `judge\replay-B0.jdg`; each check prints `PASS` or `FAIL`, and the exit code is 0 only when every check passes.

The judge run on Theorem 29's replay, by hand, is in `QUICKSTART.md`.

## What is proved

- **The checker is sound.** In Rocq 9.1.0, with coqchk `Axioms: <none>`: `check_batch` accepts only derivable
  theorems (`Replay3.v`: `check_thm_ok`, `check_batch_ok`; registry `RpInitOk.REG0_ok`). So `check_batch` is
  sound for `prov`.
- **Two independent judges agree.** The pmp judge and the Racket judge both ACCEPT:
  - Theorem 29's replay, `replay-all.jdg`: Con(ZFC) → Con(ZFC + ¬CH\*), 4,551 theorems, 139,194 steps;
  - the Stage 2 Σ₁ files (arithmetic of ω as ZF theorems): 7 files, 1,656 theorems, 53,069 steps.
- **Mutants are rejected.** Every mutated copy tried, including the 70 mutants of the Σ₁ files, is REJECTed by both
  judges.

Not claimed:

- That the bytes of `judge-v3.pmp`, run under the pmp semantics, compute `check_batch`. The Rocq proof is open and
  owed. Until it is closed, a pmp verdict rests on its agreement with the Racket copy.
- The independence of CH over ZFC. Theorem 29 is Cohen's half. Gödel's half, through L, is owed; it is reduced in
  Rocq, kernel-checked, to the obligations O1–O11.

## What is owed

The ten stages of the build-out. Stages 1–8 are as published in `v2026.10.10`; stages 9 and 10 include this
release.

| # | Stage | Delivered | Owed |
|---|---|---|---|
| 1 | Judge v0 and its Rocq theorem | `check_batch` sound for `prov` (Replay3, coqchk none); Gam → ZFpure for pure formulas (CX3); `judge/mut` refused by both judges | the Rocq theorem that the bytes of `judge-v3.pmp`, run under the pmp semantics, compute `check_batch` |
| 2 | Σ₁-completeness and derived rules | Σ₁-completeness in Rocq; ω arithmetic; LRAT, Smith, rank–nullity, Pratt, Farkas posted | Gröbner and Nullstellensatz posted through the judge |
| 3 | Racket copy | done; agrees on every file of `v2026.10.10` | — |
| 4 | Native checker image | `bin/linux/jdgchk` | the Rocq theorem about the image's bytes (x86-64 semantics) |
| 5 | Metamath set.mm | registry map of the class-free cohort | import of set.mm proofs; export to Metamath format |
| 6 | Lean/Mathlib | 252 statements as ZF theorems, re-derived | translation of Lean proof terms; Int; universes as inaccessibles |
| 7 | Automation | 6 emitters, 1 written in pmp | the remaining emitters as pmp programs |
| 8 | The 5090 | rank / kernel / Smith through `extern` | the other certificate families on the GPU |
| 9 | The Book in pmp | `lib/ledger.pmp`; cockpit plans 1–3 | the ledger and the desk wired to judge postings |
| 10 | Public release | `v2026.10.10`; this release | — |

Also owed:

- The Lean side (AbschlussCore, agent postings) is on Lean v4.28.0, which has 3 known kernel exploits. Every such
  posting carries "replay on a fixed kernel owed".
- Gödel's half of CH (obligations O1–O11).

The full list, with the cockpit's own open items and the platform limits: `KNOWN-LIMITS.md`.

## More

- `QUICKSTART.md`: the first ten minutes.
- `CHANGELOG.md`: what changed, release by release.
- `KNOWN-LIMITS.md`: what is owed and what does not work yet.

## License

The original Pompetzki code and documentation: MIT (`LICENSE`), copyright Christopher Pompetzki. Third-party material
keeps its license: Metamath set.mm CC0-1.0, Lean and Mathlib Apache-2.0.

The method (exact linear algebra, one certificate per run, the Finite Data Principle, Theorem 21.1) is Christopher
Pompetzki's.
