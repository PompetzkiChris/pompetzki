# Changelog

## 1.0.0 — 2026-10-10 (tag `v1.0.0`)

The first release of Abschluss as one system: the cockpit, the pmp language, the pmp judge, the Racket second judge
and the Book ledger.

### Added

- **The cockpit, `Abschluss.exe`** (Windows x64, written in pmp, cockpit plans 1–3). ERP-style books for
  machine-checked mathematics:
  - plan 1: every configured pmp Process log read as documents of subledgers Computed (C) and Certified (K), on the
    Journal, Document, Open items and Trial balance screens, each figure equal to the run's certificate and
    confirmed by an independent Racket reading;
  - plan 2: the Jobs screen, Run again for pmp documents, the Rocq check job;
  - plan 3:
    - reversal with a reason from a list of five and an optional note (`ledger\reversals\`);
    - period close by month, in order, from the project's first month (`ledger\periods\<project>-<yyyymm>.txt`);
    - export of the current grid as a new TSV (`exports\`);
    - Settings with folder dialog, file dialog and time-zone menu; Save writes a new `config\config-<yyyymmddhhmmss>.txt`;
    - a cache of each Process log's documents (`cache\`, SHA-256 trailer); a short, corrupt, other-version or
      other-key file is ignored and the log is parsed again;
    - every write is a new file (`CREATE_NEW`); nothing is overwritten.
- Receipts of the cockpit:
  - plan 3 report (2026-09-28): suite `41 PASS, 0 FAIL`; the immutability check of spec 10.6: 5 files unchanged,
    10 new;
  - the 1.0 build (2026-10-10): 23 headless checks, 23 PASS, 10 checks not run (they open dialogs, windows or jobs);
    smoke start and close, exit 0.
- Release assets: `Abschluss-1.0-windows-x64.zip`, `Abschluss-1.0-source.zip`, `Abschluss-1.0-results.zip`,
  `SHA256SUMS.txt`.
<!--OPTIONAL:installer-->
- `Install-Abschluss.exe`, the Windows installer.
<!--OPTIONAL:verifier-->
- `abschluss-verify.exe`, which checks the assets against `SHA256SUMS.txt`.
<!--OPTIONAL:selftest-->
- `judge\selftest.cmd` and `judge\selftest.rkt`: both judges on the fault cases of `judge\mut\`, the Racket judge on `replay-B0.jdg`; 21 PASS on the 1.0 build.
<!--OPTIONAL:examples-->
- `examples\`, a first project for the cockpit.
- Documents: `README.md`, `QUICKSTART.md`, `CHANGELOG.md`, `KNOWN-LIMITS.md`.

### Included from earlier work

- The pmp judge `judge-v3.pmp`, the Racket judge `racket/judge.rkt`, the JDG1 format, `rocq2jdg.rkt`.
- `Replay2.v`, `Replay3.v`, `RpInitOk.v` and the coqchk receipts.
- `replay-all.jdg` (Theorem 29) and `sigma1/` with its files, mutants and judge results.
- `lib/ledger.pmp`, the Book's ledger.

### What this release claims

- `check_batch` is sound for `prov` (Rocq 9.1.0, coqchk `Axioms: <none>`).
- The two judges agree on 4,551 + 1,656 theorems and on every mutant tried.
- Not claimed: that the pmp bytes compute `check_batch`. That proof is owed.

## v2026.10.10 — 2026-10-10 (the pmp judge release)

<https://github.com/PompetzkiChris/pompetzki/releases/tag/v2026.10.10>

Assets: `pompetzki-windows-x64-20261010.zip`, `pompetzki-linux-x64-20261010.zip`, `pompetzki-source-20261010.zip`,
`SHA256SUMS.txt`.

- `judge/judge-v3.pmp`: checks derivations in a Hilbert calculus for first-order logic with equality over ZF, the
  function `check_batch` of `rocq/Replay2.v`.
- `bin/windows/pompetzki.exe`, `bin/linux/pompetzki` (static x86-64), `bin/linux/jdgchk` (static Linux ELF of the
  checker, JDG1 on stdin).
- `judge/racket/judge.rkt`, the independent second implementation.
- `rocq/Replay3.v`: `check_thm_ok`, `check_batch_ok`; registry `RpInitOk.REG0_ok`; Rocq 9.1.0, coqchk
  `Axioms: <none>`.
- Results (2026-10-09), each with how it was checked:
  - Theorem 29, Con(ZFC) → Con(ZFC + ¬CH\*): `replay-all.jdg`, 4,551 theorems, 139,194 steps; both judges ACCEPT,
    coqchk `Axioms: <none>`;
  - Cohen's half over the plain CH statement (`AlignCH.con_zfc_con_notch_plain`): both judges ACCEPT the alignment
    file, coqchk clean;
  - Σ₁-completeness proved once in Rocq (`bounded_complete`, `sigma1_complete`): coqchk `Axioms: <none>`;
  - conservativity of definitions (`gam_pure_conservative`): recursive coqchk `Axioms: <none>`;
  - arithmetic of ω as ZF theorems: 7 files, 1,656 theorems, 53,069 steps; both judges ACCEPT; 70 mutants, all
    REJECT;
  - derived rules LRAT, Smith normal form, rank–nullity over Q, Pratt primality, Farkas infeasibility: 19 originals
    × both ACCEPT; 186 mutants × both REJECT;
  - LRAT corpus (CaDiCaL, 35 instances): 35 LRAT ACCEPT; 3 JDG files, both judges ACCEPT;
  - Pratt corpus (all 78,498 primes below 10⁶ and others): the checker accepts every certificate; JDG for 7, 13, 23;
  - Farkas `cyclic-k02`: both judges ACCEPT;
  - 252 statements of the `import Mathlib` environment as ZF theorems (`L6-nat.jdg`, 345 theorems, 37,714 steps):
    both judges ACCEPT;
  - automation: 6 emitter files, both judges ACCEPT; 42 of 42 mutants rejected;
  - RTX 5090 through pmp `extern`: exact integer rank, kernel and Smith form; both judges ACCEPT; 30 of 30 mutants
    rejected;
  - Metamath set.mm: 167 `ax-`/`df-` labels of the 5,757-assertion class-free cohort mapped to the registry; 10
    route-check files, both judges ACCEPT.
- The ten-stage table with what is owed.
- `MANIFEST.sha256` over every file. License MIT for the original code and documentation.

## coo-final-v2-20261009 (prerelease)

<https://github.com/PompetzkiChris/pompetzki/releases/tag/coo-final-v2-20261009>

- Published by GitHub at 2026-10-10T06:49:46Z. The deadline snapshot's notes name it the full staged candidate and
  component overlays.

## deadline-snapshot-20261010 — 2026-10-10 (prerelease)

<https://github.com/PompetzkiChris/pompetzki/releases/tag/deadline-snapshot-20261010>

- The gathered archive `PMP-deadline-snapshot-20261010-v1.zip` (1,010,379,345 bytes, 2,428 members) was rejected by
  GitHub with HTTP 404 and is not an asset of the release; `SHA256SUMS-DEADLINE.txt` and the assembly receipt
  attached there describe that archive.
- The downloadable packages are `PMP-current-sources-and-evidence-20261010-v2.zip` and
  `Book-0127b-prejoin-portable-20261010-v1.zip`; they check against `SHA256SUMS-PUBLIC-v2.txt`.
- The release states that the original ten-part project remains unfinished.
