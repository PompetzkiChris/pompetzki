Abschluss 1.0 is the first release of the one system for machine-checked mathematics by Christopher Pompetzki: the cockpit, the pmp language, the pmp judge, the Racket second judge and the Book ledger.

**The cockpit** (`Abschluss.exe`, Windows x64, written in pmp) keeps ERP-style books: pmp Process logs as documents of the Computed and Certified subledgers, Rocq checks, a journal, open items, trial balance, reversals, period close by month, and TSV exports. It writes new files only; nothing is overwritten. **The judge** (`judge-v3.pmp` on the pmp interpreter) checks derivations in a Hilbert calculus for first-order logic with equality over ZF. `racket/judge.rkt` is an independent second implementation.

**Downloads**
- `Abschluss-1.0-windows-x64.zip`: the cockpit, the pmp interpreter and judge, the Racket judge, `judge\selftest.cmd`, and Theorem 29's certificate `judge\replay-all.jdg`
- `Abschluss-1.0-source.zip`: the sources
- `Abschluss-1.0-results.zip`: the results and their receipts
- `SHA256SUMS.txt`: check with `certutil -hashfile <file> SHA256` (Windows) or `sha256sum -c SHA256SUMS.txt --ignore-missing` (Linux, WSL)
<!--OPTIONAL:installer-->
Install with `Install-Abschluss.exe`, or unzip and run `Abschluss.exe`.
<!--OPTIONAL:selftest-->
Run `judge\selftest.cmd` (needs Racket): each check prints `PASS` or `FAIL`, and the exit code is 0 only when every check passes.

**Proved**
- `check_batch` is sound for `prov`: Rocq 9.1.0, coqchk `Axioms: <none>` (`Replay3.v`).
- Both judges ACCEPT Theorem 29's replay, Con(ZFC) → Con(ZFC + ¬CH*): 4,551 theorems, 139,194 steps.
- Both judges ACCEPT the Σ₁ files: 7 files, 1,656 theorems, 53,069 steps. Every mutant tried is REJECTed by both.

**Owed**
- The Rocq theorem that the bytes of `judge-v3.pmp` compute `check_batch`; until then a pmp verdict rests on agreement with the Racket copy.
- Gödel's half of CH (obligations O1–O11); CH independence is not claimed. Stages 2 and 4–9 of the build-out: see `KNOWN-LIMITS.md`.
- Linux runs the judge only, from the v2026.10.10 binaries. The cockpit's warm start on 5.4 GB of logs is 24,578–26,047 ms; the 10 s target is not met.

Earlier: [v2026.10.10](https://github.com/PompetzkiChris/pompetzki/releases/tag/v2026.10.10) (the pmp judge release), [coo-final-v2-20261009](https://github.com/PompetzkiChris/pompetzki/releases/tag/coo-final-v2-20261009) and [deadline-snapshot-20261010](https://github.com/PompetzkiChris/pompetzki/releases/tag/deadline-snapshot-20261010) (prereleases).
