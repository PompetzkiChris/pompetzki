# Abschluss 1.0

Abschluss 1.0 is the first release of the one system for machine-checked mathematics by Christopher Pompetzki: the cockpit, the pmp language, the pmp judge, the Racket second judge and the Book ledger.

**Start here:** unzip `Abschluss-1.0-windows-x64.zip` and run `Abschluss-1.0\Abschluss Start.exe`, a single launcher for the cockpit, the judges, the Book, the selftest and the examples. Or run `installer\Install-Abschluss.exe` next to the bundle, which installs to `%LOCALAPPDATA%\Programs\Abschluss-1.0` with a Start Menu shortcut and writes an uninstaller.

**What is in it**
- **The cockpit** (`Abschluss.exe`, Windows x64, written in pmp, rebuilt from source for this release; `build.cmd` reproduces the same bytes). It keeps ERP-style books: pmp Process logs as documents of the Computed and Certified subledgers, Rocq checks, a journal, open items, trial balance, reversals, period close by month and TSV exports. It writes new files only.
- **The judge** (`judge-v3.pmp` on the pmp interpreter) checks derivations in a Hilbert calculus for first-order logic with equality over ZF. `racket/judge.rkt` is an independent second implementation.
- **The Book** (`book\`): 9,843 postings, each accepted by both judges, in a hash chain; `book\verify-book.cmd` checks the chain and prints `CHECK OK`.
- **Examples** (`examples\`): 10 worked derivations (tautologies, equality chains, ω numerals, Farkas, rank–nullity 4×4, Smith form 2×2, Pratt certificate for 7) and 10 mutants. Both judges agree with `EXPECTED.tsv` on all 20.
- **Tools** (`tools\`): JudgeDrop (judge a file from a window), mmverify (Metamath verifier: set.mm, 251,981 statements, 47,842 proofs checked in 8.4 s, counts equal to metamath 0.198), jdg-stats, book-post.

**Downloads**
- `Abschluss-1.0-windows-x64.zip` (the bundle above, with the installer)
- `Abschluss-1.0-linux-x64.tar.gz` (the Linux pompetzki judge and its selftest)
- `Abschluss-1.0-source.zip` (sources: cockpit, pmp libraries, judge, Racket judge, Σ₁ emitter, Rocq `.v` files)
- `Abschluss-1.0-results.zip` (lane results with their receipts, and the Book)
- `SHA256SUMS.txt`: check with `certutil -hashfile <file> SHA256` (Windows) or `sha256sum -c SHA256SUMS.txt` (Linux, WSL)

**Proved**
- `check_batch` is sound for `prov`: Rocq 9.1.0, coqchk `Axioms: <none>` (`Replay3.v`).
- Both judges ACCEPT Theorem 29's replay, Con(ZFC) → Con(ZFC + ¬CH*): 4,551 theorems, 139,194 steps. An independent replay on a second machine gave identical verdicts on 176 of 176 judge rows.
- Both judges ACCEPT the Σ₁ files: 7 files, 1,656 theorems, 53,069 steps.
- Mutation testing: 298 of 300 single-step mutants rejected by both judges; the other 2 leave a valid proof of the same statement (explained in the results).

**Owed**
- The Rocq theorem that the bytes of `judge-v3.pmp` compute `check_batch`; until then a pmp verdict rests on agreement with the Racket copy.
- Gödel's half of CH; CH independence is not claimed. Stages 2 and 4–9 of the build-out: see `docs\KNOWN-LIMITS.md`.
- The pmp interpreter judges about 5.8 ms per step, so `replay-all.jdg` takes about 800 s; the cockpit's warm start on 5.4 GB of logs is about 25 s against a 10 s target.

Earlier release: [v2026.10.10](https://github.com/PompetzkiChris/pompetzki/releases/tag/v2026.10.10) (the pmp judge release). MIT licence.

Full documentation: [docs/1.0/README.md](docs/1.0/README.md), [QUICKSTART](docs/1.0/QUICKSTART.md), [USER-GUIDE](docs/1.0/USER-GUIDE.md), [KNOWN-LIMITS](docs/1.0/KNOWN-LIMITS.md), [CHANGELOG](docs/1.0/CHANGELOG.md), [Deutsch](docs/1.0/README.de.md). The README of the v2026.10.10 judge release is kept at [docs/README-v2026.10.10.md](docs/README-v2026.10.10.md).

## Credits

**Abschluss** and the Pompetzki language — Christopher Pompetzki.

Developed with Anthropic's Claude (Claude Code). Anthropic does not sponsor, endorse or review this project.
