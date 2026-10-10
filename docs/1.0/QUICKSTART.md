# Abschluss 1.0 — the first ten minutes

Windows x64. On Linux and WSL only the judge runs (step 4c).

## 1. Download and check the hash (2 minutes)

From <https://github.com/PompetzkiChris/pompetzki/releases/tag/v1.0.0> download `Abschluss-1.0-windows-x64.zip`
and `SHA256SUMS.txt` into one folder. Then, in that folder:

```
certutil -hashfile Abschluss-1.0-windows-x64.zip SHA256
```

The printed hash must equal the line for that file in `SHA256SUMS.txt`. On Linux or WSL:
`sha256sum -c SHA256SUMS.txt --ignore-missing`.

<!--OPTIONAL:verifier-->
Or run `abschluss-verify.exe` in the download folder; it checks the assets against `SHA256SUMS.txt`.

## 2. Install (1 minute)

<!--OPTIONAL:installer-->
Run `Install-Abschluss.exe`.

Or unzip `Abschluss-1.0-windows-x64.zip` into a folder of your own, for example `C:\Abschluss`.

## 3. Selftest (1 minute)

<!--OPTIONAL:selftest-->
In the unzipped folder run `judge\selftest.cmd`: both judges run on the fault cases of `judge\mut\` and the Racket judge on `judge\replay-B0.jdg`; each check prints `PASS` or `FAIL`, the last line is `TOTAL n passed, m failed`, and the exit code is 0 only when every check passes.

The selftest needs Racket: `C:\Program Files\Racket\racket.exe`, or set the variable `RACKET` to your `racket.exe`.
`judge\selftest.cmd full` adds the pmp judge on `replay-B0.jdg` (about 100 s).

## 4. Judge one file by hand

### 4a. Windows (PowerShell), in the unzipped folder (2 minutes)

```
cd judge
..\pompetzki.exe judge-v3.pmp replay-B0.jdg
racket racket\judge.rkt replay-B0.jdg
```

`replay-B0.jdg` is Theorem 29's registry with batch 0. Each judge prints `ACCEPT` (823 theorems, 24,968 steps,
registry 706 → 1,529) and exits 0. The pmp judge takes about 100 s, the Racket judge about 1 s.

### 4b. The full certificate of Theorem 29 (14 minutes)

`judge\replay-all.jdg` is the certificate of Theorem 29, Con(ZFC) → Con(ZFC + ¬CH\*), all 11 batches:

```
cd judge
..\pompetzki.exe judge-v3.pmp replay-all.jdg
racket racket\judge.rkt replay-all.jdg
```

Both judges print `ACCEPT` with registry 706, theorems 4,551, steps 139,194, final registry 5,257, and exit 0.
The recorded pmp run took 801 s (`run-v3-all.txt`); the Racket judge takes 3.32–3.53 s.
A refused file prints `REJECT` with the theorem and step, and exits 1.

### 4c. Linux or WSL, from the `v2026.10.10` repository root

The 1.0 zip carries no Linux binaries. The `v2026.10.10` release has them, with the certificate at
`certificates/theorem29/replay-all.jdg`:

```
cd judge
../bin/linux/pompetzki judge-v3.pmp ../certificates/theorem29/replay-all.jdg
racket racket/judge.rkt ../certificates/theorem29/replay-all.jdg
../bin/linux/jdgchk < ../certificates/theorem29/replay-all.jdg
```

A stop with `gosub: too deep` or `LIMIT a memory block is full` is a resource limit of the pmp interpreter, not a
refusal (see `KNOWN-LIMITS.md`).

## 5. Open the books (3 minutes)

Started without an argument, `Abschluss.exe` reads its configuration from `C:\ClaudeOutput\abschluss\config`
(recorded in the app hand-in's status, 2026-10-10 03:11 EDT). `config-sample\` in the zip holds a sample
configuration file.

1. Start `Abschluss.exe`. Left: the navigation tree. Right: the toolbar (Back, Refresh, Export and the screen's own
   buttons), the grid, and the status bar.
2. In the tree, open **Settings**. Add a project root with the folder dialog: a pmp program folder with its Process
   logs, a Lean project (a folder with `lakefile.toml` or `lakefile.lean`, and `lean-toolchain`), or a Rocq folder.
   Pick the time zone from the menu. **Save** writes a new `config\config-<yyyymmddhhmmss>.txt`, reloads and
   rebuilds the tree.
3. Press **Refresh**. Every source is read; unchanged sources come from the cache. The status bar shows the progress.
   On the reference books (266 logs, 6,038 documents, 5.4 GB) a start from the cache took 24,578–26,047 ms in the
   plan 3 report (2026-09-28); the first read with an empty cache took 500,891 ms on that report's earlier code
   (commit `4eb8201`).
4. Open **Journal**: one row per document (number, kind, date, project, source, status, items, cost, model,
   session). Click a column header to sort. Type in the filter box to filter. Double-click a row to open it.
5. **Document** shows a header grid and an items grid, with **Show source**, **Open file**, **Run again** and
   **Reverse**.
6. **Trial balance** shows the project's figures. Double-click any figure to see its lines.
7. **Export** writes the current grid as a new TSV file in `exports\`.
8. Under the project, **Periods** lists the months. **Close period** closes the earliest ended open month and
   writes `ledger\periods\<project>-<yyyymm>.txt`. It stays disabled, with its reason, while a task is red.

The cockpit never changes or deletes a file. Every file it writes, its cache included, is opened with `CREATE_NEW`,
and a correction is a reversal document in `ledger\reversals\`.

<!--OPTIONAL:examples-->
The `examples` folder of the zip can be added in Settings as a first project root.

## Next

- `README.md`: what Abschluss is, what is proved, what is owed.
- `KNOWN-LIMITS.md`: what does not work yet.
