# Abschluss 1.0 — known limits

Each item below is owed or does not work yet. Figures are the ones recorded in the receipts named.

## 1. Owed on the proof side

| Stage | Owed |
|---|---|
| 1 | The Rocq theorem that the bytes of `judge-v3.pmp`, run under the pmp semantics, compute `check_batch`. Until it is closed, a pmp verdict rests on its agreement with the Racket copy. |
| 2 | Gröbner and Nullstellensatz posted through the judge. |
| 4 | The Rocq theorem about the native checker image's bytes (x86-64 semantics). |
| 5 | Import of Metamath set.mm proofs; export to Metamath format. |
| 6 | Translation of Lean proof terms; Int; universes as inaccessibles. The 252 Lean/Mathlib statements in `v2026.10.10` are re-derived statements, not translated proofs. |
| 7 | The remaining derivation emitters as pmp programs. |
| 8 | The other certificate families on the RTX 5090. |
| 9 | The Book in pmp: the ledger and the desk wired to judge postings. `lib/ledger.pmp` and the cockpit exist; the cockpit does not post judge results. |

- **CH.** Theorem 29 gives Con(ZFC) → Con(ZFC + ¬CH\*), Cohen's half. Gödel's half, through L, is reduced in Rocq,
  kernel-checked, to the obligations O1–O11 and is not closed. The independence of CH over ZFC is not claimed.
- **Lean side.** AbschlussCore and the agent postings are on Lean v4.28.0, which has 3 known kernel exploits. Every
  such posting carries "replay on a fixed kernel owed".

## 2. Platforms

- **Windows x64 first.** The cockpit runs on Windows x64 only. An ARM Mac is a later port.
- **Linux: the judge only.** The pmp interpreter runs on x86-64 Linux and WSL; the static binaries `pompetzki` and
  `jdgchk` were published in `v2026.10.10` under `bin/linux/`. The 1.0 zip carries no Linux binaries. The cockpit
  does not run on Linux.
- **Racket.** The second judge and the selftest need a Racket installation. `judge\selftest.cmd` uses
  `C:\Program Files\Racket\racket.exe` unless the variable `RACKET` names another `racket.exe`.
- **Selftest on Windows only.** The selftest is `judge\selftest.cmd` with `judge\selftest.rkt`; there is no
  `selftest.sh`.

## 3. The judge

- **Resource stops are not refusals.** The pmp interpreter stops with `gosub: too deep` on formulas nesting numerals
  above 38, and with `LIMIT a memory block is full` on registries above 1,091 entries. On those files the Racket
  judge ACCEPTs. The stop is a resource limit of the interpreter, not a REJECT.
- **Speed.** The interpreter takes 5.8 ms per step; the recorded pmp run on the full Theorem 29 replay took 801 s
  (`run-v3-all.txt`), the Racket judge 3.32–3.53 s. A native judge `judge-v3.exe` (pmpc) ran the full replay in
  0.57 s (4.1 µs per step); it is not in this release.

## 4. The cockpit

Recorded in the cockpit plan 3 report (`abschluss/REPORT.md` in `Abschluss-1.0-source.zip`, 2026-09-28), the design,
and the 1.0 build's receipts (2026-10-10).

- **It reads and reports.** It does not yet post pmp claims into Lean (account determination and a Lean-side
  certificate checker are a later spec).
- **Configuration folder.** Started without an argument, `Abschluss.exe` reads its configuration from
  `C:\ClaudeOutput\abschluss\config` (app hand-in status, 2026-10-10 03:11 EDT).
- **Warm start over 10 s.** On the reference books (266 logs, 6,038 documents, 5.4 GB) a start from the cache took
  24,578–26,047 ms; the first read with an empty cache took 500,891 ms on the report's earlier code (`4eb8201`). The
  target of under 10 s is not met. Cause, measured: in `pompetzki.exe` a word is found in time proportional to the
  number of words bound before it, and every `goto`/`gosub` scans all labels; with the app's about 1,040 labels a
  taken jump costs about 3 µs. Route: a separate interpreter with names and labels resolved once (task T33).
- **First Journal build.** On the reference books it takes 17 s with no message loop, and Windows marks the window
  Not Responding meanwhile.
- **Clicks during the ledger build** are dropped, not queued. Click again after the build.
- **Reverse on right-click.** The plan 3 report recorded it as not hooked. The 1.0 source wires it: plan 2a's
  right-click menu on a C or K document offers "Reverse...", which calls plan 3's reversal (`abschluss.pmp`). No 1.0
  receipt exercises that path; the Reverse button on the Document screen is the path the plan 3 report recorded as
  working.
- **Checks not run on the 1.0 build.** 23 headless checks pass; 10 were not run because they open dialogs, windows or
  files, start jobs, or need Lean/Rocq fixtures: dialogs, grid-show, open, jobs, leanjob, rocqjob, rdlean, rcver,
  abort3, progchg.
- **General ledger code.** The 1.0 source carries plan 6's General ledger screen (`lib\gl6.pmp`, `lib\rdlean.pmp`);
  no 1.0 receipt exercises it, and it is not claimed.
- **Dark mode.** The status bar strip stays light; the headers and lists are dark.
- **Period documents** list the Lean, Rocq and token items as "not read by this version".
- **Settings.** Typing is limited to a reversal note; coqarg and project lines are kept as they are. A coqarg is
  changed only in the configuration file itself.
- **Claim shapes.** Plan 3's reader marked 449 of the 6,038 real documents Error, "certificate and log disagree on
  the claims", for claim lines missing from spec §5.2 (claims with a rule and no text; `established by rule
  noninjective with witness 1`). The §5.2 amendment of plan 4 defines how these lines are read. The 1.0 reader
  (`lib\rdpmp.pmp`) carries plan 4's claim grammar and passes its fixture checks against the oracle reader; no 1.0
  receipt gives the count of Error documents on the reference books under it.
- **Cache.** A cache file whose SHA-256 trailer is valid but whose string offsets or item indices point outside its
  areas is not bounds-checked field by field. Only a crafted file can have that; a damaged one fails the checksum.
- **`lib\hot.pmp`** is generated from static counts. After code changes regenerate it
  (`racket tests/hotwords.rkt > lib/hot.pmp`). A hot word missing from it is found later: slower, never wrong.
- **Out of scope of this cockpit:** posting pmp claims into Lean; token-budget availability control; an MRP run and
  an automatic clearing run over open items; several users and permissions; transcripts without usage fields
  (shown as the cost center "no usage data").

## 5. The interpreter

- `print` of an integer word crashes `pompetzki.exe` (exit 139, no output): `set x const 5` then `print x`.
  Reproduced on the 1.0 zip's `pompetzki.exe` (sha256 `ccf83592…3bec`) at 2026-10-10 03:10:55 EDT: segmentation
  fault, exit 139.
