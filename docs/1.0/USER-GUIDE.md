# Abschluss cockpit — User Guide (draft for 1.0)

> **Draft status.** Drafted by GitHub Copilot (Copilot CLI 1.0.95, model claude-sonnet-5.5, no tools, run 02:58:30–03:00:10 EDT) from three files only; checked line by line against those files by the Claude manager (A51 Copilot/Cowork), 2026-10-10 03:01:22 EDT. Corrections are listed in `CHECK-a.md`; the unedited draft is `USER-GUIDE.copilot-raw.md`. This file (v2) supersedes `USER-GUIDE.md`, whose two Sources lines were damaged by the manager's script.
> REPORT.md is the plan-3 report of 2026-09-28. Before this guide ships, compare every "Built" line with the Abschluss.exe actually handed in under `app\` for 1.0: plans 2 and 4 may have landed since, and nothing here was checked against that build.

This draft uses only the three source documents listed under "Sources". Three kinds of statement are marked:
- **Built** means REPORT or SCOPE confirms it.
- **Designed, not confirmed built** means only the design file states it.
- **Owed** means a source lists it as not done.

The REPORT file describes plan 3 only. It names plan 1 as the base and plan 2 as a separate branch that has not been merged.

## 1. What the cockpit is

The design names the application "Abschluss", for the accounting close and the closure of a set. [design §Abschluss: the closing cockpit — design]

The stated goal is the best mathematics software there is, free. The first user is Terence Tao. [design §1. Agreed understanding]

The interface works like an ERP, with every action done by clicking. It is designed for an accountant. [design §1. Agreed understanding]

The ledger structure is:
- General ledger: Lean 4.
- Subledgers: Computed (C), Certified (K) and Proved (P). [design §1. Agreed understanding]

The money tracked is token usage by the models. [design §1. Agreed understanding]

The application is written in pmp and runs on Windows x64 first. [design §1. Agreed understanding]

The design says the cockpit reads and reports. It does not post pmp claims into Lean. [design §1. Agreed understanding]

SCOPE lists "Stage 9, the Book in pmp" with the parts ledger, axiom trace and negative ledger. It states that `lib/ledger.pmp` and cockpit plans 1–3 exist, and that they are not wired to judge postings. [SCOPE §1. The one system (the Monolith) and where each part stands]

SCOPE calls the earlier Lean-side ledger "AbschlussCore, agent postings". [SCOPE §1. The one system (the Monolith) and where each part stands]

**Built state.**
- REPORT describes branch `cockpit-plan-3`. It is local and not pushed, and its worktree is `C:\ClaudeOutput\abschluss-plan3`. [REPORT §Abschluss plan 3 — report]
- It has not been merged with plan 2. A merge check against plan 2's `044ee3f` showed no conflicts. It must be rerun against plan 2's head before merging. [REPORT §9. Merge notes for plan 2]

**Disagreement between the sources.**
- The design makes the Lean 4 project the general ledger. [design §1. Agreed understanding]
- SCOPE names the pmp judge as "the only judge of the Book" and the Lean side as the "earlier ledger". [SCOPE §1. The one system (the Monolith) and where each part stands]
- The sources do not state how the two fit together.

## 2. Design rules the cockpit follows (designed, not confirmed built)

| Rule | What the cockpit does |
|---|---|
| Belegprinzip (no posting without a document) | Every line comes from a source: a Process log run, a Lean declaration, a Rocq check record or a transcript line. [design §2. Design rules (German bookkeeping law, applied)] |
| Nachprüfbarkeit | Every figure drills down to the source lines that produce it. [design §2. Design rules (German bookkeeping law, applied)] |
| Radierverbot | The cockpit writes new files only (`CREATE_NEW`). Corrections are reversal documents. [design §2. Design rules (German bookkeeping law, applied)] |
| Vorsicht, Imparität | Red and yellow spread to every dependent at once. [design §2. Design rules (German bookkeeping law, applied)] |
| Realisation | A line is green only after a kernel or a pmp rule has accepted it. [design §2. Design rules (German bookkeeping law, applied)] |

The Radierverbot rule is built for the plan-3 writers. The immutability test (spec 10.6) passed with "5 files unchanged, 10 new". [REPORT §2. Verification (fresh runs on the final code unless marked)]

## 3. Screens and views

### 3.1 Layout

The design's layout is:
- A navigation tree on the left.
- On the right, a toolbar (Back, Refresh, Export, plus the screen's own buttons), a grid, and a status bar with a coloured message.
- In every grid: clicking a column header sorts, double-clicking drills down, right-clicking opens the actions, and a filter box filters as you type. A totals line shows at the bottom. [design §7. Screens (all clicking)]
- The theme follows the Windows light/dark setting. Every status shows as a coloured icon plus its word. [design §7. Screens (all clicking)]

**Built (plan 3).**
- List headers are dark in dark mode. [REPORT §1. What was built]
- The status bar strip stays light in dark mode. [REPORT §5. Deferred minors]
- Right-click is not wired in the plan-3 branch (see section 4). [REPORT §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)]

### 3.2 Navigation tree

The design's tree lists all projects, then each project with its screens, then Jobs, Vendors, Periods and Settings. [design §7. Screens (all clicking)]

In the plan-3 branch, Periods sits under each project. Jobs comes before Periods only once plan 2 is merged. [REPORT §8. Every hook line in `abschluss.pmp` (diff against plan 1, `ce99acb`)]

### 3.3 The screens

The design lists thirteen screens. Their status is:

| # | Screen | Design | Status |
|---|---|---|---|
| 1 | Cockpit | Per project and for all projects. A list of tasks with lights, each clickable to its lines (section 6). [design §7. Screens (all clicking)] | Period close reads "tasks with lights and details" in the plan-3 branch (see section 6). A full Cockpit screen is not confirmed built. |
| 2 | Journal | All documents. Columns: number, kind, date, project, source, status, items, cost in USD, model, session. [design §7. Screens (all clicking)] | Built. On the real books it showed 6,038 rows. [REPORT §2. Verification (fresh runs on the final code unless marked)] |
| 3 | Document | A header grid (field, value) and an items grid. Buttons: Show source, Open file, Run again / Check again, Reverse. [design §7. Screens (all clicking)] | Built. The real-books probe showed 29 rows, including `Period closed | no` and `Reversed by | -`. [REPORT §2. Verification (fresh runs on the final code unless marked)] The Reverse action button works on this screen. [REPORT §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)] |
| 4 | General ledger | All GL lines. Columns: name, kind, module, status, axioms, dependents, uses, posted, by. [design §7. Screens (all clicking)] | Designed, not confirmed built. REPORT says the Lean items are "not read by this version". [REPORT §1. What was built] |
| 5 | Open items | GL Open lines, pmp claims not established, programs whose latest run failed, and Rocq files Rejected. Columns: item, type, project, materiality, age, bucket, owner. Default sort is materiality, descending. [design §7. Screens (all clicking)] | Open items exist in the plan-3 branch: a reversed document leaves Open items. [REPORT §1. What was built] The GL and Rocq parts are designed, not confirmed built. |
| 6 | Trial balance | Per project: GL (closed, open, impaired, qualified, error), K (established, not established, annotations), C (computed runs), P (proved, qualified, rejected), suspense and axiom classes. Every figure drills down. [design §7. Screens (all clicking)] | The period document contains a trial balance (see section 6). The screen itself is not confirmed in REPORT. |
| 7 | Axioms | The trial balance of axioms, per project. [design §7. Screens (all clicking)] | Designed, not confirmed built. |
| 8 | Bill of materials | A tree from theorem down to leaves, with statuses. "Path to suspense" expands the chain to the `sorry` a line inherits. [design §7. Screens (all clicking)] | Designed, not confirmed built. |
| 9 | Costs | Per project and period, one row per model: input, cache write, cache read, output, USD, with closed lines and cost per closed line below. [design §7. Screens (all clicking)] | Designed, not confirmed built. REPORT says the token items are "not read by this version". [REPORT §1. What was built] |
| 10 | Vendors | A model scorecard: sessions, tokens, USD, closed lines, linked runs, rejected linked runs, rejection rate, cost per closed line. [design §7. Screens (all clicking)] | Designed, not confirmed built. |
| 11 | Jobs | Running and finished jobs: kind, project, start, duration, exit code, status. Double-click shows the log. Cancel is available. [design §7. Screens (all clicking)] | Not in the plan-3 branch. REPORT refers to Jobs as arriving with plan 2. [REPORT §8. Every hook line in `abschluss.pmp` (diff against plan 1, `ce99acb`)] |
| 12 | Periods | Per project: period, open or closed, closing date, qualifications. Double-click opens the period document. [design §7. Screens (all clicking)] | Built, for each project and for all projects. It has a periods grid and a tasks grid. [REPORT §1. What was built] |
| 13 | Settings | Projects and roots, tool paths, transcript roots, the price list and the time zone. Saving writes a new configuration file. [design §7. Screens (all clicking)] | Built. See section 7. |

**Numbering.**
- REPORT numbers Periods as screen 13 and Settings as screen 14 in the plan-3 code. Screens 11 and 12 are plan 2's. [REPORT §4, Merge fit ruling: "screen dispatch 13/14 beside plan 2's 11/12"] [REPORT §9. Merge notes for plan 2; §8. Every hook line in `abschluss.pmp` (diff against plan 1, `ce99acb`)]
- The design numbers Periods 12 and Settings 13. [design §7. Screens (all clicking)]
- The user-visible names are the same. Only the internal numbering differs.

**Cockpit task lights (designed, not confirmed built).** The design lists these tasks:
- Lean build: green or red.
- Suspense (`sorryAx` users): 0 is green.
- Open items: 0 is green.
- Axioms: the standard three only is green; otherwise yellow.
- The latest run of every pmp program discharged is green; Rejected or Incomplete is red.
- Every `.v` file's latest check Proved or Qualified is green; unchecked is yellow; Rejected is red.
- All sessions of the period priced is green; any Unpriced is yellow. [design §7. Screens (all clicking)]

## 4. Menus and commands

The sources do not describe a menu bar. [design §7. Screens (all clicking)]

**Toolbar buttons.**
- Back, Refresh and Export are designed for the toolbar, plus each screen's own buttons. [design §7. Screens (all clicking)]
- REPORT confirms Export and an action button built in plan 3. They are controls 131 and 132, with a note label and note box at 133 and 134. The toolbar sits to the right of plan 2's filter box. [REPORT §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)]

**Right-click menu.**
- The design says right-clicking a grid opens the actions. [design §7. Screens (all clicking)]
- REPORT says plan 2 owns the right-click menu (`AHRCLICK`). Plan 3's "Reverse…" right-click entry (`AZRCLICK`) is not hooked.
- **Owed:** after the merge, a "Reverse…" entry must be added to that menu. Until then, Reverse works through the button on the Document screen. [REPORT §6. Open items; §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)]
- The design also lists "Check with Rocq" as a right-click on a `.v` file. [design §5.3 Rocq: subledger P (`lib/rd-rocq.pmp`)]
- The design lists the Rocq check as an action, but REPORT says Rocq items are "not read by this version". Not confirmed built. [REPORT §1. What was built]

**Actions in the design.**
- Refresh: reads every source, taking unchanged sources from the cache.
- Build: `lake build`, then the extractor.
- Run again (C or K): runs the program with the interpreter whose sha is in the certificate. If that exe has changed, the action is disabled with the reason shown.
- Check with Rocq (P).
- Reverse (subledger documents only).
- Close period.
- Export: the current grid, as a new TSV in `exports\`. [design §8. Actions and jobs]

**Built in plan 3.** Reverse, Close period, Export, Periods and Settings. [REPORT §1. What was built]

**Not in the plan-3 branch.** Run again is plan 2's control (id 105). [REPORT §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)] REPORT does not state that Build or Check with Rocq were built.

**Dialogs and menus in plan 3.**
- The Settings screen uses a folder dialog, a file dialog and a time-zone menu. [REPORT §1. What was built]
- The time-zone menu items probed were "US-Eastern" and "UTC". [REPORT §2. Verification (fresh runs on the final code unless marked)]
- The Reverse reason menu lists: "wrong statement", "wrong certificate", "superseded", "refuted by counterexample", "run in error". [REPORT §2. Verification (fresh runs on the final code unless marked)]

**Command-line modes.**
- The plan-3 branch has modes `first`, `progress`, `abort`, `selftest3`, and a config-folder argument. [REPORT §8. Every hook line in `abschluss.pmp` (diff against plan 1, `ce99acb`)]
- `first` populates the window with all logs and was used for the timing measurements. [REPORT §3. Timings (real configuration: 266 logs, 6,038 documents, 5.4 GB)]
- The design names `Abschluss.exe selftest`, which opens every screen, scripts double-clicks and prints each grid's first 20 rows. [design §10. Testing]
- The sources do not describe the other modes' user-facing behaviour.

## 5. The ledger (the Book)

### 5.1 Structure

The design's ledger has:
- a general ledger from Lean projects;
- subledgers C and K from pmp Process logs;
- subledger P from Rocq checks started in the cockpit. [design §3. Scope]

A project is a named set of source roots. Each root is a Lean project, a pmp program folder or a Rocq folder. [design §4. Ledger model]

### 5.2 Document kinds and numbers (designed)

| Kind | Letter | One per | Number |
|---|---|---|---|
| Lean commit | G | commit touching `.lean` files | G + first 10 hex of the commit |
| pmp run | K (with claims) or C (without) | `==== run` block in a Process log | letter + `yyyymmddhhmmss` + first 4 hex of the program sha256 |
| Rocq check | P | check job | P + `yyyymmddhhmmss` + first 4 hex of the file sha256 |
| Reversal | R | reversal | R + `yyyymmddhhmmss` + the reversed number |
| Period close | A | closed period | A + project + `yyyymm` |

[design §4. Ledger model]

REPORT confirms the reversal file name `R<stamp><number>.txt`. [REPORT §1. What was built]

### 5.3 Statuses (designed; each shown as a word and a colour)

| Status | Colour | Meaning |
|---|---|---|
| Closed | green | GL line with axioms within {propext, Classical.choice, Quot.sound} and the build green |
| Certified | green | pmp claim established by rule; a run whose claims are all established by rule |
| Proved | green | Rocq `Print Assumptions` answered "Closed under the global context" |
| Computed | grey | pmp run without claims, which is discharged |
| Checked | grey | Rocq file compiled, with no `Print Assumptions` in it |
| Unpriced | yellow | token usage with no matching price, or with its components missing |
| Qualified | yellow | extra axioms (`Lean.ofReduceBool`, `Rocq.*`, others by name); a Rocq check listing axioms |
| Annotation | yellow | pmp text claim "closed (annotation, not a proof)" |
| Impaired | yellow | GL line depending on a `sorry` it does not contain itself |
| Open | red | GL line containing `sorry`; pmp "claim not established" |
| Rejected | red | pmp "FAILED line N"; Rocq nonzero exit |
| Incomplete | red | run with no certificate block, or a cancelled or timed-out job; it proves nothing |
| Error | red | Lean module fails to build; a source that cannot be read or parsed |
| Reversed | grey | any subledger document that a reversal names |

[design §4. Ledger model]

**Built.**
- Reversed is built, with internal status number 14. [REPORT §1. What was built]
- Error is built for pmp documents. 449 of the 6,038 real documents are Error with the message "certificate and log disagree on the claims". [REPORT §7. Findings outside plan 3]

### 5.4 How a pmp document gets its status (designed; pmp reader built in plan 1 and used in plan 3)

The first matching rule applies:
1. No certificate lines: Incomplete.
2. A `FAILED` line: Rejected.
3. M = 0: Computed.
4. K = M: Certified.
5. Otherwise: Open. [design §5.2 pmp: subledgers C and K (`lib/rd-pmp.pmp`)]

The reader counts established claims itself and compares with the certificate's K of M. A mismatch makes the document Error, with both numbers shown. [design §5.2 pmp: subledgers C and K (`lib/rd-pmp.pmp`)]

**Plan-4 amendment (designed, not confirmed built).** The design's amendment lists line shapes the first reader did not handle, and says that from plan 4 on the reader and oracle read them. [design §5.2 amendment (plan 4, 2026-09-28)]

The shapes are:
- claims with a rule and no text;
- established lines with a witness;
- pairing of established and closed lines with the innermost open claim;
- the first-build certificate format. [design §5.2 amendment (plan 4, 2026-09-28)]

The amendment says plan 3's reader marked 449 documents Error for these shapes alone. [design §5.2 amendment (plan 4, 2026-09-28)] REPORT's open finding agrees on the 449 figure. [REPORT §7. Findings outside plan 3]

REPORT does not state whether plan 4 has been built. Until it is, the 449 Error documents remain as REPORT describes.

### 5.5 Materiality, age and periods (designed)

- **Materiality:** the number of project declarations that depend on an open item, directly or not.
- **Age:** today minus the item's posting date.
- **Aging buckets:** 0–7, 8–30, 31–90, over 90 days.
- **Periods:** calendar months. A document belongs to the period of its date. [design §4. Ledger model]

### 5.6 Reversal (built in plan 3 for C and K documents)

- The reason is picked from a five-item menu, with an optional note.
- The cockpit writes `ledger\reversals\R<stamp><number>.txt`. [REPORT §1. What was built]
- The document becomes Reversed, leaves Open items and is never current. [REPORT §1. What was built]
- The design also says the reversal file records the original number, the reason, the time and the Windows user name. REPORT does not confirm the user-name field. [design §8. Actions and jobs]
- GL lines are corrected in the Lean source, never by reversal. [design §8. Actions and jobs]
- REPORT confirms the Reverse menu, and that a cancelled menu wrote nothing. [REPORT §2. Verification (fresh runs on the final code unless marked)]
- The design allows reversal of subledger documents, which includes P. REPORT states C/K only. Rocq (P) documents are not confirmed built. [design §8. Actions and jobs; REPORT §1. What was built]

## 6. Period close

**Built in plan 3.**
- It closes only ended months, in order from the project's first month. [REPORT §1. What was built]
- It writes `ledger\periods\<project>-<yyyymm>.txt`. The file holds the trial balance, tasks with lights and details, document numbers with source sha256, reversals, interpreter names and the configuration file. [REPORT §1. What was built]
- The Lean, Rocq and token items read "not read by this version". [REPORT §1. What was built]
- The action is disabled, with its reason shown, while a task is red. [REPORT §1. What was built]
- Documents of a closed period show locked. A reversal of one is dated now. [REPORT §1. What was built]
- The Document screen shows the period state, for example `Period closed | no`, and "yyyy-mm closed" for a locked document. [REPORT §2. Verification (fresh runs on the final code unless marked); §8. Every hook line in `abschluss.pmp` (diff against plan 1, `ce99acb`)]

**Disagreement.**
- The design says Close period is enabled when no task is red, and that each yellow task is written into the period document as a qualification. [design §7. Screens (all clicking)]
- The design also says the period document records the commit, `lean-toolchain`, the Mathlib revision, interpreter shas, and the price-list and configuration file names. [design §8. Actions and jobs]
- REPORT's built version reads no Lean, Rocq or token items, and does not mention Mathlib revision, commit or price-list file names. Prefer REPORT for what exists. The Lean, Rocq and token parts of the period document are designed, not confirmed built.

**Test seam.** `selftest3` takes 2026-09 as the current month, so that "the earliest open period has not ended" is checked identically in every month. This value is 0 outside `selftest3`. [REPORT §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)]

## 7. Settings

REPORT confirms these configuration keywords: lean and rocq roots, `claude`, `codex`, `tool lake|git|coqc`, `coqarg`, `timezone`, `prices`. [REPORT §1. What was built]

Save writes a new `config\config-<yyyymmddhhmmss>.txt`, reloads the configuration, the ledger and every log (from the cache), and rebuilds the tree. [REPORT §1. What was built; §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)]

Settings shows the pending configuration lines and action rows. A project's name comes from its folder. `coqarg` and project lines are kept as they are. A `coqarg` is changed only in the file itself. [REPORT §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)]

The design says the only typed inputs are the price list's rates and an optional note on a reversal. [design §1. Agreed understanding] REPORT says typing is limited to a reversal note. A price-list editing screen is not confirmed built. [REPORT §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)]

## 8. File locations

**Design layout.** The design's tree under `C:\ClaudeOutput\abschluss\` is:

| Path | Contents |
|---|---|
| `abschluss.pmp` | the application, emitted as `Abschluss.exe` |
| `lib\grid.pmp`, `lib\ledger.pmp` | grid and ledger libraries |
| `lib\rd-lean.pmp`, `lib\rd-pmp.pmp`, `lib\rd-rocq.pmp`, `lib\rd-tokens.pmp` | source readers |
| `lean\AbschlussExtract.lean` | the Lean extractor |
| `config\config-<yyyymmddhhmmss>.txt` | one new file per saved change; the newest applies |
| `config\prices-<yyyymmddhhmmss>.txt` | price lists |
| `ledger\rocq\`, `ledger\reversals\`, `ledger\periods\` | documents the cockpit writes |
| `jobs\` | job logs and extractor output |
| `cache\` | per-source summaries, rebuildable |
| `exports\` | one new TSV per export |
| `tests\` | Racket oracles and the selftest's expected output |
| `docs\specs\` | the design file |

[design §6. Files]

**Writing rule.** The cockpit opens every file it writes with `CREATE_NEW`. If the name exists, the write fails and the failure is shown. Nothing is overwritten. [design §6. Files]

**Built in plan 3.**
- The cache: `<data root>\cache\<key>.bin`, one per Process log. The key is made from the path, size, last-write time, reader version and chunk size, hashed to 64 hex characters. [REPORT §1. What was built]
- A file that is too short, fails its checksum, or has another version or key is ignored and the log is parsed. The status bar names the first such file and the reason. A superseded or corrupt slot is never overwritten; the writer takes the next slot (`-2` to `-8`). [REPORT §1. What was built]
- Writers make their own folders on first write. Opening the cockpit writes only its cache. [REPORT §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)]
- Reversals go to `ledger\reversals\`, period documents to `ledger\periods\`, exports to `exports\`, and configuration to `config\`. [REPORT §1. What was built]
- The real-configuration run had 266 cache files totalling 12,565,691 bytes. [REPORT §2. Verification (fresh runs on the final code unless marked)]

**Source locations the design reads.**
- Process logs: every `*-process.txt` under the configured pmp roots. [design §5.2 pmp: subledgers C and K (`lib/rd-pmp.pmp`)]
- Claude transcripts: `*.jsonl` under the configured roots. [design §5.4 Tokens: cost (`lib/rd-tokens.pmp`)]
- Codex transcripts: `*.jsonl` under the sessions root. [design §5.4 Tokens: cost (`lib/rd-tokens.pmp`)]

The sources do not state an installed location for the finished application or a release folder path. [REPORT §Abschluss plan 3 — report; SCOPE §4. Release today: what is ready, and what it may claim]

## 9. How a judge posting is booked

Not stated in the source documents.

The sources do not describe the cockpit steps from submission of a judge posting to ACCEPT or REJECT, or how the outcome appears in the ledger. What they do say:

- The pmp judge (`judge-v3.pmp` under `pompetzki.exe`) is "the only judge of the Book". It ACCEPTs Theorem 29's replay (4,551 theorems, 139,194 steps) and today's 7 Stage 2 files, and REJECTs every mutant tried. [SCOPE §1. The one system (the Monolith) and where each part stands]
- A Racket copy (`racket/judge.rkt`) agrees on every file so far. [SCOPE §1. The one system (the Monolith) and where each part stands]
- The ledger and cockpit plans 1–3 are "not wired to judge postings". [SCOPE §1. The one system (the Monolith) and where each part stands]
- Under the Book's rule an open entry closes by a proof, a refutation or an independence result. The one entry closed by pmp so far is half of CH: Theorem 29 gives Con(ZFC) → Con(ZFC + ¬CH*). Gödel's half through L is owed. [SCOPE §2. How much of mathematics is formalized]
- Lean-side postings carry "replay on a fixed kernel owed", because Lean v4.28.0 has 3 known kernel exploits. [SCOPE §1. The one system (the Monolith) and where each part stands]
- The design puts posting pmp claims into Lean (account determination and a Lean-side certificate checker) outside the cockpit's scope. [design §3. Scope; §12. What follows this spec]

The cockpit's own pmp documents are runs of programs with a certificate, not judge postings. A run is Rejected on a `FAILED line N`, and Certified when all claims are established by rule. [design §4. Ledger model; §5.2 pmp: subledgers C and K (`lib/rd-pmp.pmp`)] The sources do not equate this with a judge ACCEPT or REJECT.

## 10. Performance and behaviour to expect (plan-3 branch)

- The target "< 10 s" for a warm start is not met. [REPORT §3. Timings (real configuration: 266 logs, 6,038 documents, 5.4 GB)]
- The measured values on the real configuration (266 logs, 6,038 documents, 5.4 GB) are:
  - Warm `first` mode: 26,047 and 24,578 ms.
  - The emitted exe's status line: 17,688 ms.
  - Cold `first` mode with an empty cache: 500,891 ms. [REPORT §3. Timings (real configuration: 266 logs, 6,038 documents, 5.4 GB)]
- The stated cause is how `pompetzki.exe` resolves names and labels. Plan 3 may not change the interpreter. [REPORT §3. Timings (real configuration: 266 logs, 6,038 documents, 5.4 GB)]
- The first Journal build on large books takes 17 s with no message loop, so Windows marks the window Not Responding meanwhile. [REPORT §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)]
- A click made during the ledger build is lost rather than queued. Closing during the build is honoured when the build ends. [REPORT §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)]
- Closing during a cold read of the logs takes 88–112 ms. [REPORT §2. Verification (fresh runs on the final code unless marked)]
- Refreshing unchanged logs allocates nothing (200 refreshes: arena 0, heap 0). [REPORT §2. Verification (fresh runs on the final code unless marked)]

## 11. Error handling

**Designed.**
- Every failure shows as a red row in the grid where the data would have been, with the path, the line and the OS or parser message.
- An unknown interpreter, an unknown model or a missing price is shown as such. No value is filled in.
- A certificate that disagrees with the reader's own count makes its document Error. [design §9. Error handling]

**Built.**
- A log's read error is reported again on Refresh while the log is unchanged. [REPORT §1. What was built]
- A damaged cache file is ignored and named in the status bar. [REPORT §1. What was built]

## 12. Owed and open

**From REPORT (cockpit):**
- Warm start under 10 s: not met. The route is task T33, a separate interpreter with names and labels resolved once, queued for Antigravity A03. [REPORT §6. Open items; §3. Timings (real configuration: 266 logs, 6,038 documents, 5.4 GB)]
- `AZRCLICK` (Reverse on right-click) is not hooked. After the merge, a "Reverse…" entry must be added to plan 2's menu. [REPORT §6. Open items]
- Merge with plan 2 is owed. Rerun `git merge-tree` against plan 2's head first. [REPORT §9. Merge notes for plan 2]
- After the merge, regenerate `lib\hot.pmp` with plan 2's hot routines added. [REPORT §9. Merge notes for plan 2]
- The 200-refresh run on the real configuration ran on the code of `4eb8201`, not the final code. [REPORT §6. Open items]
- 449 of 6,038 real documents are Error, "certificate and log disagree on the claims". The line shapes are described in the design's plan-4 amendment. [REPORT §7. Findings outside plan 3; design §5.2 amendment (plan 4, 2026-09-28)]
- Deferred minors:
  - the status bar strip stays light in dark mode;
  - cache string offsets and item-to-document indices are not bounds-checked field by field when the SHA-256 trailer is valid;
  - `lib\hot.pmp` must be regenerated after code changes;
  - the 17-second first Journal build with no message loop. [REPORT §5. Deferred minors]
- Period close does not read Lean, Rocq or token items ("not read by this version"). [REPORT §1. What was built]
- The Journal and Document screens, Periods, Settings and Reverse were checked by window messages, not by real mouse input. A defect visible only to real mouse input would go unseen. [REPORT §4. Rulings (every `Ruling:` line of the ledger, in order, each with its cost if wrong)]

**From the design (not confirmed built):**
- Slices 3–5: the Lean extractor and reader, General ledger, Axioms, Bill of materials and Cockpit screens, the Rocq reader and check job, and the token reader, price list, run links, Costs and Vendors. [design §11. Build order]
- Out of scope, each for a later spec:
  - posting pmp claims into Lean;
  - token-budget availability control;
  - an MRP run and automatic clearing run over open items;
  - the ARM Mac port;
  - several users and permissions;
  - transcripts without usage fields. [design §3. Scope]

**From SCOPE (system and release):**
- That the bytes of `judge-v3.pmp` compute `check_batch`: in progress (Codex), not proved. [SCOPE §1. The one system (the Monolith) and where each part stands]
- Stage 2: the Rocq "once" proof is not done, and the derived rules (rank–nullity, Smith, Gröbner, Nullstellensatz, LRAT, Pratt, Farkas) are not posted. [SCOPE §1. The one system (the Monolith) and where each part stands]
- Stages 4 (native image theorem), 5 (Metamath set.mm) and 6 (Lean/Mathlib → ZF translator) are not started. 0 Mathlib theorems are judged by pmp. [SCOPE §1. The one system (the Monolith) and where each part stands]
- Stage 8: searchers are not wired to pmp. [SCOPE §1. The one system (the Monolith) and where each part stands]
- Stage 9: the Book in pmp is not wired to judge postings. [SCOPE §1. The one system (the Monolith) and where each part stands]
- Stage 10, public release: not done. The last dist builds were 2026-09-17/18/23/24. [SCOPE §1. The one system (the Monolith) and where each part stands]
- Lean side: every posting carries "replay on a fixed kernel owed". [SCOPE §1. The one system (the Monolith) and where each part stands]
- Gödel's half of CH through L is owed. [SCOPE §2. How much of mathematics is formalized]
- Release steps:
  - finish the 15 remaining judge runs (about 10 minutes);
  - write `RESULTS.md`;
  - make a release folder with a sha256 manifest and README;
  - publish, which needs Christopher's yes and the place. [SCOPE §4. Release today: what is ready, and what it may claim]
- What the release may claim: `check_batch` is sound for `prov` (Rocq), and two independent implementations agree on 4,551 + 1,656 theorems and on every mutant. It may not yet claim that the pmp bytes compute `check_batch`; the release states that as owed. [SCOPE §4. Release today: what is ready, and what it may claim]

## Sources

- C:\ClaudeOutput\abschluss\docs\specs\2026-09-27-cockpit-design.md
- C:\ClaudeOutput\abschluss\REPORT.md
- C:\ClaudeOutput\abschluss\docs\SCOPE-AND-RELEASE-2026-10-09.md

(Manager correction: the Copilot draft printed the second and third paths without `\a`; the defect was in the manager's prompt, see CHECK-a.md item 1.)

