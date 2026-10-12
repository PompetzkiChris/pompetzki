**Abschluss 1.3.1**

This release rejects impossible certificate record counts before allocation, rechecks Book postings with their recorded primary execution route, and corrects installation version handling. It preserves the exact matrix engine and the interpreter's current source bytes.

A tiny input declaring `999999999999` theorems or proof steps previously caused Racket to exit out of memory and the primary pmp routes to return LIMIT. The v6 judge applies the necessary bound that each declared record occupies at least one remaining input byte before allocating theorem, step or numeric-list vectors. The Racket cross-check applies that bound before its theorem and step vectors. Maximum numeric predicate IDs, empty batches and arbitrary zero padding retain their meaning. The numeric domain remains `0..999999999999`; a thirteenth significant digit is refused before arithmetic.

Book v7 uses the recorded, hash-bound primary route for fresh rejudgment. An interpreted posting now reexecutes through the interpreter even when a native judge is present. Poster and checker select the same current judge version. A recorded file path ending in `/` or `\` is refused before basename normalization. The low-level writer, original theorem statements, hypotheses and theorem-field reconstruction are preserved.

The Windows application opens an editable exact matrix workspace. Integer and rational entries, rank-nullity, kernels and images, `Ax = b`, determinant, inverse and the matrix operations remain exact. Each malformed batch item receives its own ordered rejection while surrounding valid jobs continue. Existing output files are preserved.

Executed validation includes:

- 938 v6 judge runs: Windows native 264, Linux native 264, Windows interpreted pmp 146 and Racket 264; zero unexpected outcomes or timeouts. The unchanged reviewed corpus includes the full 4,551-theorem replay.
- 51 additional executions authored and run by Local Grok Build, with root verification of all raw output, input, executable and source hashes; zero failed assertions.
- Candidate and extracted-source-only Windows builds each pass 76 package checks, including 849 exact Fraction cases and eight owned hidden GUI callback cases. Each also passes 40 numeric/count checks with zero timeouts.
- Book v7 source and compiled checks each pass 4 posting, 5 checker, 29 evidence, 2 pipe/verdict and 30 route/path checks. The shipped compiled package checks cover 26 route/path cases; the four historical-version checks have their separate source/compiled receipts. Full posting and fresh rejudgment preserve 4,373 Proved, 178 Qualified and 139,194 steps across 4,551 theorems.
- The source ZIP reproduces byte for byte. Both Windows bundles contain the same 442 paths. All 417 ordinary files and 17 declared embedded source hashes match, both interpreter binaries match, and directly measured allocated native PE sections match. Rebuilt executable and build-context differences are identified in SOURCE-CLOSURE-1.3.1.json.

The current packaging recipe selects 22 files, the current judge/runtime map selects 86, Book v7 selects 14, and the cockpit selection explicitly pins 94 code/helper files. Raw validation outputs and their explicit hashes are supplied in validation-1.3.1-public.zip. The source asset includes both reviewed certificate validation corpora.

The separate reader instruction-step addendum compiles 14 modules and recursively checks 12 selected closed statement types over the actual extracted 77-instruction controller. It retains the declared source-extraction and native/OS boundaries. Additional source-reader work continues separately. Earlier ASCII and registry/numeric proof addenda remain available with their explicit premises and source credit.

The kernel checks and finite executable tests have their stated scopes. Compiler preservation and whole-judge executable correspondence remain open formal obligations. The GUI tests execute actual Compute callbacks in owned hidden frames; physical visible-window interaction is a separate acceptance boundary.

Download [version 1.3.1](https://github.com/PompetzkiChris/pompetzki/releases/tag/v1.3.1). SHA256SUMS.txt covers the distributions and supplemental artifacts. Earlier releases, source variants, failed build/test directories and their receipts are preserved.
