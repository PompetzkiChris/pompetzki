# Verified Book posting and evidence rejudgment, version 7

Copyright (c) 2026 Christopher Pompetzki. Project code uses the accompanying MIT license.

The supported poster is `verified-book-post.rkt --bundle DIR OUTDIR DATE INPUT ...`. It creates a fresh posting, copies the JDG inputs, runs the authenticated primary pmp judge and independent Racket cross-check, and binds inputs, selected tools, and outputs by SHA256 with exact integer timestamps. It chooses source version v6 first, then v5, then v4, and selects the native executable of that same version when available. `--interpreted` forces the selected primary source through the interpreter. Existing targets refuse. Ambiguous or timed-out runs produce SUSPENSE and nonzero status.

The supported checker is `verified-book-check.rkt --bundle DIR POSTINGDIR`. It validates the recorded native or interpreted command and selected tool/source hashes, then reruns that recorded route. In v6, an interpreted posting could be rejudged with the native executable; an actual-process reproduction is preserved and corrected in v7. Both routes retain fresh mathematical rejudgment.

Recorded Windows and POSIX paths resolve by basename after relocation. A recorded path ending in slash or backslash refuses before basename normalization. Empty recorded paths refuse. Tests cover artifact paths, command executable and input paths, snapshot paths, output paths, and receipt-directory paths with both trailing separators.

The checker retains v6 complete artifact closure, both ledger chains, ordered F/B/N identities and links, unique receipts/metadata, exact sequential times, unambiguous stored output, exact input byte counts, and artifact hashes before and after rejudgment. It reconstructs all theorem-derived B fields, including complete statement and derivation hashes, hypotheses, citations, duplicate-statement backlinks, registry identity, and axiom/definition/hypothesis-entry traces. A posting contains exactly the four supported ledger/receipt/metadata files plus judge-inputs and judge-runs. Those directories contain exactly the declared regular files. Extra files, directories, links, missing files, or duplicate identities refuse.

The low-level book-post-v4.rkt writer is unchanged. Its library accepts internally consistent unsigned evidence; a completely fabricated false-proof posting can be written through that library and is rejected by the supported checker's real rejudgment. No theorem statement, hypothesis, derivation, or evidence-reconstruction formula was changed.

Grok Bot supplied the preceding Book corrections and the v6 recorded-route patch. Codex independently reproduced the route and trailing-path defects and added this versioned correction and Windows regressions. Source credit, patch hashes, and the MIT project license are included.

The source and compiled suites each passed posting 4/4, checker 5/5, evidence review 29/29, owned pipe/verdict controls 2/2, and route/path checks 30/30. Both full replay runs posted and rejudged the unchanged 4551 theorems: 4373 Proved, 178 Qualified, and 139194 steps. The route tests use actual primary native and interpreted programs and independently inspect each fresh command receipt. V6 priority is checked with v6, v5, and v4 present; historical v5 and v4 bundles are also checked in both execution modes.

With Python 3 and Racket:

```
python test-verified-book-v4.py --bundle DIR
python test-verified-check.py --bundle DIR
python test-review-v7.py --bundle DIR
python test-full-replay.py --bundle DIR
python test-route-path-v7.py --bundle DIR
```

On Windows, `python test-adversarial.py --bundle DIR` checks owned ambiguous-verdict and inherited-pipe controls. The poster/checker/review/full/route drivers accept `--poster` and `--checker` executable paths where applicable; the pipe driver accepts `--poster`. `--racket` supplies an interpreter. The route driver accepts repeated `--historical-bundle` arguments for available older bundles. Output directories are new timestamped test directories beside these sources.

PUBLIC-SOURCE-MANIFEST.json lists the 14 current public files explicitly. Copied historical v6 aliases and driver versions are excluded. PUBLIC-RUN-RESULTS.json records current finite results and hashes. Full local command receipts and the original reproductions remain outside the public source whitelist. Executable-to-Gallina and compiler preservation remain open proof obligations.
