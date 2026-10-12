# Verified Book posting and evidence rejudgment, version 5

Copyright (c) 2026 Christopher Pompetzki. Project code uses the accompanying MIT license.

The supported poster is `verified-book-post.rkt --bundle DIR OUTDIR DATE INPUT ...`.
It creates a fresh output directory, copies the JDG inputs, runs the authenticated
pmp judge and the separate Racket implementation, and records input, tool and
output hashes with exact integer timestamps. It prefers v5 judge files and keeps
v4 compatibility. Existing output targets are refused. An ambiguous verdict or
expired deadline produces SUSPENSE and a nonzero exit.

The supported checker is `verified-book-check.rkt --bundle DIR POSTINGDIR`.
It verifies both ledger chains and ordered record identities, checks metadata
and RECEIPTS for unique input identities, exact sequential times, consistent
verdicts and unambiguous stored output, and resolves the recorded judge artifacts
to the actual selected files in the supplied bundle or PATH interpreter. It
checks artifact hashes before and after fresh rejudgment. Historical absolute
paths are used only as recorded text; local snapshots and logs resolve by
basename. Windows and POSIX recorded paths can be checked after relocation.

For every accepted input, the checker reconstructs every theorem-derived B field
from the checked JDG bytes: theorem and registry entry indices, classification,
statement and complete derivation hashes, step count, exact hypotheses, duplicate
statement backlink, citations, axiom/definition/hypothesis-entry traces, input and
registry hashes, source and judge completion evidence. It checks F/N input hashes,
byte counts, registry/count/aggregate/trace fields, record links and end ranges.
Unrecorded snapshot files, duplicate records and contradictory receipt evidence
are rejected.

The low-level writer remains `book-post-v4.rkt`. It accepts internally consistent
unsigned receipt evidence through its library interface. A complete forged
metadata/log/input/ledger set can therefore be written by that library. Fresh
rejudgment by the supported checker rejects a forged false proof. The checker
provides consistency checks and fresh mathematical verification; these files
carry no digital signature or attestation of who produced the historical run.

The Grok Bot Book lane supplied the preceding posting corrections and executed
Linux adversarial evidence. Codex added the correcting evidence verifier and
the Windows regressions in this version. Version 4 sources, archives, failed
cases and run outputs are preserved beside version 5. No mathematical theorem
statement or hypothesis was changed by this correction.

Run the portable regressions with Python 3 and Racket:

```sh
python test-verified-book-v4.py --bundle DIR
python test-verified-check.py --bundle DIR
python test-review-v5.py --bundle DIR
python test-full-replay.py --bundle DIR
```

The correcting review driver creates its own four-file posting and attack
copies; it requires no prior review directory. It tests hypotheses, IDs,
receipt/log/metadata corruption and a complete library forgery. The full replay
driver requires the unchanged released input SHA256
`a202ed994929c8484f053219047d854729af4a3d97ad8f804bb3cdef3b4a52ae` and checks
4,551 postings: 4,373 Proved, 178 Qualified, and 139,194 derivation steps.
On Windows, `test-adversarial.py --bundle DIR` uses an owned test executable for
ambiguous verdicts and inherited output pipes. Its fixture names follow the
selected v5 or v4 bundle. It does not operate on user processes.

`--racket` selects an interpreter for each driver. The original poster/checker
drivers and the full replay driver also accept explicit compiled poster/checker
paths. Source hashes, the public whitelist and verified run totals are recorded
in `PUBLIC-SOURCE-MANIFEST.json` and `BOOK-V5-FREEZE.json`.

The Gallina checker and canonical prefix proof statements retain their original
hypotheses. JDG parser denotation, executable checker correspondence with Gallina,
compiler preservation, and shipped executable byte correspondence remain separate
proof obligations. Finite test results do not establish those theorems.
