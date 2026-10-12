# Verified Book posting and evidence rejudgment, version 6

Copyright (c) 2026 Christopher Pompetzki. Project code uses the accompanying MIT license.

The supported poster is `verified-book-post.rkt --bundle DIR OUTDIR DATE INPUT ...`.
It creates a fresh posting, copies the JDG inputs, runs the authenticated pmp and
separate Racket implementations, and binds inputs, selected tools and outputs by
SHA256 with exact integer timestamps. It prefers v5 judges and keeps v4 bundle
compatibility. Existing targets are refused. Ambiguous or timed-out runs produce
SUSPENSE and a nonzero exit.

The supported checker is `verified-book-check.rkt --bundle DIR POSTINGDIR`.
It verifies both ledger chains, ordered F/B/N identities and links, receipt and
metadata uniqueness, exact sequential times, unambiguous stored logs, input byte
counts, and selected artifact hashes before and after fresh rejudgment. It
reconstructs every theorem-derived B field, including statement and complete
derivation hashes, exact hypotheses, citations, duplicate-statement backlinks,
registry identity and axiom/definition/hypothesis-entry traces. Windows and POSIX
recorded paths resolve by basename after relocation.

Version 6 closes the declared artifact set. A supported posting contains exactly
`BOOK-1.0.ledger`, `NEGATIVE-1.0.ledger`, `RECEIPTS.tsv`, `run-metadata.json`,
`judge-inputs/` and `judge-runs/`. The two artifact directories contain exactly the
declared regular snapshot and per-case stdout/stderr files, with unique output
identities. Extra files, nested directories, links, missing files and duplicate output names are
rejected. An unreferenced `judge-runs` file that version 5 accepted now produces
CHECK FAILED. Version 5 sources and the original reproduction are preserved.

The low-level `book-post-v4.rkt` writer remains unchanged. Its library accepts
internally consistent unsigned evidence. A complete forged false-proof posting
can be constructed through that library; fresh rejudgment rejects it. These files
carry no digital signature or historical producer attestation.

Grok Bot supplied the preceding posting corrections and executed adversarial
evidence. Codex added the correcting evidence checker and Windows regressions.
This version changes artifact verification; it changes no mathematical theorem
statement or hypothesis.

With Python 3 and Racket, run:

```sh
python test-verified-book-v4.py --bundle DIR
python test-verified-check.py --bundle DIR
python test-review-v6.py --bundle DIR
python test-full-replay.py --bundle DIR
```

On Windows, run `python test-adversarial.py --bundle DIR` for owned ambiguous
verdict and inherited-pipe controls. The review driver creates its own fixtures;
it covers five added artifact-closure attacks alongside the preceding evidence
attacks. The full replay driver checks the unchanged released SHA256
`a202ed994929c8484f053219047d854729af4a3d97ad8f804bb3cdef3b4a52ae`, with
4,551 theorem postings, 4,373 Proved, 178 Qualified and 139,194 steps.

`--racket` selects an interpreter. The original poster/checker drivers and full
replay driver also accept explicit compiled poster/checker paths. The current
public source whitelist is the 13-file `PUBLIC-SOURCE-MANIFEST.json`; retained
version 5 copies are excluded. `PUBLIC-RUN-RESULTS.json` supplies sanitized run
totals. `BOOK-V6-FREEZE.json` and its SHA list bind sources and final receipts.

The Gallina proof statements retain their original hypotheses. Parser denotation,
Gallina/executable correspondence, compiler preservation and shipped executable
byte correspondence remain separate proof obligations. Finite checks do not
establish those theorems.
