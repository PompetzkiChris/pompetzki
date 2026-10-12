# Verified Book posting and rejudgment

Copyright (c) 2026 Christopher Pompetzki. Project code is under the accompanying MIT license.

This version integrates the Grok Bot Book lane's executed corrections, with a separate rejudging verifier developed by Codex. Earlier sources, archives and run outputs remain beside this version. `PROVENANCE.json` binds the received archive and describes the integration.

`verified-book-post.rkt --bundle DIR OUTDIR DATE INPUT ...` creates a fresh posting, copies the JDG inputs, runs the authenticated pmp judge and the independent Racket judge, and binds their commands, input hashes, program hashes, output hashes and exact integer timestamps in its ledger metadata. It prefers v5 judges and retains v4 fallback for older candidate bundles. An ambiguous verdict or expired deadline produces SUSPENSE and exit 3. Existing output targets are refused.

`verified-book-check.rkt --bundle DIR POSTINGDIR` recomputes the ledger chains, verifies copied inputs and output hashes, reruns both judges on the copied inputs, and reconstructs theorem statement and derivation hashes. It accepts relocated posting directories. This rejudgment detects a forged theorem hash even when the attacker has recomputed the entire ledger chain.

The low-level `book-post-v4.rkt` writer checks receipt metadata and logs. Those files carry no digital signature: a complete internally consistent rewrite requires fresh rejudgment by `verified-book-check`. The supported posting interface runs the judges itself. The low-level command line refuses imported verdict rows.

The poster and checker bound waits for inherited output pipes. On POSIX they also start each judge in a separate process group. On Windows an owned descendant may continue until it exits, but it cannot hold the poster's reader wait indefinitely. Mathematical expectations use exact integers and rational numbers; timing uses exact integer milliseconds.

Run `python test-verified-book-v4.py --bundle DIR` and `python test-verified-check.py --bundle DIR`. On Windows, `test-adversarial.py` additionally compiles an owned test executable to exercise ambiguous verdicts and an inherited output pipe, without changing user processes.

The JDG parsers, executable checker correspondence with Gallina, and compilation semantics remain open proof obligations. The source checker and canonical-prefix theorems retain their original statements and hypotheses.
