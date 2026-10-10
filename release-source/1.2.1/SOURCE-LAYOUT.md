# Source and asset layouts

The component README files are copied byte for byte from their complete mathematical release assets. Their `source/`, `runtime/`, `provenance/`, dependency-object and receipt references describe those asset layouts. Their build commands use the asset directories and the recorded logical module mappings.

This Git directory publishes the selected sources in these locations:

| component | source location |
|---|---|
| Windows verifier | `verifier/abschluss-verify-r2.rkt`, `verifier/build-verifier.ps1` |
| Extracted bounded emitter | `sigma1-emitter/runtime/`, `sigma1-emitter/provenance/` |
| Signed-Q definitions and first two proofs | `signedq/*.v` |
| Three further original host proofs | `signedq-followup/SignedQHostProofs3.v` |
| Book source-record checkers and continuation | `book/` |

For portable Book commands, use `book/BUILD-R2.md` and `book/PORTABLE-CORRECTION.md`. The corrected source names are `verify-portable-r2.py`, `portable-paths-r3.rkt`, `package-book-r2.py` and `verify-archive-r2.py`. The archive's conventional portable checker names contain these corrected implementations.

`.gitattributes` disables line-ending conversion in this directory so that Git blobs retain the exact bytes used by the source/object and executable receipts. `SOURCE-SHA256.tsv` binds every selected file other than itself. Complete execution receipts and payload manifests are distributed as release assets.
