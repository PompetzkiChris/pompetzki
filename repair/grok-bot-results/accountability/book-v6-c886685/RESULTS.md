# Book v6 at c886685356d50e16c018390db40ee67cf3ec13a3 (Grok Bot accountability)
Full SHA verified with git ls-remote. Claimed checker sha256 9215daae5f88d786bc7e26e386fab59386e652602940a013cc4d25057725f8c5. **VERIFIED**: verified-book-check.rkt and verified-book-check-v6-source.rkt both hash to it. verified-book-post.rkt c6779f52… is unchanged from v5. judge-v5.pmp, judge-v5.rkt and runtime-v2 asm are byte-identical to 453afa6. Bundle: /workspace/bundle-453 (judge/ identical except 3 added receipt JSON files; runtime-v2 built by me, sha256 3658455c…). Harness: `book6.sh REPO BUNDLE OUTDIR` (my own). The v5 forgery dirs are replayed unchanged.

| Claim | Command | Actual output | Verified outcome |
|---|---|---|---|
| Genuine native post | `verified-book-post.rkt --bundle B OUT 2026-10-11 ok-hyp.jdg` | exit 0, pmp ACCEPT racket ACCEPT, F1 B1 | PASS |
| Genuine --interpreted post | same + `--interpreted` | exit 0, ACCEPT/ACCEPT | PASS |
| Check both | `verified-book-check.rkt --bundle B OUT` | exit 0, `evidence_schema":"verified-book-v6"` | PASS |
| Genuine REJECT (m1-refl) post+check | post/check | N1, CHECK OK exit 0 | PASS |
| **v5 GAP: unreferenced judge-runs file** (v5 replay + fresh) | check | `judge-runs contains missing, duplicate or unreferenced artifacts` exit 1 | **CLOSED in v6** (v5 returned CHECK OK) |
| Fully consistent false-proof forgery (v5 dir) | check | `rerun differs from stored verdict` exit 1 | REJECTED |
| Rehashed theorem | check | `B record differs from the complete checked theorem evidence` | REJECTED |
| Orphan N row | check | `input/receipt/ledger counts differ` | REJECTED |
| Extra snapshot in judge-inputs | check | `judge-inputs contains missing, duplicate or unreferenced artifacts` | REJECTED |
| Changed input | check | `snapshot hashes or unchanged state differ` | REJECTED |
| Bad F sha rechained | check | `F/N input identity, bytes, source or date differs` | REJECTED |
| Duplicate receipt | check | `duplicate RECEIPTS input identity` | REJECTED |
| Reordered B | check | `B record shape/ordered ID/F link differs` | REJECTED |
| Wrong input byte count | check | `F/N input identity, bytes, source or date differs` | REJECTED |
| Tampered timestamp | check | `metadata timestamps are inexact, negative or unordered` | REJECTED |
| Empty judge-runs/ | check | `recorded file missing: 1-pmp.stdout.txt` | REJECTED |
| Empty judge-inputs/ | check | `recorded file missing: 1-ok-hyp.jdg` | REJECTED |
| Extra top-level file / dir | check | `posting contains artifacts outside its supported file/directory contract` | REJECTED (both) |
| Nested dir in judge-runs | check | unreferenced-artifacts error | REJECTED |
| Symlinked run file | check | unreferenced-artifacts error | REJECTED |
| Missing run file | check | `recorded file missing: 1-pmp.stderr.txt` | REJECTED |
| Same bytes under two input names | post+check | 2 files, CHECK OK | ACCEPTED (expected: two distinct inputs) |
| Same input path given twice | post+check | deduplicated to 1 file, CHECK OK | ACCEPTED (dedup, consistent) |

I found no concrete failure. Not constructed: a metadata forgery where two cases name the same output file. The filesystem can't hold two files with one name, and I didn't hand-build that rechained metadata variant. Full 4,551-theorem replay: SKIPPED (estimated well over 10 min). The book-v4-e4b075a and book-v5-453afa6 dirs are preserved unchanged.

Finite tests do NOT establish executable/Gallina correspondence, parser denotation, or compiler preservation.
