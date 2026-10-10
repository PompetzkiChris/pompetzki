# Portable Book package revision

The admission journal contains 96 segments and 284,207 postings: 284,036 Proved
and 171 Qualified. There are 218,370 distinct statement hashes. The first 33
journal segments retain their original bytes. Source duplicate postings stay
in their source ledgers and duplicate tables. The selected ledger plan contains
151 merged kinds, 33 empty kinds and 34 held kinds; MERGE-PLAN.tsv states each
held reason.

The new portable checker sources are `verify-portable-r2.py` and
`portable-paths-r3.rkt`. The Python checker confines every manifest,
certificate and alias target to the resolved package root; every target must
appear in the manifest. It binds every admitted F/N historical path to its
recorded certificate hash, byte count and portable payload. Its validation
uses explicit exceptions, including when Python runs with `-O`.

The Racket resolver confines alias targets, requires their manifest membership,
rejects link and junction traversal and rejects absent historical aliases on
each host. Contained absent local journal paths remain valid probes for the
source checkers' segment scan.

`package-book-r2.py BASE_STAGE NEW_STAGE NEW_ARCHIVE CHECKER_DIR` builds a fresh
stage from the existing packaged Book data, replaces its conventional portable
checker names with these new implementations, creates the full SHA-256 manifest
and writes a ZIP with sorted entries and a fixed timestamp. CHECKER_DIR must
contain both named checker sources. Both output paths must be new. Predecessor
stages and archives remain at their original paths.

`verify-archive-r2.py ARCHIVE NEW_EXTRACT_DIR NEW_RECEIPT_DIR` checks every ZIP
path, duplicate member names, link entries and CRC, extracts into a new
directory and runs the Python payload checker and both Racket source checkers
serially. Python 3.11 or later and Racket are required. Every validation log and
the archive hash appear in the new receipt directory.

All 648 admitted F certificates and 2,073 admitted N certificates are bundled.
The archive also bundles 16 historical suspense payloads. One S record retains
its original expected 369,409-byte payload hash; the explicitly checked current
and archived named paths contain different 305,155-byte content. The original S
journal and source bytes remain intact, with the checked paths and hashes
described in CERTIFICATE-PAYLOAD-GAPS.tsv and PAYLOAD-BOUNDARIES.md.

Five historical composite receipt references resolve to ten actual judge
outputs. RECEIPT-RESOLUTIONS.tsv states those bindings; no historical receipt
reference remains unresolved in this package.
