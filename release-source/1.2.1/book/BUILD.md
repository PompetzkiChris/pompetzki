# Book continuation build receipt

The build root is `C:\ClaudeOutput\pompetzki\release-1.0\recovery-gpt-20261010\book` on THEBIGMAGILLA, Alienware Area-51 AAT2265. The source hand-ins remain under `C:\ClaudeOutput\pompetzki\release-1.0\handin`; the earlier master remains under `book-master`.

The continuation copied the 33 earlier journal segments and both original duplicate/conflict tables into a new directory. `ORIGINAL-JOURNAL-SHA256.json` binds the earlier segment bytes. No original journal segment was edited.

`inventory.rkt HANDIN-ROOT inventory-all.tsv DATE` captures current source bytes. `recovery-prepare.py` selects the current inventory and excludes the preliminary `queue\CX-M3b\book` ledger pair in favor of sealed `queue\CX-M3b\book2`. It also records source pairs absent from the earlier inventory.

`chainverify.rkt inventory.tsv chainverify.tsv` checks every selected ledger. `spotcheck.rkt plan inventory-extra.tsv chainverify.tsv SHIPPED-BOOKDIR spot\PLAN-extra.tsv` chooses the new controls. `recovery-plan.py` combines the earlier controls with those new controls and keeps completed dual-judge receipts for reuse. Interrupted process results are excluded from the reusable receipt file.

`spotcheck.rkt run-small spot\PLAN.tsv spot\run-recovery spot\PRIOR-VERDICTS.tsv` reruns the remaining controls, with two process lanes and a 600-second timeout per judge. `check-final-receipts.py` independently binds all 157 final CX-M3b and SETMM-out7b receipts to their actual certificate bytes, verdict words, exits and accepted counts.

`code\recovery-finish.ps1` makes the decisions, appends new journal segments and runs both source-record checkers. Every tool creates new receipt files. `package-book.py` verifies the final source seals, stages the admitted journal/source ledgers/certificates/receipts under relative aliases, renders the Book, writes the full SHA-256 manifest and creates `Abschluss-1.2.1-book-master.zip` with its checksum file.

After extraction, `verify-portable.py` independently checks the archive manifest, journal chain, original-segment hashes, counters and certificate payloads. `master-verify-portable.rkt` and `master-verify-indep-portable.rkt` check the source-record correspondence using the relative aliases. The original absolute provenance fields remain in the journal and source ledgers.
