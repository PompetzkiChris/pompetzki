# Master Book: format and merge rules (book-master, Abschluss 1.0)

Written 2026-10-10 by the book-master session (Area-51). Code: `code\book-merge.rkt` (writer), `code\master-verify.rkt`
(checker). This file is the contract both follow.

## 1. Layout

`book-master\book\J000001.txt`, `J000002.txt`, … — lane L9's journal layout (the shipped Book in
`handin\queue\Q23-book\book\book\`), so the shipped tools read it unchanged: `tools\bookverify.rkt` (Q23),
`book-index.rkt` (Q89) and `book-html.rkt` (Q30).

One record per line, LF line ends, UTF-8, fields separated by TAB. The last field of every record is its chain value:

    chain(i) = sha256( chain(i-1) as 64 lowercase hex digits ++ LF ++ the record's other fields joined by TAB )
    chain(0) = 64 zeros

The chain runs through all segments in file order (J000001 first). Record ids: a kind letter and a number, numbers per
kind run 1, 2, 3 … without gaps over the whole journal; B ids have 7 digits, all others 6.

Append-only: the writer creates every segment file new (an existing file name stops it; nothing is overwritten). A
later merge adds segments after the last one and continues the chain and the numbering; it never changes an existing
segment. A source whose ledger sha256 already appears in an H record is not merged again.

## 2. Segments and sources

One segment per merged source:

- segment 1: the shipped Book (Q23-book, 5 L9 segments, chain head afbb82ae…c4ab): its F, B, N and S records in
  journal order. Its 2 C records (period closes) belong to the shipped Book's own numbering and are not carried;
  they are listed in the report. The shipped journal has two parts, decided separately like a ledger pair: the
  accepted part (F, B and the 17 S records) and the rejected part (N). A part held in one run merges in a later run,
  in a new segment with source SHIPPED; H field 9 says which part a segment merged ("B PASS B…", "N PASS N…";
  anything else, e.g. "N PASS 1 of 2" or "N -", means that part is not in the segment).
- then one segment per ledger pair (a folder holding BOOK-1.0.ledger and/or NEGATIVE-1.0.ledger), in the order of
  `inventory.tsv` (BOOK ledger modification time, then pair id), taking only the ledgers `MERGE-PLAN.tsv` marks MERGE:
  F and B records of the BOOK ledger first, then the N records of the NEGATIVE ledger.

A ledger is marked MERGE only when (a) its sha256 now equals the inventory's, (b) Q122's `ledger-verify.rkt` passes it
(chain, grammar, ranges, counts), (c) 2 of its records were spot-checked by re-running both judges on their files and
both picks PASS (`code\spotcheck.rkt`). A ledger with no record to check merges nothing. A ledger whose 2 picks could
not be run (file absent, recorded judge time over the 600 s limit) or did not PASS is HELD, with the reason.

The writer re-reads each merged source, recomputes its chain record by record and stops on any difference, and checks
the source file's sha256 against `MERGE-PLAN.tsv` before reading it.

## 3. Records (field positions are 0-based; extra fields are added after L9's, before the chain)

### H — segment head
    0 H<k>  1 segment book/J<k>.txt  2 previous - -  |  previous book/J<k-1>.txt <sha256 of that file>
    3 opened <DATE>  4 book-merge.rkt <sha256>  5 racket.exe <sha256>
    6 source <pair id | SHIPPED>
    7 book <path> sha256 <hex> head <chain head> records <lines>      |  book -
    8 negative <path> sha256 <hex> head <chain head> records <lines>  |  negative -
    9 spotcheck <B part> ; <N part>
      a part this segment merges: "B PASS <id>,<id>" / "N PASS <id>,<id>" (the 2 spot-checked source records);
      a part it does not merge (that ledger absent, held, or already merged): "B -" / "N -", or, for SHIPPED, the
      decision text of the held part (e.g. "N PASS 1 of 2") — anything not of the form "PASS <id>,<id>".
      [amended 2026-10-10 06:39: the first text said "B none" / "N none"; the writer has always written "-"]
(for SHIPPED, field 7 is `book <folder> segments 5 head <hex> records <lines>` and 8 is `negative -`; the shipped
journal holds its N and S records itself.)

### F — judged file accepted by both judges
    0 F<n>  1 file <path>  2 sha256 <hex>  3 bytes <n>  4 source <folder>  5 registry <n0> prefix <hex>
    6 theorems <m>  7 steps <total>  8 pmp <verdict text>  9 racket <verdict text>  10 verdicts <name>
    11 postings B<x>-B<y> | postings -          (the master B ids of the file's postings that were booked here)
    12 stmt <hex> | stmt -                      (source's; the shipped Book's F records have none: "-")
    13 ax …  14 def …  15 hypent …              (source's; for the shipped Book: the union of its postings' traces)
    16 receipt <path>                           (source's; for the shipped Book: lanes\L9\verdicts\<verdicts name>)
    17 posted <date>                            (source's; for the shipped Book: its segment's H "opened" date)
    18 booked <k> duplicates <d>                (k + d = m)
    19 from <source F id> <source chain value>
Fields 0–11 keep L9's positions and meaning; 12–17 are Q10's (book-post.rkt) additions.

### B — posting
    0 B<n>  1 F<n> (master)  2 thm <j>  3 entry <e>  4 Proved | Qualified  5 stmt <hex>  6 drv <hex>  7 steps <s>
    8 hyps …  9 first B<n> | first -  10 cites …  11 ax …  12 def …  13 hypent …  14 file <sha256>
    15 registry <hex>  16 source <folder>  17 pmp ACCEPT <time>  18 racket ACCEPT <time>
    19 pmp-verdict <the F record's full pmp verdict text>  20 racket-verdict <the F's full racket verdict text>
    21 verdicts <name>  22 receipt <path>  23 from <source B id> <source chain value>
Fields 0–18 are L9's B record. Changed from the source: the B and F ids (master numbering), `first` (the master id of
the first posting with the same stmt, "-" when this is that posting), and the B ids in `cites` (mapped to master ids;
a cited posting that was a duplicate maps to the master posting with the same stmt and drv). R<n> cites are kept.
Every other field is copied byte for byte.

### N — file rejected by both judges
    0 N<n>  1 Rejected  2 file <path>  3 sha256 <hex>  4 bytes <n>  5 source <folder>  6 pmp REJECT …  7 racket REJECT …
    8 verdicts <name>  9 receipt <path>  10 posted <date>  11 from <source N id> <source chain value>
(shipped Book N records have no receipt/posted fields: receipt and posted are derived as for F.)

### S — suspense (shipped Book only: pmp stopped at its gosub depth bound, the Racket verdict alone)
    0 S<n>  1 reason …  2 file  3 sha256  4 bytes  5 source  6 pmp …  7 racket …  8 verdicts <name>
    9 receipt <path>  10 posted <date>  11 from <source S id> <source chain value>

### E — segment end
    0 E<k>  1 segment book/J<k>.txt  2 records <records of the segment before E, H included>
    3 F<a>-F<b> | F -  4 B… | B -  5 N… | N -  6 S… | S -  7 C -  8 closed <DATE>
    9 duplicates F <a> B <b> N <c> S <d>       (source records of this segment not booked because already booked)
Fields 0–8 are L9's E record (bookverify.rkt checks them).

## 4. Duplicates and conflicts

- B: key = (stmt, drv). The first posting with a key is booked; every later one is a duplicate.
- F: key = file sha256. An F whose sha256 was booked before and all of whose postings are duplicates is not booked.
  (If such a file had a new posting the F is booked anyway and the case is listed in CONFLICTS.tsv.)
- N, S: key = file sha256 (within the kind).
- Every record not booked is a row of `DUPLICATES.tsv`: kind, source pair, source id, source chain, key, and the master
  id it duplicates. Nothing is dropped without a row.
- `CONFLICTS.tsv`: a file sha256 that is both accepted (F) and rejected (N), or booked F twice; listed, still booked.

## 5. Checks of the result

- `code\master-verify.rkt`: the chain, ids, H/E links and counts; every B has both ACCEPT verdicts, both full verdict
  texts, a receipt and a `from`; no two B with the same (stmt, drv); every `first`/`cites` B id points to an earlier
  posting; and, for every record, the `from` reference: the source record (by id) in the named source ledger has that
  chain value and the same unchanged fields.
- the shipped `tools\bookverify.rkt` (Q23) on `book-master`.
- an independent checker written from this file alone (`code\master-verify-indep.rkt`).
