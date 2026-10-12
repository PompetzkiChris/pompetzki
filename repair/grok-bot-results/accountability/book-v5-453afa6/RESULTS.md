# Book v5 accountability (453afa6)

Public `codex/exact-release-repair` full SHA `453afa610a32b3e94fe9d2fcccc700a6ecca73b4` (`git ls-remote` verified). Fresh checkout `/workspace/acct-453a`. Own harness (not the Book lane’s). 2026-10-11 ~22:30 EDT.

## Builds / hashes

| Item | sha256 |
|---|---|
| `judge/judge-v5.pmp` | `4d936cb8103c6aa97fb6ec290f88b3ee636c69f94f0cdb089a4621d9ba251d1b` |
| `judge/judge-v5.rkt` | `c63bd449af3a7653c483b9bb42039b2942f658614bc2606eb7b40c5b95b6b2d0` |
| `repair/runtime-v2/source/pompetzki.asm` | `2329d3c993abfc5a89b979e6caae0b47aabdc12ec1858d752134a71a4e014f2e` |
| `repair/libraries/strx/strx.pmp` | `05b773ce83c0c7da3dab6833ee7c9de720de773274c4e2ea16c7b6f59536702f` |
| Built runtime-v2 Linux | `3658455cbc09d42836e18b5e0aea4600dd17bef644f78f46557ded8928e47ce8` |
| Built native judge-v5 Linux | `47aad2214515c74ae60bb18b9168df82ecbec4cf7901b60bf18e7b5a1eaa5e68` |
| `verified-book-check.rkt` (= `-v5-source.rkt`) | `c9237281fccc1d3c1194ef85bcb9bf776ddb5074156c089690440ea04eeaa944` |
| `verified-book-post.rkt` | `c6779f520f1ce4438eda2cec01f36e0bc023c584f20233f1565d8c531040deb3` |

Bundle: native ELF renamed to `judge/judge-v5-windows.exe`; `pompetzki.exe` = runtime-v2.

## Defect controls (quick)

| Claim | Command | Output | Outcome |
|---|---|---|---|
| False registry REJECT (native / interpreted) | `judge-v5-linux` / `rtv2 judge-v5.pmp` on `a1` | `REJECT` … `entry differs from canonical REG0`, exit 1 | **PASS** |
| Canonical REG0 ACCEPT | native on `ctl-canonical-reg0` | `ACCEPT` … 706, exit 0 | **PASS** |
| INT64_MIN literal / div / mod on runtime-v2 | `b1`,`d1`,`d2` | `-9223372036854775808` / wrap MIN / `0` | **PASS** |
| strx embedded NUL | `c1-trim-nul` | `3 97 0 98 32 0 98` | **PASS** |

## Book v5 attacks

| Claim | Command | Output | Outcome |
|---|---|---|---|
| Valid post native `ok-hyp.jdg` | `verified-book-post --bundle B OUT DATE ok-hyp` | exit 0; ACCEPT/ACCEPT; F1 B1 Qualified | **PASS** |
| Valid post `--interpreted` | same + `--interpreted` | exit 0; pmp=`pompetzki.exe judge-v5.pmp …` | **PASS** |
| Check both | `verified-book-check` | `"status":"CHECK OK"`, `evidence_schema":"verified-book-v5"` | **PASS** |
| Genuine m1 REJECT post+check | post/check `m1-refl` | N1; CHECK OK | **PASS** |
| Fully consistent false-proof forgery (m1 as ACCEPT; logs/RECEIPTS/metadata/hashes/stmt·drv `e032a160…`/`08368b17…`; chains recomputed) | check forge | `CHECK FAILED: rerun differs from stored verdict`, exit 1 | **REJECTED** (earlier incomplete forge failed at RECEIPTS first; cleaned forge reaches rejudgment and still fails) |
| Rehashed theorem (flip B stmt, rechain) | check | `B record differs from the complete checked theorem evidence`, exit 1 | **REJECTED** |
| Ambiguous ACCEPT+REJECT judges | post with amb bundle | exit **3**; `SUSPENSE 1` … `UNKNOWN` | **REJECTED at post** |
| Check ambiguous posting | check vs amb bundle | `stored verdict/exit code differs`, exit 1 | **REJECTED** |
| Orphan N ledger row | check | `input/receipt/ledger counts differ`, exit 1 | **REJECTED** |
| Unreferenced file in `judge-runs/` (v4 GAP) | check + `orphan.stdout.txt` | `"status":"CHECK OK"`, exit 0 | **GAP REMAINS** — v5 does **not** close judge-runs orphans |
| Unrecorded extra snapshot in `judge-inputs/` | check + `extra.jdg` | `snapshot directory contains unrecorded or duplicate inputs`, exit 1 | **CLOSED** (new in v5) |
| Changed input after judging | replace snapshot bytes | `snapshot hashes or unchanged state differ`, exit 1 | **REJECTED** |
| Bad F sha256 rechained | flip F sha | `F/N input identity, bytes, source or date differs`, exit 1 | **REJECTED** |
| Duplicate RECEIPTS row | duplicate data line | `duplicate RECEIPTS input identity`, exit 1 | **REJECTED** |
| Reordered B id (`B0000002` alone) | check | `B record shape/ordered ID/F link differs`, exit 1 | **REJECTED** |
| Wrong F byte count | `bytes 1` | `F/N input identity, bytes, source or date differs`, exit 1 | **REJECTED** |
| Tampered/unordered timestamps | racket start &lt; prior pmp end | `metadata timestamps are inexact, negative or unordered`, exit 1 | **REJECTED** |
| Existing output refused | re-post to same OUT | `output already exists`, nonzero | **REFUSED** |
| Full 4551-theorem replay | `test-full-replay.py` | — | **SKIPPED** (not run; would need multi-minute posting; recorded in raw) |

## Limits

Finite tests do not establish executable/Gallina correspondence. Extra files under `judge-runs/` that are not named in metadata remain unchecked. Snapshot directory extras are now rejected.

## Addendum: stripped native judge-v5-linux

Compared self-built `judge-v5-linux` (`47aad221…5e68`, 113368 bytes) to committed `judge/native-v5/judge-v5-linux` (`1b890ced…ffad`, 113416 bytes) after `objcopy --strip-all` on copies of both:

| Artifact | sha256 after `--strip-all` | size |
|---|---|---|
| built-stripped | `1cf6cea0d711d68768c332fb67e18d28271c04a17bceb2746f78b1403a1daf4f` | 94480 |
| committed-stripped | `1cf6cea0d711d68768c332fb67e18d28271c04a17bceb2746f78b1403a1daf4f` | 94480 |

**Verified outcome: MATCH** (`cmp` identical; `strip --strip-all` same). Pre-strip hash difference is non-code metadata (e.g. build paths/symbols); code sections match when stripped. Both stripped copies still REJECT the false-registry control (exit 1).
