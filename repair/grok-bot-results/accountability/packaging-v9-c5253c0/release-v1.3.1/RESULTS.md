# Release v1.3.1: anonymous verification run
Command: `verify-release-1.3.1.sh WORK /workspace/acct-c525 Abschluss-1.3.1-windows-x64.zip=db3d4669…:200606657 Abschluss-1.3.1-source.zip=8db56c0c…:180990181 rdnum-finite-reader-proof-public.zip=9766d3b5…:131636`. Exit 0, `RESULT PASS` (raw/report.txt). API account fields and release.json are deliberately not stored.
Harness note: two bugs in my script were fixed before the recorded run. It picked only the first SUMS file, and it didn't strip CRLF from the SUMS files, which made SUMS show "absent". Only the final run is kept.

| Asset | Size | sha256 | API size/digest | SUMS file | Claim |
|---|---|---|---|---|---|
| Abschluss-1.3.1-source.zip | 180990181 | 8db56c0cd336d84f3c4b6f867324683c28f33e8c390f773926a4c21ac225282a | OK/OK | SHA256SUMS OK | **MATCH** (size+hash) |
| Abschluss-1.3.1-windows-x64.zip | 200606657 | db3d46690b1aae086539f25dabee0d1133fee6d8ac70d24f2eb9216550183c38 | OK/OK | SHA256SUMS OK | **MATCH** |
| rdnum-finite-reader-proof-public.zip (expanded-reader addendum) | 131636 | 9766d3b5ce274b2ac74567efb5b60cf0327591ce546ee358483277389dce99f0 | OK/OK | READER-V2-SHA256SUMS OK | **MATCH** |
| rdnum-instruction-steps-proof-public.zip | 100204 | bfcae55fa26e… | OK/OK | SHA256SUMS OK | — |
| SOURCE-CLOSURE-1.3.1.json | 16532 | 26b27715… | OK/OK | SHA256SUMS OK | — |
| validation-1.3.1-public.zip | 1424927 | 3490564f… | OK/OK | SHA256SUMS OK | — |
| SHA256SUMS.txt | 489 | aa3f502b… | OK/OK | self | — |
| READER-V2-SHA256SUMS.txt | 104 | 816586ba… | OK/OK | self | — |
8 assets, as claimed. Tag `v1.3.1` → c5253c0922f553b1ac8ef18240c1c372ff39657f (ls-remote); API `target_commitish` is the same. **MATCH.**

Bounded checks (raw/pins.txt, report.txt):
| Check | Source ZIP | Windows ZIP |
|---|---|---|
| 22 selected packaging files vs recipe | 22/22 present, 0 mismatches | not shipped (compiled bundle carries no packaging sources), 0 present (expected) |
| judge-v6.pmp 87562735… | MATCH | MATCH |
| judge-v6.rkt a16ffa34… | MATCH | MATCH |
| runtime-v2 asm 2329d3c9… | MATCH (`runtime/source/pompetzki.asm`) | n/a (binary interpreter: pompetzki.exe 957366e6…, pompetzki-w.exe d6c6e22a…, both unchanged from 1.3.0) |
| Book-v7 checker 8fa76a95… | MATCH | n/a (compiled) |
| matrix engine 99084a40… | MATCH | n/a (compiled MathEngine) |
| pinned native judge-v6-windows.exe 9b84cb4b… | MATCH (`vendor/gated-native/`) | MATCH (`judge/judge-v6-windows.exe`); `provenance/native-rebuild-comparison.json`: tested 9b84cb4b…, `rebuild_performed: false`, exact tested bytes shipped |
| VERSION | — | `1.3.1` |
The validation ZIP also contains the 22 rows, byte-identical. No broad suites were rerun. These hash checks do not establish formal correspondence.

## Native freeze outputs: are they now public? (raw/native-search.txt)
I computed sha256 for all 8 assets and every member of every ZIP, recursing into nested ZIPs: 6,395 files.
| Freeze row (NATIVE-V6-FREEZE.sha256) | Found in release? | Where |
|---|---|---|
| judge-v6-windows.exe 9b84cb4b… | **YES** | source ZIP `vendor/gated-native/judge-v6-windows.exe`; Windows ZIP `judge/judge-v6-windows.exe` |
| native-provenance.json 6c0d5d4a… | YES | source ZIP `vendor/gated-native/`; Windows ZIP `provenance/` |
| native-test-result.json 9ad99e7f… | YES | same |
| **judge-v6-linux 6db4c7df…** | **NO**: no file with that hash, and no file named judge-v6-linux in any asset | — |
Therefore 3 of the 4 earlier-missing freeze outputs are now public. The Linux native judge is still unavailable, so the stripped comparison against my build (a8b9179161f2…79fa) **could not be performed**. The bytes behind the Linux receipt rows in validation-v6-resource remain unverifiable. This is an artifact-availability limitation, not a test failure.
