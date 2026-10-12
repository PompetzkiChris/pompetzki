# Accountability round 47ccf28

Public `codex/exact-release-repair` at full SHA `47ccf28cb37f2f5846a68cfefddb07e4a433406f` (`git ls-remote` verified). Fresh anonymous checkout `/workspace/acct-47cc`. 2026-10-11 ~22:20 EDT.

## 1. Hash table (measured)

| Path | sha256 | Notes |
|---|---|---|
| `judge/judge-v3.pmp` | `bf147194d415d0ab6991b5912c718c772f4bcb285ea027326fc5a108a81e6ce7` | |
| `judge/judge-v4.pmp` | `c0698f6c00310e4cf95147d4ddfbfab0f8c06d00aa8f9ca1da8482123c073e33` | |
| `judge/judge-v4.rkt` | `13bffe0ca241b5c4b179e6be25a52a164178b71fc03f913e3b92cc5c2576acc0` | |
| `judge/judge-v5.pmp` | `4d936cb8103c6aa97fb6ec290f88b3ee636c69f94f0cdb089a4621d9ba251d1b` | matches PROVENANCE / SHA256SUMS-source-v5 |
| `judge/judge-v5.rkt` | `c63bd449af3a7653c483b9bb42039b2942f658614bc2606eb7b40c5b95b6b2d0` | |
| `judge/registry-auth-v4.rkt` | `7369c098521020283016dbe86845790e7456be6ef255d8204ab696b6e4723a26` | |
| `judge/racket/judge.rkt` (v1.2 era) | `d6cf694c294a829172976ebd6741d15e39d91f5cb2feb09951421e5212c079ca` | |
| `repair/runtime/source/pompetzki.asm` | `778a2710b4151bad5a71c1bbdf5b5243d86d01f2a654fd727f341d589f2289db` | = portable-interpreter source |
| `repair/runtime-v2/source/pompetzki.asm` | `2329d3c993abfc5a89b979e6caae0b47aabdc12ec1858d752134a71a4e014f2e` | matches runtime-v2 SHA256SUMS + README |
| `repair/libraries/strx/strx.pmp` | `05b773ce83c0c7da3dab6833ee7c9de720de773274c4e2ea16c7b6f59536702f` | |
| `judge/native-v5/portable/{build-native.py,pmpc-original.rkt,linux-runtime.asm}` | `acae7180…` / `660399e1…` / `89a9c945…` | match SHA256SUMS-source-v5 |
| **Committed** `judge/native-v5/judge-v5-linux` | `1b890cedd973b2815bd4be436adb60737b08162ba48c4ef4196241ccb01affad` | matches `native-provenance.json`; not executable in checkout until `chmod +x` |
| **Committed** `judge/native-v5/judge-v5-windows.exe` | `b9e2ed070340d6ec926caca0f3c71929137e3a9bf2650ba6bc78c94e880e7545` | matches provenance; not run (no Wine) |
| **Built here** runtime-v2 Linux | `6589662d0d3197d296974b3ba1c4785aa1cc56a0217b917047023baac4097ba9` | `build-interpreter.py --target linux` |
| **Built here** native judge-v5 Linux | `4c1c90b9d171ca7ddecc6d0d1851712f4dde970ef5fd752f134ee5b4cabbed22` | `native-v5/portable/build-native.py`; **≠ committed** (path-dependent link), behaviour matched on all controls below |
| `bin/linux/pompetzki` | `414e976b9ef34b3cf971d947bd0060347eb1bf77564333caf5944ff4067382a7` | historical public ELF |

### Receipt mismatches / quirks

| Claim | Verified outcome |
|---|---|
| `repair/runtime-v2/SHA256SUMS-source.txt` (6 files) | **All MATCH** |
| `judge/native-v5/portable/SHA256SUMS-source-v5.txt` content hashes | **All MATCH** when mapping `PROVENANCE.json`→`PROVENANCE-v5.json`, `README.md`→`README-v5.md`, `SOURCE-INPUTS.json`→`SOURCE-INPUTS-v5.json` |
| Same SUMS **filenames as written** | **NAME MISMATCH**: listed paths `PROVENANCE.json` / `README.md` / `SOURCE-INPUTS.json` do not exist; only `*-v5.*` names exist. Content OK under alias. |
| README / provenance source hashes for v5.pmp, runtime-v2 asm, portable-interp asm | **MATCH** |
| Self-built `judge-v5-linux` vs committed artifact hash | **MISMATCH** (`4c1c90b9…` vs `1b890ced…`); both pass the same behavioural controls after `chmod +x` on the committed ELF |

## 2. Defect controls & padding (exact)

| Claim | Command | Actual output | Verified outcome |
|---|---|---|---|
| (a) false registry rejected by v5 native / interpreted / racket | `judge-v5-linux` / `runtime-v2 judge-v5.pmp` / `racket judge-v5.rkt` on `a1`/`a2` | `REJECT` … `entry differs from canonical REG0`, exit 1 (all) | **PASS** |
| (a) canonical REG0 accepted | same on `ctl-canonical-reg0.jdg` | `ACCEPT` … `706`, exit 0 (all) | **PASS** |
| (a) committed `judge-v5-linux` (after chmod) | same | REJECT / ACCEPT as above | **PASS** (was exit 126 Permission denied until chmod) |
| (b) INT64_MIN literal on runtime-v2 | `pompetzki b1-literal-min.pmp` | `-9223372036854775808`, exit 0 | **PASS** |
| (b) computed INT64_MIN | `b2` | `-9223372036854775808`, exit 0 | **PASS** |
| (b′) INT64_MIN div -1 | `d1` | `-9223372036854775808`, exit 0 | **PASS** (wrap; no SIGFPE) |
| (b′) INT64_MIN mod -1 | `d2` | `0`, exit 0 | **PASS** |
| (c) strx embedded NUL on runtime-v2 | `c1-trim-nul.pmp` + repaired strx | `3 97 0 98 32 0 98`, exit 0 | **PASS** |
| Pad: `R 0000000000706` (13-digit token, value 706) | v5 n/p/r | ACCEPT 706 | **PASS** (v5); v4 `REJECT a number has more than 12 digits` |
| Pad: `R 000000000706` (12 digits) | v5 + v4 | ACCEPT | **PASS** |
| Pad: entry `e 000000000000 000000000002` (12-digit pads) | v5 + v4 | ACCEPT | **PASS** |
| Pad: `e 0 0000000000002` (12 zeros then 2 = value 2) | v5 n/p/r | ACCEPT 706 | **PASS**; v4 REJECT (>12 digits) |
| Pad: `e 0000000000000 0000000000002` (13 zeros / 12z+2) | v5 | ACCEPT | **PASS**; v4 REJECT |
| Pad: `R` = 13 zeros (value 0) | v5 | ACCEPT registry 0 | **PASS**; v4 REJECT |
| Pad: `R` = 12 zeros | v5 + v4 | ACCEPT registry 0 | **PASS** |
| 13 **significant** digits `e 1000000000000 …` | v5 n/p/r | `REJECT a number has more than 12 significant digits`, exit 1 | **PASS** (v5 choice: reject 13th sig digit; message says “significant digits”) |
| Fixture `leading-zero-and-tab-prefix.jdg` | v5 n/r, v4 | ACCEPT | **PASS** |

**v5 padding policy observed:** leading zeros do not count toward the 12-significant-digit bound; tokens of any length that denote an integer in `0..999999999999` are accepted; a 13th significant digit is rejected before arithmetic. Integer equality (not digit-string equality) is used for REG0 auth, so padded spellings of canonical values authenticate.

## 3. Branch `grok/embedded-reg0-gate` (`cd40e50eaeb3fe910b36cc8a60a0610454b70c29`)

Diff vs merge-base `52e4a28`: **only two files added**

| File | sha256 | Implementation bytes? |
|---|---|---|
| `audit/reg0-embedded-gate/AUDIT-RECEIPT.md` | `8fa19df8baa34b7f149d7062030516b4fcd9fe814471671061befe89ad93c5d3` | No — markdown claims + archive hashes |
| `audit/reg0-gate-v5/PADDING-AND-RUNTIME.md` | `9ce895c839cfe28d10a6ce692b253007d363e1d6cdfbed63d70fd572127f1f66` | No — markdown claims + padding table |

No `*.pmp` / `*.rkt` / `*.asm` / binary implementing a gate was added on that branch. Referenced zip archives are **not** in the branch tree.

| Claim on that branch | Verified outcome |
|---|---|
| Embedded REG0 gate correction / executed API checks / padding ALL PASSED / runtime-v2 guards | **NOT COUNTED** (audit receipt only; no implementation to build or run here) |
| Zip hashes `26ada064…`, `917b30b3…`, `d773b4e5…` | **NOT COUNTED** (archives absent from the branch) |

(The v5 + runtime-v2 implementations that those receipts describe **are** on `codex/exact-release-repair` at 47ccf28 and were built/tested in §1–2.)

## Limits

Finite tests do **not** establish executable/Gallina correspondence. Self-built native ELF hash ≠ committed ELF hash; behaviour matched on the controls run. Windows committed EXE not executed.


Raw stdout for every case is also concatenated in `raw/all-stdout.txt` (individual key captures kept).
