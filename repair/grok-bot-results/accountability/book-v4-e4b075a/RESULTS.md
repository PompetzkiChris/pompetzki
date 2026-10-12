# Book v4 accountability (e4b075a)

Independent attack of `repair/book-v4` at `codex/exact-release-repair` commit `e4b075a1df98f454a0536ca8ed135b6911769efc`. Fresh public clone `/workspace/acct-e4b0`. Own harness (not the Book lane's). 2026-10-11 ~22:10 EDT.

## Builds / bundle

| Item | Identity |
|---|---|
| Interpreter | `nasm -DLINUX -f elf64 repair/runtime/source/pompetzki.asm` + `ld` → sha256 `b8725cbd…7fcc` (source `778a2710…89db`) |
| Native judge-v4 | `build-native.py --target linux` → sha256 `a715ee69…8b93`, installed in the test bundle as `judge/judge-v4-windows.exe` (name the poster looks for) |
| Bundle layout | `/workspace/bundle-e4b0`: `pompetzki.exe` = Linux interpreter; `judge/judge-v4.pmp`, `judge/judge-v4.rkt`, native ELF as above |
| Note | Runtime source at e4b075a still SIGFPEs on INT64_MIN÷−1; `repair/runtime-v2` at a2293a3 does not. Book tests do not exercise that path. |

## Results

| Claim | Command | Actual output | Verified outcome |
|---|---|---|---|
| Valid posting (native default) of `judge/mut/ok-hyp.jdg` | `racket verified-book-post.rkt --bundle B OUT DATE ok-hyp.jdg` | exit 0; `pmp ACCEPT racket ACCEPT`; `BOOK … F 1 B 1 … Qualified 1`; `SUSPENSE 0`. Metadata pmp command = native ELF. | **PASS** |
| Valid posting `--interpreted` | same with `--interpreted` | exit 0; ACCEPT/ACCEPT; pmp command = `pompetzki.exe judge-v4.pmp <snapshot>` | **PASS** |
| Check of both postings | `racket verified-book-check.rkt --bundle B POSTING` | exit 0; `"status":"CHECK OK"`, theorems 1. Rejudgment uses the native judge even for the interpreted posting (by design of the checker). | **PASS** |
| Genuine REJECT of `m1-refl.jdg` posts + checks | post then check | post exit 0, `N 1`; check `"status":"CHECK OK"`, negative_files 1, pmp/rkt REJECT | **PASS** |
| Fully consistent false-proof forgery | Rewrite m1 REJECT posting as ACCEPT: logs, RECEIPTS.tsv, run-metadata.json (verdicts/exits/hashes), BOOK F+B rows with **authentic** stmt/drv of m1 theorem 0 from `inspect-jdg` (`stmt e032a160…`, `drv 08368b17…`), NEGATIVE emptied; recompute both ledger chains bound to new metadata sha | `CHECK FAILED: rerun differs from the stored verdict`, exit 1 | **REJECTED (defender wins)**. Self-consistent ledger+metadata is not enough; rejudgment catches the false proof. |
| Rehashed-theorem | Valid ok-hyp posting; flip last nibble of B `stmt` hash; recompute BOOK chain | `CHECK FAILED: theorem posting differs from its checked derivation`, exit 1 | **REJECTED** |
| Ambiguous ACCEPT+REJECT | Bundle with native+racket judges printing both words, exit 0; post ok-hyp | post exit **3**; `pmp UNKNOWN racket UNKNOWN`; `SUSPENSE 1 … verdicts pmp UNKNOWN exit 0, racket UNKNOWN exit 0`. Check of that posting: `stored verdict and exit code differ`, exit 1 | **REJECTED at post (SUSPENSE)** and at check |
| Orphan ledger N row | Valid posting + extra N record in NEGATIVE with recomputed chain | `CHECK FAILED: ledger includes postings without a checked input`, exit 1 | **REJECTED** |
| Orphan unreferenced file in `judge-runs/` | Valid posting + extra `orphan.stdout.txt` not named in metadata | `"status":"CHECK OK"`, exit 0 | **GAP**: extra files outside the metadata binding are ignored. Not a verdict forgery by itself. |
| Changed input after judging | Replace snapshot bytes with m1 without updating hashes | `CHECK FAILED: snapshot input hash differs`, exit 1 | **REJECTED** |
| Bad F sha256 in ledger (chain recomputed) | Flip F sha256 to `bbb…` | `CHECK FAILED: judge run has no corresponding ledger record`, exit 1 | **REJECTED** |
| Direct receipt import refused | `racket book-post-v4.rkt RECEIPTS.tsv OUT DATE` | stderr `Use verified-book-post.rkt to run the judges…`, exit 2 | **REFUSED** |
| Existing output refused | re-post to `post-default` | `book-post: output already exists: …`, nonzero | **REFUSED** |

## Limits

- Finite tests do **not** establish executable/Gallina correspondence, nor that the JDG parser matches the Rocq checker.
- The checker rejudges with the **native** Linux ELF when present; it does not re-run the interpreted path.
- Orphan files not referenced by `run-metadata.json` are not hashed or refused.
- Attacks were run against a locally assembled Linux bundle that renames the native ELF to `judge-v4-windows.exe` to satisfy the poster's Windows-oriented search. Behaviour of a real Windows `judge-v4-windows.exe` was not exercised.

Raw captures: `raw/*.stdout`, `raw/small-captures.txt` (exits/stderrs), forge trees were not archived (reproducible from the scripts' description above).
