# Gate source on this branch

This directory is the implementation. The receipts under `audit/reg0-embedded-gate/` and `audit/reg0-gate-v5/` only describe it.

`v5/` is the current gate. `v4cap/` is the preserved 12-digit gate. Neither reads `REG0.canon`. The trusted text is the AUTHREF literal inside `embed_data.py` and `reggate.pmp`. `Theorem REG0_ok` is not redefined here. Executable correspondence with Gallina `check_batch` is open.

A digit token denotes that integer. Leading zeros do not change it. v5 accepts 13 or more digits of padding. v4cap rejects a token longer than 12 digits as parse. This tree is not `codex/exact-release-repair` `47ccf28`. That revision declares an index domain of 0 through 999999999999.

## Run

From the repository root, with the released Linux interpreter or any later one:

```text
POMPETZKI=/path/to/pompetzki python3 audit/grok-gate/v5/test_padding.py
python3 audit/grok-gate/v5/gate.py audit/grok-gate/mutants/fail-false.jdg
POMPETZKI=/path/to/pompetzki /path/to/pompetzki audit/grok-gate/v5/reggate.pmp audit/grok-gate/mutants/fail-false.jdg
```

`POMPETZKI` defaults to `pompetzki` on `PATH`. The padding log already produced by that command is `v5/tests/padding-output.txt`. The capped-gate log is `v4cap/tests/linux-output.txt`. `v4cap/test_all.py` still contains the sandbox paths from the machine that wrote that log.

Python is the oracle (`gate.py`). Racket was not executed for this tree.

These local archive bytes are not in git and were not rewritten:

```text
917b30b3aec0d5fc84afdd0733861fae7229d21114e6b0ac87f238bb2bade841  reg0-initial-registry-gate-2026-10-11.zip
74542 bytes

d773b4e529eaf70713baad0c15618bbe5d8f355906904a1c9b72faaf1fd73402  reg0-embedded-gate-2026-10-12.zip
85105 bytes
```
