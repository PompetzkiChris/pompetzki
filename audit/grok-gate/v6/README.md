# v6 domain correction

v5 at `audit/grok-gate/v5` is unchanged. This directory is the correction.

A digit token is an integer in 0..999999999999. Leading zeros are skipped and do not count. The 13th significant digit is `REJECT registry` / `parse`, before `int()` and before a proof judge. `sys.set_int_max_str_digits` is not called.

`judge-gated-v5.sh` and `judge-gated-v5.ps1` run this gate, then `judge/judge-v5.pmp` from commit `7b40504` (same bytes at `c886685`). They do not call judge-v3. The v5 wrappers are still the judge-v3 route.

```text
POMPETZKI=/path/to/pompetzki python3 audit/grok-gate/v6/test_long_padding.py
POMPETZKI=/path/to/pompetzki python3 audit/grok-gate/v6/test_wrapper.py
```

Executable correspondence with Gallina remains open.
