# Registry gate v5

v5 sits beside the capped gate. It does not replace these archives:

```text
917b30b3aec0d5fc84afdd0733861fae7229d21114e6b0ac87f238bb2bade841  reg0-initial-registry-gate-2026-10-11.zip
74542 bytes

d773b4e529eaf70713baad0c15618bbe5d8f355906904a1c9b72faaf1fd73402  reg0-embedded-gate-2026-10-12.zip
85105 bytes
```

The embedded AUTHREF literal is still the public `judge-v4.pmp` literal at `63f45bb`, sha256 `d3dbc73283b61a2ba72431552d33c1810e140e24bbfda85b1a30aef006dac047`. No external `REG0.canon` is read. `Theorem REG0_ok` remains the proved theorem in `RpInitOk.v`, not an axiom added here. Executable correspondence with Gallina `check_batch` remains open.

## Digit rule

A token of one or more digits denotes that integer. Leading zeros do not change it.

| token | value |
|---|---|
| `2`, `02`, `000000000002` | 2 |
| `0`, `00`, twelve zeros, 1024 zeros | 0 |
| twelve zeros followed by `2` | 2 |
| `2` followed by 100 zeros | 2 × 10^100, not 2 |
| `0.0`, `+2`, `-1`, `2a`, `0x2`, `.` | not an integer token |

v4 `RDNUM`, and the 2026-10-12 capped gate copied from it, reject a token of 13 or more digits before using the value. Racket accepts the integer. That cap is the discrepancy. v5 does not apply it. Eighteen significant digits still fit in a signed machine word. A larger significant integer cannot equal a canonical REG0 number, so the gate reports formula or hypotheses, not parse. The proof judge is not started.

## Executed

`python3 test_padding.py` wrote `tests/padding-output.txt`. Both pmp and Python agreed.

The capped gate rejects `zeros12-then-2` (13 digits) as parse and accepts a 12-digit token. v5 accepts 12, 13, 64 and 1024 leading zeros on the value 2 and on the value 0, including a hypothesis count of those zeros. Sixty-four nines, 1024 nines, `2` followed by 100 zeros, and `9223372036854775807` are formula mismatches. A 10^64 hypothesis count is a hypothesis mismatch. The seven malformed tokens are parse failures. Preserved mutants and the public tab/leading-zero fixture keep the previous verdicts.

Command, from this directory, with the released Linux interpreter:

```text
python3 test_padding.py
```

The interpreter used was `pompetzki` sha256 `414e976b9ef34b3cf971d947bd0060347eb1bf77564333caf5944ff4067382a7`. It is not runtime-v2.
