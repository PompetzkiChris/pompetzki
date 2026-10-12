# v5 registry gate and Linux runtime-v2

Additive archive, beside the two earlier packages. Their bytes were rechecked after this zip was written:

```text
26ada0641eecb84b9fde9181ad41407aa31cd167f09b4767a926376cabfc13bc  reg0-gate-v5-runtime-v2-2026-10-12.zip
254011 bytes

917b30b3aec0d5fc84afdd0733861fae7229d21114e6b0ac87f238bb2bade841  reg0-initial-registry-gate-2026-10-11.zip
74542 bytes

d773b4e529eaf70713baad0c15618bbe5d8f355906904a1c9b72faaf1fd73402  reg0-embedded-gate-2026-10-12.zip
85105 bytes
```

The 2026-10-12 archive is the 12-digit gate. v5 treats a digit token of any length as that integer. Leading zeros do not change the value. Thirteen or more digits are not a parse error. The embedded AUTHREF literal is still public judge-v4.pmp at 63f45bbcaa88e370827d2dd2e95a6d422fb8c589, sha256 d3dbc73283b61a2ba72431552d33c1810e140e24bbfda85b1a30aef006dac047. No external REG0.canon is read. Theorem REG0_ok stays the proved theorem. Executable correspondence with Gallina check_batch remains open.

## Padding, executed

Command, from reg0-gate-v5, using released Linux pompetzki sha256 414e976b9ef34b3cf971d947bd0060347eb1bf77564333caf5944ff4067382a7:

```text
python3 test_padding.py
```

Log: reg0-gate-v5/tests/padding-output.txt. Last line: ALL PADDING CHECKS PASSED. failures 0. pmp and Python agreed. Re-run after deleting an unused MAX_DIGITS constant; the verdicts did not change.

| input | spec | v4-cap | v5 |
|---|---|---|---|
| 12 zeros then 2 (13 digits) | GATE | REJECT parse | GATE |
| exactly 12 zeros | GATE | GATE | GATE |
| 13, 64, 1024 zeros then 2 | GATE | REJECT parse | GATE |
| 13, 64, 1024 zeros | GATE | REJECT parse | GATE |
| 11 zeros then 2 | GATE | GATE | GATE |
| hyp count of 12 zeros | GATE | GATE | GATE |
| hyp count of 13 or 1024 zeros | GATE | REJECT parse | GATE |
| 64 nines, 1024 nines, 2 then 100 zeros, 9223372036854775807 | REJECT formula | REJECT parse | REJECT formula |
| hyp count 1 then 64 zeros | REJECT hypotheses | REJECT parse | REJECT hypotheses |
| 0.0 +2 -1 2a 0x2 . 2. | REJECT parse | REJECT parse | REJECT parse |

Racket was not executed in this sandbox. Python is the cross-check that ran.

## runtime-v2, executed on Linux

Source commit a2293a309bcb5f171914bff78129ba59e4e2fa44.

```text
2329d3c993abfc5a89b979e6caae0b47aabdc12ec1858d752134a71a4e014f2e  source/pompetzki.asm
5450cb80e0264e1844f9e3e4130de0dfeb8be7c0ca28adf036921f1ee7dbdf7d  build-linux/pompetzki
```

NASM 2.16.03, `nasm -DLINUX -f elf64`, then `ld -e _start`. Both steps exit 0. Assembler stderr empty. Source-to-executable correspondence is open.

```text
python3 linux-word-guard.py
```

368 div/mod cases (8x8 corners and 120 random pairs, seed 20261011), failed_assertions 0.

| program | result | exit |
|---|---|---|
| div -9223372036854775808 by -1 | -9223372036854775808 | 0 |
| mod -9223372036854775808 by -1 | 0 | 0 |
| literal -9223372036854775808 | -9223372036854775808 | 0 |
| literal div of that value by -1 | -9223372036854775808 | 0 |
| literal mod of that value by -1 | 0 | 0 |
| div by 0 | division by zero | 1 |
| emitted ELF of the literal division | -9223372036854775808 | 0 |

Released 2026-10-10 interpreter 414e976b9ef34b3cf971d947bd0060347eb1bf77564333caf5944ff4067382a7: the same non-literal pair dies with signal 8 (Python exit -8) for div and mod. Its literal is rejected, exit 1. Public Windows test-word-division.py was not run. There is no Windows executable in this archive.
