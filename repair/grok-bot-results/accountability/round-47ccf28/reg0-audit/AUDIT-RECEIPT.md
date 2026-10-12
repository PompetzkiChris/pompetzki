# Embedded REG0 gate

This branch was opened from `codex/exact-release-repair` at `52e4a28ecf47c9e06b230d975c04a174272a3cdf`.
The v4 judges under test are commit `63f45bbcaa88e370827d2dd2e95a6d422fb8c589`.

The corrected gate embeds that commit's `judge-v4.pmp` AUTHREF literal. It does not read `REG0.canon`. Decimal spellings compare as integers: `02` is 2 and `00` is 0. An altered external canon plus a forged matching input is rejected before the proof judge. `Theorem REG0_ok` in `rocq/RpInitOk.v` at `e8958a92` is `Proof`/`Qed`, not an extra axiom. Executable correspondence with Gallina `check_batch` remains an open obligation.

Executed here: 3538/3538 API checks, 16 preserved mutants, 14 public v4 fixtures against `judge-v4.pmp`, the altered-canon attack, and the three spelling files through released `judge-v3.pmp`. Python and `reggate.pmp` agreed. The run log is inside the archive.

## Archives

Previous archive, bytes unchanged:

```text
917b30b3aec0d5fc84afdd0733861fae7229d21114e6b0ac87f238bb2bade841  reg0-initial-registry-gate-2026-10-11.zip
74542 bytes
```

Corrected archive:

```text
d773b4e529eaf70713baad0c15618bbe5d8f355906904a1c9b72faaf1fd73402  reg0-embedded-gate-2026-10-12.zip
85105 bytes
```

AUTHREF sha256 `d3dbc73283b61a2ba72431552d33c1810e140e24bbfda85b1a30aef006dac047`.
Public `judge-v4.pmp` sha256 `c0698f6c00310e4cf95147d4ddfbfab0f8c06d00aa8f9ca1da8482123c073e33`.
Released `judge-v3.pmp` sha256 `bf147194d415d0ab6991b5912c718c772f4bcb285ea027326fc5a108a81e6ce7`.
RpInitOk.v sha256 `827498d05d92fd334a093273b1bdf13ef5fa11e643b84b2fa8ac83dff07d8bf3`.
