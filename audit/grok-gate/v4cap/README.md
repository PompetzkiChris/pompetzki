# Embedded canonical-registry gate

Correction of the 2026-10-11 external-file gate. Decimal spellings of the same integer are the same token, and the canonical reference is the literal embedded in the program. An outside `REG0.canon` is not authority.

The previous archive is unchanged:

```text
917b30b3aec0d5fc84afdd0733861fae7229d21114e6b0ac87f238bb2bade841  reg0-initial-registry-gate-2026-10-11.zip
74542 bytes
```

## What changed

The public v4 judges (`judge/judge-v4.pmp`, `judge/judge-v4.rkt` at `63f45bbcaa88e370827d2dd2e95a6d422fb8c589`) compare tags and exact decimal integers. Whitespace is a delimiter. `02` means 2 and `00` means 0. Their reference is a text literal inside the program. `REG0-canonical.jdg` is an export; changing it does not change the judge.

The previous gate compared raw spellings, so `02` and `00` were rejected, and it trusted whatever file `REG0.canon` or `REG0_CANON` named. Both of those are regressions against v4. This package follows the v4 rule.

A numeric token is one to twelve digits, the same bound as `RDNUM` in `judge-v4.pmp`. The value is the integer. Space, tab, CR and LF are delimiters. `0.0` is not an integer token. More than 706 initial entries is a count refusal. A formula or hypothesis mismatch is a registry refusal. `T` is required after the prefix so a registry refusal happens before the proof judge. The proof judge is the released `judge-v3.pmp`, called only after `GATE`.

## Embedded reference

`embed_data.py` and the `text AUTHREF` line in `reggate.pmp` are the AUTHREF literal from public `judge-v4.pmp`, byte for byte:

```text
d3dbc73283b61a2ba72431552d33c1810e140e24bbfda85b1a30aef006dac047
```

706 entries, each closed by `!`. Compared as integers with `/workspace/reg0-gate/REG0.canon` (`f5331a7229623ff9a1c99e7e8dd0fae8c21d4c14e8262b3f1b5d7b11d603f528`), which was cut from released `replay-all.jdg` `a202ed994929c8484f053219047d854729af4a3d97ad8f804bb3cdef3b4a52ae`: 0 mismatches. `build.py` does that check. The running gate does not open either file.

## REG0_ok is a theorem

Public `rocq/RpInitOk.v` at `e8958a92d72c0b4cace72949510807b8a5b1320e`, sha256 `827498d05d92fd334a093273b1bdf13ef5fa11e643b84b2fa8ac83dff07d8bf3`, declares:

```coq
Theorem REG0_ok : reg_ok hypf REG0.
Proof.
  ...
Qed.
```

There is no `Axiom`, `Hypothesis`, or `Parameter` in that file. The full statement is `SOURCE-REG0-OK.txt`. `judge/rocq/PrefixSoundness.v` at `63f45bb` proves `REG0_prefix_ok` by `exact REG0_ok`. It does not assume an extra axiom. The checker theorems keep an explicit premise, `reg = firstn n REG0` or `reg = firstn n canonical_data`, and then call the released `check_thm_ok` / `check_batch_ok`.

This sandbox did not re-run Rocq. The kernel receipts in that commit were read, not repeated.

## Correspondence, still open

These programs are not a proof that their bytes compute Gallina `check_thm` or `check_batch`. Parsing, token comparison, and executable correspondence remain separate obligations. An `ACCEPT` from the released judge is still read through those theorems and through the authenticated prefix. Finite runs do not close that gap.

## What was executed

`tests/linux-output.txt` is the run. Python and `reggate.pmp` agreed on every file.

- 3538 API checks, the same shape as `judge/test-registry-api-v4.rkt`: prefixes 0..706, a formula mutation, a hypothesis mutation and a token mutation at each of 706 entries, leading zeros on all 706, a 707th entry, `0.0`, and non-list input. 3538 passed, 0 failed. Separate checks: `02` is 2 and `00` is 0.
- All 16 preserved mutants. The three spelling files (`2` as `02`, count `00`, hypothesis `0` as `00`) were rejected by the old gate and accepted by this one. The other thirteen kept the same class. The released `judge-v3.pmp` then accepted the three spelling files.
- All 14 public `judge/registry-tests-v4b` files, by this gate and by public `judge-v4.pmp` on the released Linux interpreter. Prefixes 0, 1, 677 and 706, and the tab/leading-zero file, were `GATE` here and `ACCEPT` there. Forged registry, altered formulas, altered hypotheses and 707 entries were refused by both before an accept. The two false proofs and the missing-registry use were canonical prefixes here; `judge-v4.pmp` then refused the steps (`ax: not an axiom shape`, `use: no such registry entry`).
- Altered-canon attack. A 706-entry `REG0.canon` whose entry 0 was replaced by `a n q 0 0`, and a JDG whose registry is that entry, cited by `U`. The old `reggate.pmp`, run in that directory, printed `GATE`. This gate printed `REJECT registry` / `0` / `formula` with `REG0_CANON` set to the altered file. `judge-gated.sh` did not start the proof judge. Called directly, released `judge-v3.pmp` accepted the forged file.
- Empty prefix, false `Y` step: `GATE`, then `judge-v3.pmp` rejects `ax: not an axiom shape`.
- `pass-empty.jdg` from a directory with no canon file: `GATE`.

`judge-gated.ps1` is the Windows policy. It was not executed.

Not re-run here: the 918 runtime cases, the 150 strx cases, the Book ledger, the 132 native cases, and the 4551-theorem replay. Those claims belong to commit `63f45bb`. This run does not re-certify them.

## Files

| file | role |
|---|---|
| `embed_data.py` | embedded AUTHREF and parsed entries |
| `gate_core.py`, `gate.py` | Python gate. Opens only the JDG path |
| `reggate.pmp` | pmp gate. Same literal. No `read` of a canon |
| `reggate.pmp.tpl`, `build.py` | rebuild, after checking v4 against `REG0.canon` |
| `judge-gated.sh`, `judge-gated.ps1` | proof judge only after `GATE` |
| `test_all.py` | the run |
| `tests/linux-output.txt` | the output |
| `SOURCE-REG0-OK.txt` | the theorem, not an axiom |
| `previous/PRESERVED.txt` | the earlier archive hash |

Released tools used, not modified:

| file | sha256 |
|---|---|
| `pompetzki` Linux | `414e976b9ef34b3cf971d947bd0060347eb1bf77564333caf5944ff4067382a7` |
| `judge-v3.pmp` | `bf147194d415d0ab6991b5912c718c772f4bcb285ea027326fc5a108a81e6ce7` |
| public `judge-v4.pmp` | `c0698f6c00310e4cf95147d4ddfbfab0f8c06d00aa8f9ca1da8482123c073e33` |
