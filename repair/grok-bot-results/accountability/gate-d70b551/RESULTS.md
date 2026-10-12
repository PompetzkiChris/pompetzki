# grok/embedded-reg0-gate at d70b551c6559a2c1cde0bc46f1b7e310a26bfe92 (Grok Bot accountability)
ls-remote confirms the head. Merge-base with codex/exact-release-repair: 52e4a28. 83 changed paths, each with sha256, in raw/files-vs-merge-base.txt. This commit **contains implementation bytes**: v5/reggate.pmp cbac6ec3…, gate.py 84e6d7bd…, gate_core.py e7e11cd2…, judge-gated.sh a9bdf541…. Gate claims tested here **COUNT**. Earlier archive-only claims (the zip receipts) remain **NOT COUNTED**.
Run: `POMPETZKI=<interp> JUDGE_V3=judge/judge-v3.pmp GATE_PROOF_LOG=log sh judge-gated.sh FILE`, plus `python3 gate.py FILE`. Interpreters: released v1.2.0 pompetzki 414e976b… (the one the gate README names) and runtime-v2 3658455c…. Both give the same verdicts.

| Claim | Command | Actual output | Verified outcome |
|---|---|---|---|
| False registry (forall x, not x=x) refused before the proof judge | judge-gated.sh false-registry.jdg | `REJECT registry 0 formula`, exit 1, proof log empty; Python gate same | **PASS** |
| Canonical REG0 gated then accepted | canonical-reg0.jdg | `GATE 706 706` then judge `ACCEPT`, exit 0 | **PASS** |
| Leading zeros (3 extra) do not change values | padded3-reg0.jdg | `GATE 706 706` + ACCEPT, exit 0 | **PASS** |
| 13+ digit padded tokens (13 zeros on every number, R count too) | padded13-reg0.jdg | gate `GATE 706 706` (pmp and Python agree), then judge-v3 `REJECT a number has more than 12 digits`, exit 1 | **Gate claim PASS. End-to-end verdict REJECT**: the downstream judge-v3 12-digit cap still refuses what the gate accepts. This is a safe-direction refusal, but the pipeline is inconsistent. |
| REG0 prefix (10 and 705 entries) | prefix10/prefix705 | `GATE 10 706` / `GATE 705 706` + ACCEPT, exit 0 | **Prefix accepted by design** (canonical prefix rule); recorded as observed |

Finite tests do NOT establish executable/Gallina correspondence, parser denotation, or compiler preservation.
