# Lane L6 handoff R4 (Stage 6, Lean/Mathlib into ZF), written 20:26 (`date`)

Session dbf01e6c-006d-4c90-94fb-778738656246. Lane folder `C:\ClaudeOutput\pompetzki\lanes\L6`.
A judge run on the round-2 files was in progress at 20:26. Its verdicts are in HANDOFF-R4-FINAL.md.

## 1. Recovery facts

- `date` at the start of recovery: 20:18:10.
- No process of this lane was alive.
- `abschluss-verify\lean.lock` held my entry `owner-L6-192606`, left by the interrupted Lean run below. I released it at 20:19:51 with `lean-gate-v2.ps1 release L6`.
- Interrupted at 19:30 and left in place, not used:
  - `lean\L6Export3.lean` run (instances of generic queue lemmas at ℤ/ℕ): `lean\export3-run.log` is 0 bytes, there is no end file, and no `lean\export-inst.sexp` was written.
  - `r2\out\files\L6-int-4.rows.txt`: 5,025 NUL bytes. `L6-int-4.index.txt` (intact) records the same theorems.
  - `r2\out\files\manifest.txt`: ends in NUL bytes. Its readable lines match the hashes below.
- Checked after the outage: the 5 round-2 JDG1 files and their 28 mutants contain no NUL bytes, and the 5 files' SHA-256 equal the values the emitter printed before 19:30.

## 2. Round 1 (unchanged, verified before the outage)

- `out\L6-nat.jdg`
  - sha256 `a9894a405c97705d8016f63082d22a5604c89e379f51dd84ee2c00e414b1f1ac`, 14,399,840 bytes;
  - 345 theorems, 37,714 steps, final registry 1022.
- Receipt `out\judge-run.txt` (18:20:59–18:35:54):
  - pmp `judge-v3.pmp`: ACCEPT, exit 0, 850,090 ms;
  - `racket\judge.rkt`: ACCEPT, exit 0, 3,317 ms;
  - all 10 mutants in `out\mut\`: REJECT, exit 1, from both judges.
- 252 statements of the `import Mathlib` environment, each under its Lean name (`out\STATEMENTS.md`):
  - 9 declared in Mathlib modules;
  - 243 declared in Lean core `Init.*`.
- Sources: `out\sources-sha256.txt`. zfcore.rkt `34423126…eb343f`, zfbatch.rkt `fb3f5fc5…18fc1`, zfnat.rkt `eccb5d61…3e6`, scripts.rkt `20f2af1e…2471a` are unchanged at 20:26.
- Derivations in round 1 come from my hints. Only the statements come from Lean.

## 3. Round 2 outputs (built 19:25–19:30, before the outage)

Directory `r2\out\files\`, all new files.

| file | sha256 | bytes | theorems | final registry | content |
|---|---|---:|---:|---:|---|
| L6-pt.jdg | ac411929df10d79528ea3542c48558f8fb5541d587efa3c152359a510e517dcd | 9,035,776 | 286 | 963 | 93 derivations that follow Lean proof terms (keys `PT:<Lean name>`), plus the round-1 derivations of the lemmas those terms cite |
| L6-int-1.jdg | a65622f51d7e92870d3962675a21e857af1a6be6f020bab5add8bc604dfd6b1b | 11,968,000 | 254 | 931 | 115 ℤ statements of the Lean core library, plus the ℕ lemmas they use |
| L6-int-2.jdg | 971c76497220f705afa1163e508c5fcadfe7e646f914adcb08d23296b95696b5 | 11,792,775 | 161 | 838 | 38 ℤ statements |
| L6-int-3.jdg | ee8cd8a55fbf719a63f24ec16c3135315fc583c68bd81de0fac20dc0c9cca5f6 | 13,679,521 | 157 | 834 | 24 ℤ statements |
| L6-int-4.jdg | cc971243ad4cf7409d52b10e80cc704619397ca5590c87c210e94287b96322b7 | 13,282,605 | 139 | 816 | 13 ℤ statements |

- The generator's copy of the checker printed ACCEPT for all 5 files before 19:30.
- Every final registry is at most 1,091 (the pmp memory-block bound).
- All numerals are ≤ 2, far below the depth bound of 38.

### ℤ (item 1 of round 2)

- Encoding: ℤ = (ℕ×ℕ)/≈ with (a,b) ≈ (c,d) ⇔ a+d = b+c.
  - A ℤ variable x becomes two ℕ variables xp, xn.
  - The rules for + − · unary − = ≤ < numerals and ↑ are in `r2\leanstmt2.rkt` (header comment).
  - ≈ is a congruence for these operations, so a first-order ℤ statement holds in ℤ exactly when its translation holds over the pairs.
- This equivalence is a meta-level fact. It is not derived in ZF in these files: the files prove the translated ℕ statements.
- 210 distinct ℤ statements of the Mathlib environment derived across L6-int-1..4. Their names are in `r2\out\new-env-names-r2-r4.txt`:
  - 190 named `Int.*`;
  - 16 named `Lean.Omega.Int.*`;
  - 2 named `Lean.Grind.natCast_*`;
  - 4 named `Mathlib.Tactic.Zify.natCast_*`.
- Modules (index column 4) include Init.Data.Int.Order, Init.Data.Int.Lemmas, Init.Omega.Int, and Mathlib.Data.Int.Order.Basic (4 statements).
- Method: automatic ring normalization and cancellation (`r2\ring.rkt`). Each rewrite is an instance of a schematic relational lemma `(Rel NAME)` (`r2\rel.rkt`), derived in the same file from the ℕ theorem NAME.
- Export: 1,207 ℤ-slice theorems (`lean\export-int.sexp`), of which 448 translate.
- Automatic attempts: `r2\out\attempts\all.tsv`, 532 candidates (ℤ and leftover ℕ), 248 ok, 284 fail.
- Of the successes, 222 were under 1.5 MB each, packed smallest first into 6 groups. Only groups 1–4 were emitted, because of judge time.

### AG2 queue (item 2)

- `r2\out\queue-classification-r4.tsv`: all 7,658 declarations in queue order, with the Lean module, kind, category and the exact blocking construct.
- 7,471 names were found in the environment. The export is `lean\export-queue.sexp`, from `lean\L6Export2.lean`, run 18:50:21–18:52:08 under the lean lock.

| category | count |
|---|---:|
| translated + derived | 6 |
| translated, no derivation yet | 6 |
| not translatable | 7,646 |

The 6 translated + derived:

| declaration | file |
|---|---|
| Int.neg_eq_neg | L6-int-1 |
| Int.succ_natCast_pos | L6-int-1 |
| Nat.succ_pos' | L6-nat |
| Nat.two_lt_of_ne | L6-nat |
| Nat.two_le_iff | L6-nat |
| Nat.le_succ_iff_eq_or_le | L6-nat |

The 6 translated, no derivation yet:
- Int.eq_zero_or_eq_zero_of_mul_eq_zero
- Int.nonneg_or_nonpos_of_mul_nonneg
- Int.mul_nonneg_of_nonneg_or_nonpos
- Int.mul_nonneg_iff
- Nat.two_mul_ne_two_mul_add_one
- Nat.not_exists_sq

Blocking constructs of the 7,646, largest groups:

| construct | count |
|---|---:|
| a binder over a Sort (a generic type variable α with type-class instances) | 5,244 |
| a binder over a function type | 231 |
| name not found in the environment of import Mathlib (AG2 name resolution) | 187 |
| a binder over type Nat.Prime | 135 |
| a binder over type Dvd.dvd | 76 |
| constant HPow.hPow | 68 |
| constant Nat.choose | 50 |
| a binder over type PartENat | 48 |
| a binder over type ENNReal | 47 |
| the proposition former Dvd.dvd | 47 |
| the proposition former Int.ModEq | 46 |
| a binder over type Nat.ModEq | 43 |

The full per-declaration list is in the TSV.

### Proof terms (item 3)

- Export: `lean\export-proofs.sexp`, the proof terms (Lean `ConstantInfo.value`) of the 252 round-1 statements.
- Class 1, implemented in `r2\proofterm.rkt`: λ over the statement's variables and hypotheses, then applications of earlier lemmas. Supported constructors:
  - the arguments are ℕ terms, hypotheses, or nested lemma applications;
  - wrappers `Eq.symm Iff.symm Ne.symm id absurd Iff.intro And.intro Or.inl Or.inr Iff.mp Iff.mpr Eq.mp Eq.mpr Not.elim False.elim Eq.trans Iff.trans`;
  - η-expansion of a bare constant.
- The derivation instantiates exactly the lemmas the term cites, at the term's arguments, plus the kernel's definitional steps as ZF theorems:
  - ι of Nat.add / Nat.mul: `Nat.add_zero`, `Nat.add_succ`, `Nat.mul_zero`, `Nat.mul_succ`;
  - δ of Nat.lt: `Nat.succ_le`.
- 93 of the 252 proof terms are in class 1, and all 93 derive in L6-pt.jdg. Per-name class and reason: `r2\out\files\proofterm-class.tsv`.
- Outside class 1, by reason:

| reason | count |
|---|---:|
| a cited constant has no statement in the batch (mostly generic lemmas) | 68 |
| private `match`/`brecOn` structural recursion (`_private.…`) | 29 |
| congrArg | 20 |
| a cited lemma whose ∀ comes after a hypothesis | 9 |
| of_eq_true | 7 |
| rfl | 7 |
| more ℕ binders than the statement has | 5 |
| flip | 4 |
| let | 2 |
| other single cases | 7 |

## 4. Commands

```
cd C:\ClaudeOutput\pompetzki\lanes\L6\r2
racket classify.rkt OUT.tsv                 (queue classification; draft written 18:55: out\queue-classification-draft.tsv)
racket attempt.rkt K 4 OUT.tsv              (K = 0..3; automatic attempts, 19:13–19:16, out\attempts\)
racket emit2.rkt out\files                  (19:25:?? start file out\files-emit.start.txt, end 19:30)
racket ..\tools\judge-par.rkt out\files out\judge-r4.txt   (started 20:19:5x, console out\judge-r4.console.txt)
```

## 5. Sources (sha256)

| file | sha256 |
|---|---|
| r2/leanstmt2.rkt | b4cd0cf98d75af2721e142d7eb79ed4a856f911a994c3247fe20a63b6fa4f749 |
| r2/engine2.rkt | e7a4033a6cd1d3adc1eb701771e31ea3cf3679a64b7eedcf43da717e4a4ded76 |
| r2/ring.rkt | f3bd285eabd1c16aaab3ef803406ed759c5be830865ebaacc27f831c82cd33c6 |
| r2/rel.rkt | ef8f29d55ad518a7e994884110d8c223954fff42d5396d792f29420e65558fe8 |
| r2/proofterm.rkt | 310bd90513ee3c347efd52169ec7dc7ec18a9e587912af13cf05863531ceda21 |
| r2/lean2zf2.rkt | 6c225af3d304cf81adf1de004f436535b67af1bbd887430459665063436e199e |
| r2/emit2.rkt | 01cbe29b2bdcd370ec1e91b1ddbdd150e4b06843e208f65b14ef3fca6498d765 |
| r2/classify.rkt | 7bca0a7208a35a204a40809b788fb5611ce29fc8cd65bb51eec00cf831174925 |
| r2/attempt.rkt | c033af3746fe09141c60c9fa610dff68d5cd0d8c22a099569c0fb2aec45a167c |
| lean/L6Export2.lean | 53e835379922df2eedd0fe35dacb3bcda87c97f2c88c420e2996dc68b5c3b75d |
| lean/export-queue.sexp | 8ba9c293db3f7fdf438c183095e300e49f555ad4e8e6506ab662ea018ef3b6a3 |
| lean/export-int.sexp | ae8be7e3d1a776507a3a81fa10dc2982fcdc56b11432d20ab6dc88c681909470 |
| lean/export-proofs.sexp | e2656418f1219e327a4617c64165db34963f23c15d689ec047f3818849ecdebb |
| zfcore.rkt / zfbatch.rkt / zfnat.rkt / scripts.rkt | as in out\sources-sha256.txt (unchanged) |

## 6. Open (not done)

- **ZF derivation of the ℤ encoding's soundness.** The quotient (ℕ×ℕ)/≈ as a ZF set, and the theorem that a translated statement over pairs is equivalent to the statement over the quotient set, are not derived. The ℤ files prove the translated ℕ statements.
- **ℤ statements derived but not emitted.**
  - 26 ring-file candidates over 1.5 MB each, among them `Int.mul_assoc`, `Int.mul_add` and `Int.add_mul`.
  - Groups 5 and 6 of the packing: 13 statements, listed by emit2's grouping of `r2\out\attempts\all.tsv`.
- **Queue items translated, not derived:** Int.eq_zero_or_eq_zero_of_mul_eq_zero, Int.nonneg_or_nonpos_of_mul_nonneg, Int.mul_nonneg_of_nonneg_or_nonpos, Int.mul_nonneg_iff, Nat.two_mul_ne_two_mul_add_one, Nat.not_exists_sq.
- **Queue items blocked by generic type variables (5,244).** Instantiating them at ℤ/ℕ (`lean\L6Export3.lean`) did not run to completion: it was interrupted at 19:30 and not rerun.
- **Proof terms outside class 1:** 159 of the 252 (reasons above), including every proof by structural recursion (`Nat.brecOn` with private match functions), e.g. `Nat.zero_add`, `Nat.add_comm`, `Nat.add_assoc`.
- **Translation-table items not derived:** the minimality half of `Nat.le` (least relation closed under refl and step).
- **Judge verdicts on the round-2 files and mutants:** pending at 20:26, see HANDOFF-R4-FINAL.md.
