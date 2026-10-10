# L2R HANDOFF-R4-FINAL

Written from `date` readings up to 20:34:13 EDT 2026-10-09. Folder: `C:\ClaudeOutput\pompetzki\lanes\L2R\`.

This file completes HANDOFF-R4.md (sha256 152c0148b61ac868d44721279cfdd8ef33b1a1c21319fb6f96ba29fbb7c7339d). HANDOFF-R4.md has the recovery checks, the round-1 results and the full hash list as of 20:28:53. Nothing below changes those.

## Receipts completed after HANDOFF-R4.md

`<LP>` = `-R /c/ClaudeOutput/pompetzki/forcing-src/general Cohen -R /c/ClaudeOutput/pompetzki/lanes/LCH/rocq LCH -R /c/ClaudeOutput/pompetzki/lanes/L2R L2R`, with the toolchain at
`C:\ClaudeOutput\formalization-toolchain-20260924\tools\Rocq-Platform-2026.07.0-9.1\bin`.

| command | start | end | result | log |
|---|---|---|---|---|
| `coqchk <LP> L2R.L2RGoedel L2R.L2RGoedelD0R4b` | 20:27:21 | 20:30:45 | "Modules were successfully checked", real 3m23.838s, exit 0; no -o, so no axiom summary | coqchk-r4.log |
| `coqchk -o <LP> L2R.L2RGoedel L2R.L2RGoedelD0R4b` | 20:30:56 | 20:33:36 | "Modules were successfully checked", Axioms: <none>, type-in-type <none>, unsafe fixpoints <none>, assumed positivity <none>, real 2m39.576s, exit 0 | coqchk-r4b.log |

coqchk-r4b covers both checked modules and everything they load:
- L2R: L2RDefR4, L2RRefl, L2RSepL, L2RLogicA
- LCH: Rel2, GoedelCH, LAXred2, VLred, Abs2
- Cohen: the libraries listed in each file's imports

## Accepted theorems (round 2), all with Axioms: <none>

- `L2RGoedelD0R4b.goedel_final_red_d0`: VLred.goedel_final_red with LSEP Mf (O8) and LCOLL Mf (O9) replaced by STR Lev, SSUB Mf Lev, SIN Mf Lev, SCOV Mf Lev, GREFL Mf Lev and DSEP0 Mf psi n for every d0 psi.
- `L2RGoedel.goedel_final_red_levels`: the same, with DEFsep in place of DSEP0.
- `L2RDefR4.lsep_from_grefl_dsep0`, `L2RDefR4.defsep_from_dsep0`, `L2RDefR4.relU_d0`.
- `L2RRefl.lsep_from_grefl`, `L2RRefl.lcoll_from_grefl`.
- `L2RSepL.lsep_from_levels`, `L2RSepL.lcoll_from_levels`.

Round 1 is unchanged from HANDOFF-R4.md: `bounded_complete`, `sigma1_complete`, `sigma1_bounded_statements`, `sigma1_all_statements`. Their receipts are build-run-1.log and coqchk-all.log, both Axioms: <none>, exit 0.

## New files after HANDOFF-R4.md, SHA-256

```
b14a883c5b163412b5a03d560002dbbdc4075741373cc78eed85aff889bbad80  RESULTS-2.md
c2f4480f2972b7abd773b4e19ab01db45c4c9d87293813055f3766f958e8ab31  STATUS-2.txt
a220dffccbed3b925af8cf53e11eb254c8c08fd4f23fd7c5462fe554d5d88541  hashes-r4.txt
745e83369311c7878d0a8bcd7260a5a86816de38d5e11e572a819ed31a49c7e3  coqchk-r4.log
a7cabfaf210d713d84afd5c42f754a034e097b232c3a6a01c43ba44fbf615f9a  coqchk-r4.end.txt
3af326fba60d217802525470602c783321b882a529be4dc78a776b81aa01759d  coqchk-r4b.log
84aeea9c9b7ec80b79d30c879cf2f1dd9a44c38fbe4aa84c293431bc66b4dce5  coqchk-r4b.cmd.txt
543618af6a0f79b4ebf4784cdbeea8e6ce02c6822475d34ec81f382a67796419  coqchk-r4b.start.txt
6395370c5568e020940c487d7a77765f4d0d739c890d67dda01b2cfdd70ff514  coqchk-r4b.end.txt
```

Checked sources and binaries, the same hashes as in HANDOFF-R4.md and unchanged since:

```
06c6a902911a04d454f76495236982850bfc54797741c6189d6f5d29363802a4  L2RDefR4.v
d5a1ad8d4f3559b2547502e2f84e84aae185202e040af390c487c4971272e52c  L2RDefR4.vo
a6c5b1857b19863bfbec0e3fb824e007c23e1d919c6b31201b872578f4bb911f  L2RGoedelD0R4b.v
ac6cb09e48e7ba710fd99e675f05ed6a5a7adbbb92c8bc3e5157330e6e944ce3  L2RGoedelD0R4b.vo
e96f74bc1e155cd78a66296e1a58157a91361ee91a3b7223e5636e8e466d0eac  L2RGoedel.v
6dc2498aaa32b09e28c09dc6769fff5d49d9e0df110fbf17115f54c613fb3459  L2RGoedel.vo
9f17aa3ca079fe805c2cb297785ab18584d0cd201bdbeaf7bc3ecf991347d339  L2RRefl.vo
6ea510dfcb86d9e034b03b70183d6fced2185c2b1dadf2fb55c5802961d915ff  L2RSepL.vo
67348cb69ff8009eddc56a4f5f6a7450ed383607ead10d90de8d10d197ac1b95  L2RLogicA.vo
a3b1768376ab2c2161c88bcd8a7cbd56bbabcfa225507faceed1b771afa93c7f  PrintAx5r4.v
be399e57bc007885a73050e419d8aa6e88fd3f48f8e0c61ba1b1ad3b3939bf41  PrintAx5r4.vo
187a5795c12d483c4049e4a7784aa8cf09561606c28751d79926d21a7f12a87b  compile-r4b.log
```

## Preserved, not used

- `L2RDef.vo` (1f52954e…): cut by the outage.
- `coqchk-3.log`: 0 bytes, interrupted 19:27:40.
- `L2RGoedelD0r4.v` and `compile-r4.log`: the failed first attempt, exit 1.
- `PrintAx4r4.v`: not compiled.

## Open items, by exact name

1. **The general correspondence between the sigma1.rkt emitter and check_batch.** There is no Rocq theorem that for every sentence the emitted text equals `tr A sid` and that the emitted batch passes `check_batch`. Only the 78 emitted cases are checked: `L2RAgree.all_agree`, plus `L2RAgreeMut` (156 of 156 mutants rejected).
2. **GREFL Mf Lev** (L2RRefl.v:40). Open; needs O0.
3. **DSEP0 Mf psi n** (L2RDefR4.v:34) for every d0 psi. Open; needs O0.
4. **STR Lev, SSUB Mf Lev, SIN Mf Lev, SCOV Mf Lev**. Open single statements; they need O0.
5. **LCH O0 to O7, O10, O11.** These belong to lane LCH and are premises of goedel_final_red_d0.
6. **O8 LSEP Mf and O9 LCOLL Mf.** Reduced to items 2 to 4, not discharged.

No GPU, no download, no sub-session or helper agent. No existing file was edited, moved or deleted. The one overwrite was HANDOFF-R4.md's own 0-byte first write at 20:28:38, recorded in that file.
