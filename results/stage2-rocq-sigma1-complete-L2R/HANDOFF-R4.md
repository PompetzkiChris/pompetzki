# L2R HANDOFF-R4 (lane L2R: Stage 2 bounded/sigma1, and LCH O8/O9)

Content assembled from `date` readings 20:18:24 to 20:28:53 EDT 2026-10-09. Folder: `C:\ClaudeOutput\pompetzki\lanes\L2R\`.

- The first write of this file, at 20:28:38, produced 0 bytes because the shell heredoc failed with "bad substitution".
  Its manager4 copy was also 0 bytes. Both were rewritten with this text.
- Toolchain: `C:\ClaudeOutput\formalization-toolchain-20260924\tools\Rocq-Platform-2026.07.0-9.1\bin` (coqc and coqchk, Rocq 9.1).
- Load path `<LP>` for every command below:
  `-R /c/ClaudeOutput/pompetzki/forcing-src/general Cohen -R /c/ClaudeOutput/pompetzki/lanes/LCH/rocq LCH -R /c/ClaudeOutput/pompetzki/lanes/L2R L2R`

## Recovery checks

- 20:18:24 and 20:22:28: ran `date` and `Get-CimInstance Win32_Process`. No coqc, coqchk or racket job of lane L2R was running.
  The coqc/rocqworker processes present belonged to other lanes:
  - Groebner/JudgeProof: JudgeAXSchemaNonallRecovery.v
  - CX1: AddatLoop9.v
  - CX3B: Round2DataW17.v, Round2DataW18.v, Round2CertificateW16.v
- 20:26:03 free memory: 10,744,956 KB physical, 22,071,048 KB virtual.
- I checked every .v, .vo, .log, .txt, .md, .rkt and .sh file in the folder for NUL bytes.
  - `L2RDef.vo` (26610 bytes, mtime 19:30:38) has only 641 non-NUL bytes. The 19:30 outage cut it.
  - coqc confirms this in compile-r4.log: "L2RDef.vo: premature end of file". The file is unchanged and in place.
  - `coqchk-3.log` is 0 bytes. It is the coqchk run started 19:27:40 that the outage interrupted. It is unchanged and in place.
  - Every other .vo has the normal NUL content of a binary and loads (compile-r4b.log).
- `L2RGoedelD0r4.v` was my first attempt. It imports the cut L2RDef.vo and failed: exit 1, receipt compile-r4.log, 20:25:24 to 20:25:37. It is in place.
- New files written in recovery 4:
  - `L2RDefR4.v`: identical to L2RDef.v except line 1, the header comment.
  - `L2RGoedelD0R4b.v`
  - `PrintAx5r4.v`
  - `PrintAx4r4.v`: not compiled, because it imports the failed module.
  - `compile-r4.log`, `compile-r4b.log`, `coqchk-r4.cmd.txt`, `coqchk-r4.start.txt`, `coqchk-r4.log`, `coqchk-r4.end.txt`, `hashes-r4.txt`

## Round 1: bounded and Sigma1 completeness over Gam (verified before the outage)

| theorem | file | statement |
|---|---|---|
| bounded_complete | L2RSent.v:419 | bounded A -> wf 0 A -> (sat [] A -> prov Gam (tr A sid)) and (not sat [] A -> prov Gam (Neg (tr A sid))) |
| sigma1_complete | L2RSigma1.v:120 | pos A -> wf 0 A -> sat [] A -> prov Gam (tr A sid) |
| sigma1_bounded_statements | L2RAgree.v | the 78 sentence theorems of sigma1.rkt: each is proved, or its negation is proved, in Gam |
| sigma1_all_statements | L2RSigma1.v | the same 78 theorems, including the unbounded Sigma1 cases |

Receipts:
- `build-run-1.log`: `bash build-L2R.sh`, a clean rebuild from 18:28:56 to 18:39:11.
  - coqc of all 8 modules: exit 0.
  - `coqchk <LP> L2R.L2RSigma1 L2R.L2RAgreeMut`: 575 s, Axioms: <none>, exit 0.
- `coqchk-all.log`: 18:18:37 to 18:28:36, Axioms: <none>, exit 0.
- `PrintAxAll.out.txt`: all four theorems are "Closed under the global context".

## Round 2: O8 = GoedelCH.LSEP Mf and O9 = GoedelCH.LCOLL Mf, as VLred.goedel_final_red consumes them

All of these are "Closed under the global context": PrintAx5r4.v in compile-r4b.log, coqc exit 0, 20:27:01 to 20:27:09. The exceptions are lsep_from_levels and lcoll_from_levels, whose receipts are PrintAx2.out.txt and coqchk-2.log.

| theorem | file | premises -> conclusion |
|---|---|---|
| lsep_from_levels | L2RSepL.v | STR, REFLsep, DEFsep -> LSEP M |
| lcoll_from_levels | L2RSepL.v | STR, SSUB, SIN, REFLcoll -> LCOLL M |
| lsep_from_grefl | L2RRefl.v:119 | STR, SCOV, GREFL, DEFsep -> LSEP M |
| lcoll_from_grefl | L2RRefl.v:126 | STR, SSUB, SIN, SCOV, GREFL -> LCOLL M |
| relU_d0 | L2RDefR4.v:15 | syms g = [] -> d0 (relU w g) |
| defsep_from_dsep0 | L2RDefR4.v:56 | SIN, SSUB, (DSEP0 for every d0 psi) -> DEFsep g n for every pure g |
| lsep_from_grefl_dsep0 | L2RDefR4.v:86 | STR, SSUB, SIN, SCOV, GREFL, DSEP0 -> LSEP M |
| goedel_final_red_levels | L2RGoedel.v:11 | VLred.goedel_final_red with LSEP, LCOLL replaced by STR, SSUB, SIN, SCOV, GREFL, DEFsep |
| goedel_final_red_d0 | L2RGoedelD0R4b.v:11 | the same, with DEFsep replaced by DSEP0 |

M and Lev are arbitrary pure formulas with closedk 1. The hypotheses mean:
- STR Lev: every level is transitive.
- SSUB M Lev: every level is a subset of M.
- SIN M Lev: every level is an element of M.
- SCOV M Lev (L2RRefl.v:44): every element of M lies in a level.
- GREFL M Lev (L2RRefl.v:40): reflection for every finite list of pure formulas, uniformly in the parameters in M.
- DSEP0 M psi n (L2RDefR4.v:34): M is closed under Delta_0 separation.

Receipts:
- `coqchk-2.log`: `coqchk <LP> L2R.L2RSepL`, 19:23:44 to 19:27:50, real 4m4.609s, Axioms: <none>, exit 0.
- `compile-r4b.log`:
  - `coqc <LP> /c/ClaudeOutput/pompetzki/lanes/L2R/L2RDefR4.v`: exit 0, started 20:26:44.
  - `coqc <LP> .../L2RGoedelD0R4b.v`: exit 0, started 20:26:52.
  - `coqc <LP> .../PrintAx5r4.v`: exit 0, 20:27:01 to 20:27:09, seven times "Closed under the global context".
- `coqchk-r4.log`: `coqchk <LP> L2R.L2RGoedel L2R.L2RGoedelD0R4b`, started 20:27:21. It covers L2RDefR4, L2RRefl, L2RSepL, L2RLogicA, LCH and Cohen.
  It was still running when this file was written. Its exit code and Axioms line will be in HANDOFF-R4-FINAL.md.

Line counts:

| file | lines | Lemma/Theorem |
|---|---:|---:|
| L2RLogicA.v | 168 | 42 |
| L2RSepL.v | 324 | 28 |
| L2RRefl.v | 132 | 7 |
| L2RDefR4.v | 92 | 5 |
| L2RGoedel.v | 25 | 1 |
| L2RGoedelD0R4b.v | 25 | 1 |

## SHA-256 (sha256sum, 20:28:53; the same list is in hashes-r4.txt)

```
2c76f360ebe79bad00d986ea8e35818d49bde21bdc15051abae38903acb3ea70  L2RAgree.v
7f3bae575eb353793872a867cd6da1f475033a905ee53fc0874bb13205a6a756  L2RAgreeMut.v
58b823af2a411bd2ff5f5f0c5ebfe58690f016789e6d6c370d7306e65cbafe94  L2RArith.v
cedae7461ae0c5d680d3e8de4258015676c343fc56caf2a531f064f376787f87  L2RCases.v
4f73e69bd44e23c5232603b1572f51365bdaa76ad54599a58335c740d8852df8  L2RDef.v
06c6a902911a04d454f76495236982850bfc54797741c6189d6f5d29363802a4  L2RDefR4.v
08ed2af474d547226e3a9e217462c986f87f3d4d378f7de36e1fa6887e276c40  L2RFin.v
e96f74bc1e155cd78a66296e1a58157a91361ee91a3b7223e5636e8e466d0eac  L2RGoedel.v
a6c5b1857b19863bfbec0e3fb824e007c23e1d919c6b31201b872578f4bb911f  L2RGoedelD0R4b.v
b6f092a9a16e9f793aba9883c17aeee7ebb3678e3cfc42d6be40d2e5b716f262  L2RGoedelD0r4.v
05cd24c699624645a7df33483805d879cac934520346dcb1ef6d012ed7eb5466  L2RLogic.v
f84836916d62d821b28d80a1233b37760617932bc708eecae773e805197a688e  L2RLogicA.v
0912d4d7e3e8a29b85498ae2a0b1c0bde991583abbdbea55a77907a58342dacb  L2RRefl.v
4efa90a3fbb4dd1f4b9018c5d6a249acd04e57a373696058a8a74baad56ba11a  L2RSent.v
f218987e6344c48d0b8d1db03e5c87d5559e773deafdab8e463847e9d9e35a80  L2RSepL.v
40b3d2e6dc7d65dde6daca6ec089e10a86f628335129f0631d446210725b8afd  L2RSigma1.v
01ed0ee85df351d6fc2132cff2857ad8bb868dd633eacd7014e762b9a7f57203  agree.rkt
1556566d5e263d0748c00e2102aa6996d49c237278e0ab79ddf91d7ba71d6de6  build-L2R.sh
bd41f8848d1216b8f010bf69a2c3f360973d4e836230cc4318c1d6fcd2799d19  PrintAx2.v
1d883908ed229f601807e8f044dab00b8ffda5d2c1e8f445aa73f656e110a0ea  PrintAx3.v
6e7ac8d73d38ac4e3596d13ab479213443f14de69b7d88f4d220d73b7d4a2d4d  PrintAx4r4.v
a3b1768376ab2c2161c88bcd8a7cbd56bbabcfa225507faceed1b771afa93c7f  PrintAx5r4.v
a97580e2e400921ade55fd231612e68f869133d584083df9143a3a7b9c49295b  PrintAxAll.v
bcbfc91bc84623049047080457ddb53c93801d47efe3564985a6f0ad30c7e7fa  PrintAxL2R.v
b08231dab86bfb477be5357ed8944d53428bad5fccc030c619360eb9ae18dfd3  L2RAgree.vo
cd4ee1af17071e56622e9a8a5b7e62a9d0d6e78ce8fcdc7becfdea176034501e  L2RAgreeMut.vo
67d819723456a40aafbb951582acd1dd006164d7371ca585a630b1554c0430b2  L2RArith.vo
0f5116648a162ce8f933dbc5436f759526b5d41abd924bb7d279ff9a0327feaa  L2RCases.vo
1f52954edcb4a50ad894e5d3d0c76123967e37f556367e942c0454f972d7796a  L2RDef.vo   (cut by the outage, not used)
d5a1ad8d4f3559b2547502e2f84e84aae185202e040af390c487c4971272e52c  L2RDefR4.vo
bcd0d511e4f1fb0b915827b033aa58799dc65cb2a25a4d17ca11d40d4d0d6b56  L2RFin.vo
6dc2498aaa32b09e28c09dc6769fff5d49d9e0df110fbf17115f54c613fb3459  L2RGoedel.vo
ac6cb09e48e7ba710fd99e675f05ed6a5a7adbbb92c8bc3e5157330e6e944ce3  L2RGoedelD0R4b.vo
f341e7c2bfb72da90902311479c90d160a6d4cd054fcf2040b22c20a9ad7f84e  L2RLogic.vo
67348cb69ff8009eddc56a4f5f6a7450ed383607ead10d90de8d10d197ac1b95  L2RLogicA.vo
9f17aa3ca079fe805c2cb297785ab18584d0cd201bdbeaf7bc3ecf991347d339  L2RRefl.vo
d90a5135550516dfe8c3234091f071878f409d2b1b2674654f6eeea4cae44105  L2RSent.vo
6ea510dfcb86d9e034b03b70183d6fced2185c2b1dadf2fb55c5802961d915ff  L2RSepL.vo
7132dfb56d6104fe58c6780e13e7bd86bd0b6194e6e58bfaac27a06a977edd24  L2RSigma1.vo
7206011c9da4eab0c08c30cea751a2a21a53d1f99077ea231d31f222b02968f2  PrintAx2.vo
d3bd586fd5bede06f882c483f3c7b63c18d3fd21976e0f7ba6e6a83f300c59d7  PrintAx3.vo
be399e57bc007885a73050e419d8aa6e88fd3f48f8e0c61ba1b1ad3b3939bf41  PrintAx5r4.vo
b3ff05e952a32784218addd476dead6cc429f4e28db79c0e017c0a25f64d3e18  PrintAxAll.vo
b32bbd9939978ce0affa5ca4acf52a9b711dce51d79a30c9afd305c54e5cf0f9  PrintAxL2R.vo
ebbb091f0def6a0cff91008442ae08422c7118990a50a5ce05cfa1ae107e33e6  PrintAx2.out.txt
eb6007450a9c9072e5f1c14b6359086511627b991ae6074cfa1bc9fbb132b59f  PrintAx3.out.txt
dae9fa35726bf3855db32546e41664d1196ebc70e1e9133800a12e9a62aa9175  PrintAxAll.out.txt
7ae49c5844b6b546d03c550d7736c34c860e66eb3131269958467d713fd24ea4  RESULTS.md
c6ea535ada30ff70f63a32f7b88847a9d1e31be58299dbc859f17233e298dd6c  STATUS.txt
4009a041aabc5d248dbd7fc8b8c03e2a3004d2d9c9f85f02fa5aa212d5f6d869  build-run-1.log
79c100e8987a236696fef1d170a4232a2cf8df77f19041d3b88df3343dd418ab  coqchk.log
62ad80bfe5803f2e3b220792adc305e7d9726d871d8e81ea233e3e890e14f172  coqchk-all.log
90615b2182114fe2afcb14808389afc73b737cb56b6a802d16d640361aa9e53d  coqchk-2.log
e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855  coqchk-3.log   (0 bytes, interrupted)
0c460945a13781e1ceddd5fcf3d8f48581bb516c7d92e880c5f72c1b2498d769  compile-r4.log
187a5795c12d483c4049e4a7784aa8cf09561606c28751d79926d21a7f12a87b  compile-r4b.log
fb30269ab6756eb4b4a7110c3f24d2e1c8876973aa77f9d81d14cc28ff4fb34a  coqchk-r4.cmd.txt
764f7635ed5ef70e46178bcacc87e51a3789678f1cd2e2b3cf016c7ffa8a4cf5  coqchk-r4.start.txt
```

## Open items, by exact name

1. **The general correspondence between the sigma1.rkt emitter and check_batch.** No Rocq statement says either of these:
   - for every input sentence, the text that sigma1.rkt emits equals `tr A sid`;
   - the emitted .jdg batch is accepted by `check_batch`.

   This is checked only on the 78 emitted sentences: `L2RAgree.all_agree`, and `L2RAgreeMut`, which rejects 156 of 156 mutants. Agreement on the 78 sentences does not prove the general statement.
2. **GREFL Mf Lev** (L2RRefl.v:40), the reflection schema for the levels of L. Open. It needs O0 (Mf and Lev as defined formulas) and recursion along omega of definable class functions.
3. **DSEP0 Mf psi n** (L2RDefR4.v:34) for every d0 psi: Delta_0 separation closure of L. Open; needs O0.
4. **STR Lev, SSUB Mf Lev, SIN Mf Lev, SCOV Mf Lev**: four single statements, open. Each becomes a judge obligation once O0 fixes Mf and Lev.
5. **LCH O0 to O7, O10, O11** (lanes/LCH/RESULTS.md, lines 64 to 72 and 139 to 150). These are not assigned to L2R. goedel_final_red_d0 keeps them as premises:
   - LEX = O1
   - HT i = O2 to O6
   - rel Mf (axf 6) = O7
   - rel Mf VL = O10
   - ZFE VL |- pi ch = O11
6. **O8 = LSEP Mf and O9 = LCOLL Mf** are reduced, not discharged. LSEP needs items 2, 3 and 4; LCOLL needs items 2 and 4.

Not used:
- CX3's Conservativity2 and Stage2Conservativity2. L2R's theorems are stated over Gam and ZFpure directly, so they were not rerun.
- The GPU, and downloads.

No existing file was edited, moved or deleted. The only overwrite was this file's own 0-byte first write from 20:28:38.
