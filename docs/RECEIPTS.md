# Checker receipts (append only). A receipt binds a run file and its output to the SHA-256 of the sources checked;
# an accepted prefix recorded here is reused by registering its statements (mkf.pl done batches), not by replaying it.

## R1 2026-09-25 tvo1 (V^B translations of fo1, proto2 --multi)
- run file forcing-src/t.pmp (mkf.pl "fa1 .. fh3" "tvo1"): sha256 c9d99be66dafab1857293d9f0cf75ee8f83b4a6fd5383fca089232200b870946
- source tvo1.src: sha256 89ec0aa39600d7ae97d75434ec1c7e175e00c08dc855a62c0e4ff545a59b7c14 (2236 theorems)
- output tvo1.out: sha256 f8373ad2c472f27a9c99a8743c4895c1a4567cccfc228f528fcba0e3883d5f85
- verdict: 843 theorems accepted in order (the first 843 of tvo1.src, through Yfe806; TIndEmp among them), 0 refused;
  the run stopped in theorem 844 (TIndSuc): "Menschenwerk: the arena is full" (ARENA = 1 GiB in pompetzki.asm).
- frozen prefix: tvo1p1.src = lines 1-23248 of tvo1.src (theorems 1-843), sha256
  41c0075405afa1079c0eb8b760affa64776fcc5b5dab8c85561ebebc8f5370cb; remainder tvo1p2.src (theorems 844-2236, from
  TIndSuc), sha256 aa28feb7edc4087e06233317e50251bf296b20377f74338c82e5625485c474e4; cat p1 p2 = tvo1.src byte for byte.

## R2 2026-09-25 tvo1p2 (theorems 844-2236 of tvo1.src) on pompetzki-a16.exe
- run file forcing-src/r_tvo1p2.pmp (mkf.pl "fa1 .. fh3 tvo1p1" "tvo1p2"): sha256 58f4471571d32de265c3fc229d8a03a4b231b7ba51b773f15ed863377d178d25
- source tvo1p2.src: sha256 aa28feb7edc4087e06233317e50251bf296b20377f74338c82e5625485c474e4 (1393 theorems)
- output r_tvo1p2.out: sha256 c586cca0636a1e5e2d4ca4e29ca8a22890b82ef017bfdaa40c5999eeb12b78d0; runtime pompetzki-a16.exe sha256 99642b63d604515c5218ef95c971d5da946ad03cbc02ecceb8e44a29b3a6e795
- verdict: 1393 accepted in order (TIndSuc .. TNchIntro), nbad 0. With R1: all 2236 theorems of tvo1.src accepted.

## R3 2026-09-25 fn3-fn8 (V lemmas of the notCH* glue) on pompetzki.exe (1 GiB arena) in a JobObject (2048 MiB cap)
- run file r_fn38.pmp (mkf.pl "fa1 .. fh3 fk1 .. fk8 fn1 fn2" "fn3 fn4 fn5 fn6 fn7 fn8"): sha256 ca02f8197703f58c6470e7d74c946dac84ebe5bc7c82c5a0bf2ad7d33e4ff73e
- sources: fn3 659e0986dab26758f63f69b2de458534bc25af331923964b6f244c381e206c48, fn4 ccea8a2799b2c3eaf140469093823071bd7ada846265311495bfafd8df9faeff, fn5 70b9dd35bea2670732de3bc28757015384ccbabdfd41c4f8fa8077f95821a8ad, fn6 e59c4d34af9bea8b5bed01de7292c10c4fda6cd9578be68fb1df0f10f144e960, fn7 a853d992d2f7f5a4fb597a23a375e7489b172c359e97e9b17a3fd56389412daf, fn8 01e3fef8e8fff50a0bbba6756f244684c3d6718dfc57e1e9b833e4c0903fb5f9
- output runs/r_fn38-01/stdout.txt: sha256 3ad717fbc33db60d6bdba2e4e519d5d3613ba1bf2a4fae49724968c3ac3e4243; runtime pompetzki.exe sha256 ccf835920e566b8a45468654798fb9577a261cfec171a707e0438696515a3bec
- verdict: 70 accepted (fn3 9, fn4 21, fn5 6, fn6 13, fn7 12, fn8 9), nbad 0; peak commit 1116205056 bytes.

## R4 2026-09-25 tvn2a (the notCH* translation tail, part independent of tvo1p2 theorems) on pompetzki-a4.exe in a JobObject (5120 MiB cap)
- run file r_tvn2a.pmp (mkf.pl "fa1 .. fh3 fk1 .. fk8 fn1 .. fn8 tvo1p1 tvo1p2d" "tvn2a"; tvo1p2d = the DEF lines of tvo1p2 only): sha256 9485a5f2ac883bd1390c0b3838c96b0c6e6b1266454f72a590fb571650eb1fc4
- source tvn2a.src (splittail.pl tvn2t.src tvo1p2.src): sha256 6aa53a308c030556f0549724f10ca339d3dd12154fcb7adffc850654a0b6dcd2 (383 theorems); tvo1p2d.src sha256 f416e3795b47b4bcf88b65878dc2462c600732eec8f7b82d43186cc59c736a30
- output runs/r_tvn2a-01/stdout.txt: sha256 5b6f479333e139be5ba32be85bd80642e01a4680857e1f2045433e7558b39294; runtime pompetzki-a4.exe sha256 8acdabf76dd496dd5bb2e605dd6b48acf67badf9a230b18626861529c722a57c (a4 regression: r_tv8 verdicts equal to pompetzki.exe)
- verdict: 383 accepted, nbad 0; peak commit 4343685120 bytes.

## R5 2026-09-25 tvn2b (the notCH* translation tail, part using tvo1p2 theorems) on pompetzki-a4.exe in a JobObject (5120 MiB cap)
- run file r_tvn2b.pmp (mkf.pl "fa1 .. fh3 fk1 .. fk8 fn1 .. fn8 tvo1p1 tvo1p2 tvn2a" "tvn2b"): sha256 ecb8a5cb362497065157206d9c63d06fbb18acefa2560247723d60dcbd0b5302
- source tvn2b.src (splittail.pl tvn2t.src tvo1p2.src): sha256 271b6ea77304a460e72e2127d1450aa8532c4f6db5678e8354d1eea4386709ba (239 theorems)
- output runs/r_tvn2b-01/stdout.txt: sha256 9878e6944e7653eb094488c727adb7567d5f1a42f212ba90bfa50e85efebfb61; runtime pompetzki-a4.exe sha256 8acdabf76dd496dd5bb2e605dd6b48acf67badf9a230b18626861529c722a57c
- verdict: 239 accepted, nbad 0 (TNotchT, TNotchU, FinTNotchF among them); peak commit 4343681024 bytes; elapsed 944969000000 ns.
- FinTNotchF depends on the hypothesis VBot (the NotchF harness line "ax Bot | N A x = x x", a test hypothesis, not a
  ZFC axiom); TNotchT and TNotchU depend on accepted done batches only. With R1-R4: tvo1.src (2236), fn3-fn8 (70),
  tvn2t (622 = 383 + 239) all accepted.

## R6 2026-09-25 tvn3t (end-to-end test NotchV: NotCH and Ext, by taut gen dist vac mp, X w Om1 w conjoined with Ext) on pompetzki-a4.exe in a JobObject (5120 MiB cap)
- derivation der_NotchV.txt: sha256 f748944286b0ddb29f1a676aa3d9fc4d9cbdd896a8d257749ae3858f757d1500 (21 lines)
- translation: perl proto2.pl --multi ../lib/zfcbase.pmp IndEmp=.. NchIntro=.. NotchT=.. NotchU=.. NotchF=.. NotchV=der_NotchV.txt > tvn3.src
  (8 s); tvn3.src sha256 31fe1b549758837c1826aa68ad80397476bc52a65bef621b48e8a024dffe2cc1; tvn2.src is a byte prefix of it;
  the tail tvn3t.src sha256 1dc8e7ca1b3ad737b0ae092e5855eeefbf9391fc146f6d923e61caadaa8c0881 (88 theorems; pre1: 0 refused, 0 unchecked)
- run file r_tvn3t.pmp (mkf.pl "fa1 .. fn8 tvo1p1 tvo1p2 tvn2a tvn2b" "tvn3t"): sha256 897e1c93c841177fcaff78f7b97c2d7b286c53a4f059f90eb38944300fa6c174
- output runs/r_tvn3t-01/stdout.txt: sha256 34b7ee33520e7aabb9ba148021897c9de5037bde84da452bd87c7de4b64bbc42
- verdict: 88 accepted, nbad 0; TNotchV (3195 lines, axioms Ext Sep, no test hypothesis) = I CohP1 pp Vw489x2 pp pp,
  Vw489x2 the value name of N I N A w N Om1 w N [Ext]; peak commit 4343726080 bytes; elapsed 466781000000 ns.

## R7 2026-09-25 the general correctness proof in Rocq (forcing-src/general, namespace Cohen)
- toolchain: Rocq 9.1 (Rocq Platform 2026.07.0), coqc and coqchk from C:/ClaudeOutput/formalization-toolchain-20260924/tools/Rocq-Platform-2026.07.0-9.1/bin
- sources: 20 files in dependency order (build.sh); SHA-256 of each, of build.sh, README.md, the audit scripts and the build log in runs/rocq-general-01/sources.sha256 (sha256 of that list: 8897219b1c014deb954946f6cf9c2a0cbddf200828ad42036e6d2310b14a73e8)
- clean rebuild runs/rocq-general-01/build.log: all 20 compiled (longest Notch.v 8 s, Elim.v 8 s); coqchk -o Cohen.Final 131 s: Axioms: <none>, no type-in-type, no unsafe fixpoints, no assumed positivity
- theorem: Final.cohen_relative_consistency : KERNEL -> TNOTCH -> COHEX -> prov Gam0 Bot -> prov ZFpure Bot, and
  con_zfc_con_notch : KERNEL -> TNOTCH -> COHEX -> ~ prov ZFpure Bot -> ~ prov Gam0 Bot (Print Assumptions: closed under the global context).
  For every derivation from Gam0 (seven axioms, Separation, Collection, the 23 ZB_BASE definitions, notCH*); Claim.claim : KERNEL -> TNOTCH -> forall f, prov Gam0 f -> prov Gam (Imp Coh (TOPf (V (pi f)))).
- premises (finite, the kernel's own texts parsed in Rocq): KERNEL (46 Tpl interface theorems of tpl1.src from Gam and their placeholder hypotheses; run runs/r_tpl1-01, in progress), TNOTCH (TNotchT, accepted R5), COHEX (CohEx, accepted R3)
- audits (general/audit, audit-20260925b.txt, audit-20260925c.txt; audit-20260925.txt kept, its hypothesis count superseded by b): the 747 texts of Data.v (46 interface statements, 29 placeholder hypotheses, TNotchT, CohEx, 670 definitions) equal the sources and the run files byte for byte; every definition in the run files t r_tvo1p2 r_fn38 r_tvn2a r_tvn2b r_tvn3t r_tpl1t is identical to r_all's; r_tpl1t registers 29 placeholder hypotheses and 81 theorems of accepted batches (0 unmatched), r_tvn2b 328 batch theorems and the test hypothesis VBot, r_fn38 49 batch theorems

## R8 2026-09-25 tpl1 (the 46 interface theorems and their 1020 lemmas: premise KERNEL of R7) on pompetzki-a4.exe in a JobObject (5120 MiB cap)
- run file r_tpl1t.pmp (mkf output of tpl1, TT emptied after each RUNTHMR): sha256 fac130593797dbc443a337305281ff79e030bc6228bab0244356451369c83bbb
- source tpl1.src (mktpl.pl): sha256 30335e61615ef88ae8a57d920ded95b7dbdf6f1969342ebececc8b024c8ff50b; preflight pre1-tpl1.txt: 1066 theorems, 0 refused
- output runs/r_tpl1-01/stdout.txt: sha256 84b006b6f8b04f75521d21817ad93c9f2c6d2e67b299a191f4454a2d2f67bf30; runtime pompetzki-a4.exe sha256 8acdabf76dd496dd5bb2e605dd6b48acf67badf9a230b18626861529c722a57c
- verdict: 1066 records, nbad 0; elapsed 31928969000000 ns; peak commit 4343750656 bytes.
- the placeholder hypotheses in the kernel's record of each of the 46 interface theorems equal Data.v's lists
  (general/audit/chk_tpl_records.pl, audit-20260925d.txt: 0 differing). With R3, R5 and the batches their runs cite,
  the three premises of R7 are kernel theorems.

## R9 2026-09-25 the chapter examples/cohen-relcon.pmp (mkch.pl version 3 from r_all.pmp; pre1 --pmp r_all.pmp: 3295 theorems, 0 refused)
- chapter sha256 (sha256sum) 2af522c45fa03f86b4879c74bdcdd342f8636f1baed1d8898757911179f11e31; the certificate's program hash 523fd82482cca312c610fbc6a0a15e709db0da22abbb3be96df44b291765a8dc
- run runs/ch_relcon-01 (pompetzki-a4.exe, JobObject 6144 MiB): exit 0, elapsed 12710344000000 ns; stdout sha256 121d37ad60f037617cc177cd4d935ce9ac31965b052f103bb44699f4c8300f67
- examples/cohen-relcon-process.txt: claims established by rule 9 of 9 (63 links; TNotchT derived, no test hypothesis;
  TNotchV derived, no test hypothesis; FinTNotchF derived, names VBot; both controls refused; every lemma derived),
  statements executed 26855043865, "end: every obligation discharged"; table examples/cohen-relcon-table.txt sha256 b06d8175c8fdf37d50a9c38cc35d5cd48cd65a2b485857336a837347132f8941

## R10 2026-09-25 the closed theorem: Con(ZFC) -> Con(ZFC + notCH*) in Rocq with no premise
- RpFinal.cohen_relative_consistency_closed : prov Gam0 Bot -> prov ZFpure Bot; con_zfc_con_notch_closed : ~ prov ZFpure Bot -> ~ prov Gam0 Bot.
  Print Assumptions: closed under the global context. KERNEL_proved, TNOTCH_proved, COHEX_proved: the premises of R7.
- the replay: general/replay/mkreplay.pl transcribes the kernel's run files (lib/zfcbase.pmp, examples/lambda.pmp,
  collapse.pmp, lhull.pmp, forcing-src/r_all.pmp, forcing-src/r_tpl1t.pmp) into RpInit.v and RpB0..10.v (every rule
  re-derived by fcore.pl on the way); the closure of the 46 interface theorems, TNotchT and CohEx: 4551 theorems
  (zfcbase 24, lambda 47, lhull 253, chain 3161, tpl1 1066) over 706 initial entries (7 axioms, 670 definitions, 29
  placeholder hypotheses). The checker (Replay2.v) is proved sound (Replay3.v: check_thm_ok, check_batch_ok);
  RpC0..10.v check each batch by vm_compute (2-8 s each).
- clean rebuild of all 49 files from sources (general/build-closed.sh): runs/rocq-closed-01/build.log sha256 93030a7586e497e7d164d14e956299573b58dac0030a2490bba8372e843a7e92;
  coqchk -o Cohen.RpFinal 336 s: Axioms <none>, no type-in-type, no unsafe fixpoints, no assumed positivity.
- sources, data, scripts and the kernel's run files: runs/rocq-closed-01/sources.sha256 (sha256 of the list e2b1cd98bb48cdeb5c6fb43bab8a1abfe0c3a9b915b58877e329ba6f07338d41).

## Correction 2026-09-26 to R9 (R9 is left as written)
- "table examples/cohen-relcon-table.txt sha256 b06d8175c8fd..." is the sha256 of the table's first 24 lines, not of
  the table. The whole file (3319 lines) has sha256 c1ba040d502cb1724f607e2cf0ed54a309ce33d644f9906caf3e8f1190dda329.
  b06d8175... is what the run's certificate records for that output: the certificate hashes an output file at its
  `write` (here the 24 ZB_BASE lines); the 3295 `append`s after it are not in the certificate's hash of that file.
  Every table the chapters write with `append` (the Cohen chapters' tables) is covered by the certificate only in
  its first write; their full hashes are stated in the receipts.

## R11 2026-09-26 the book on Windows, with the Cohen chapter examples/cohen-closed3.pmp (runs/book-win-02)
- Why a new chapter: runs/book-win-01 (Mathematics.exe of 2026-09-25 17:05, 1 GiB arena) stopped in cohen-closed at
  TIndSuc, "the arena is full" (1216 table lines: the 24 ZB_BASE lemmas and 1192 of the chapter's 3295 theorems), and
  exited with 0xC0000005 while writing its certificate (mathematics-process.txt line 154284 ends inside
  "certificate: program ... sha256 "). forcing-src/arena-probe-20260925 measured the blocks; the fix is
  lib/zfc2.pmp and lib/logic2.pmp (PROGRESS.md 2026-09-26); the chapter is mkch.pl version 6.
- examples/cohen-closed3.pmp sha256 9ac2c913d73a7b1bb62fc3f214972e24bb408c5a70ec20b6badfaeaeed485ae8; lib/logic2.pmp
  sha256 00d0d5746c3a3805277f57c6e2281b38d4560f431f18261fa7cd5d02149b488f; lib/zfc2.pmp sha256
  1bfc119347ac6e0397a8c158e932f3400f819bb51c1ee10753e2467a53fcba03.
- Mathematics.exe (87 chapters) sha256 82df27adaedd4919841b061dc765fee3820265189711a0099584c503e172aa22, 17145841 bytes;
  the certificate's program hash f697f54ba6c7025039ddb7848677ccbd5b34f87864c7b0d9eef1068268c30a7f is the sha256 of the
  17036352 program bytes it carries.
- run (pompetzki 1 GiB arena, JobObject 4096 MiB): exit 0, accepted, elapsed 29607672000000 ns (8 h 13 min), peak job
  commit 1116270592 bytes (the arena is committed whole at the start); stdout sha256
  5fa711a3744df743541953de446d174a0409d7162afcc401d6bc6f2f485c12f5.
- mathematics-process.txt (run of 2026-09-26 01:54:29): "certificate: claims established by rule 295 of 295;
  annotations closed 4 of 4" (286 before, plus the Cohen chapter's 9), "statements executed 39035396949",
  "end: every obligation discharged".
- examples/cohen-closed3-process.txt: the 9 claims established by rule (every hypothesis but VBot is a lemma of lambda,
  collapse or lhull with the same statement; TNotchT derived, no test hypothesis; TNotchV derived, no test hypothesis;
  FinTNotchF derived, names VBot; the two controls refused; every lemma derived and ending in its statement).
- examples/cohen-closed3-table.txt: 3319 lines, sha256 c1ba040d502cb1724f607e2cf0ed54a309ce33d644f9906caf3e8f1190dda329,
  byte-identical to cohen-relcon-table.txt (R9, lib/logic.pmp and lib/zfc.pmp); its first 1216 lines equal
  book-win-01's cohen-closed-table.txt.
