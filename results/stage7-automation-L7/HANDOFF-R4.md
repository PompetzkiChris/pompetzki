# L7 HANDOFF-R4 (written 20:32, date)

Lane L7 (Stage 7 automation emitters), session 0c7e86d9-5a68-4a4d-b4f4-7d38ea17497c, folder C:\ClaudeOutput\pompetzki\lanes\L7.

## Recovery facts
- The emission running at 19:30 (scratch folder ...\scratchpad\dry\fk4, emit-farkas-v3.rkt, cyclic and planted certificates) died in the power loss. Its partial output stays where it is and is NOT part of this handoff.
- No L7 job was alive at 20:18 (date). Round-2 sources survived in the old scratch folder; copied unchanged into src-r4\ (sha256 below). New driver src-r4\emit-r4-v1.rkt.

## Accepted outputs (both judges, run from C:\ClaudeOutput\pompetzki\judge)
Commands: ..\pompetzki.exe judge-v3.pmp FILE ; "C:\Program Files\Racket\racket.exe" racket\judge.rkt FILE (wrapper src-r4\judge-run-v1.rkt; rows with exit codes and full judge output in judge-r4-*.txt).

Round 1 (18:46, RESULTS.md, judge-omega-1/eq-1/pmpchain-1/taut-1/quant-1.txt): six files ACCEPT exit 0 on both judges, 42/42 mutants REJECT exit 1 on both:
out\L7-4-omega-laws.jdg (ω laws: AddComm, AddAssoc, MulComm, MulAssoc, DistL, AddZL, AddSL, MulZL, MulSL by induction), out\L7-1-equality.jdg, out\L7-1-eqchain-pmp.jdg (emitted by the pmp program src\eqchain-v1.pmp), out\L7-2-tautologies.jdg, out\L7-2-direct-control.jdg, out\L7-3-quantifiers.jdg.

Recovery round (window 20:20 to 20:32, date):
- out-r4\L7-6-order.jdg: 116 theorems, 2,698 steps, final registry 793. pmp ACCEPT exit 0 (77.1 s), Racket ACCEPT exit 0. Lemmas (general, all x,y,z in ω): NatCases, AddCancelR, AddCancelL, ZeroSum, RComm, AssocEq, LeRefl, LeTrans, AddSelf, LeAntisym, LtIrrefl, LeSucc, LeTotal, LeAddMono, LeAddCancel, ZeroProd, MulCancel1, MulCancel (Nat x,y,z & not Emp z & Mul(x,z,u) & Mul(y,z,u) -> x = y). Le(x,y) := exists d (Nat d & Add(x,d,y)); Lt adds not Emp(d). 13 mutants REJECT exit 1 on both.
- out-r4\L7-5-farkas-l2d.jdg: L2D's four certificates lanes\L2D\farkas\in\f1-1d..f4-2d.sexp (source attribution: L2D) as theorems "Nat u,v,w & not Emp w -> not (Row_1 & ... & Row_m)", i.e. A x <= b has no rational solution with x = (u - v)/w (L2D's encoding), proved by unary Add-chains (src-r4\sums-v4.rkt), insertion sort, Split, cancellation and ZeroSum (src-r4\farkas7-v5.rkt). 236 theorems, 4,985 steps, 7,358,716 bytes, final registry 913. pmp ACCEPT exit 0 (374.8 s), Racket ACCEPT exit 0 (2.7 s). 13 mutants REJECT exit 1 on both.
- Reproduce: cd src-r4; racket emit-r4-v1.rkt OUTDIR (deterministic; sha256 below).

## SHA-256
    f96e7a39762360866833bfead8dc8928ddb273f72b49218db43b3697bae176d8 *src-r4/emit-r4-v1.rkt
    3a8fa521996fb30c2adc7ab99fa176425e27b278f85fcefa309bfc0ba0a2fbb7 *src-r4/farkas7-v5.rkt
    4c65bdba086bda48b8ba9dad60b28d6855f6193185f5f9a5d918b16dc2d64549 *src-r4/genfarkas-v1.rkt
    b7620f5d573b4a131f48f0bb496ed5376d56b423dc2c42815ca42e95ac49e851 *src-r4/judge-run-v1.rkt
    7827b3781a02fa24285b12e8422810adfdf506ca1144e2dd6e761a870b53d087 *src-r4/l7core-v1.rkt
    ab79425cf21197b9082ae4a1eb44fb825dab72fa4781a1af7ae6b7d66c151551 *src-r4/mutants-v1.rkt
    7aad50168c0660e1ad6892c83a7207b140b6b648d568622e8d5c196e120b51f1 *src-r4/mutants-v2.rkt
    9ed06e26293545cc2e9949fa672bdefbabfd9cb302521b87d9cd785fa60f87f7 *src-r4/omega-base-v1.rkt
    760c26abf397f45717c3ad254486b39fc58821727a93bfd81b75fc989aa55d43 *src-r4/omega-kind-v5.rkt
    f875f0a85572de1a12cf5c70002941c8d00aa64b5eecdd0bcc5573fa06eddac1 *src-r4/omega-laws-v3.rkt
    021edcb7658d105e4f03a6811e523fd5a3977720f9c4b2dd371440575b1af707 *src-r4/order2-v4.rkt
    f8ebd1356ed1072b05f029f8879a8d2244ad086c64549b6c66225225b81dcd44 *src-r4/parencheck.rkt
    2f00681758fb216f3f48931949e146753d2bf6f4a30c1aa0d87051e458eff76b *src-r4/sums-v4.rkt
    e669ea0da07482d950d8c221074ff2fabd5c1f7f03d5c5a60437816fa3b9cfba *out-r4/L7-5-farkas-l2d.jdg
    f944bb6ced59adf57338695ba37f08eccc0b5dd8db6519c8678cff3b5130f45f *out-r4/L7-6-order.jdg
    8fdb1ca3160d5e56e2177fe80ad0158ca5f77d845312c77e0a1b6fd981ab7ad8 *out/L7-1-eqchain-pmp.jdg
    289f44b94ef64cf8ef66dabdd73ea4d2009d6b75b8e11d27db5b345d01930fb3 *out/L7-1-equality.jdg
    b4c034a5acd79b4940805149fa247fd29f41a95ca6cef38bbbcbc5f18895bb9c *out/L7-2-direct-control.jdg
    f42eaffa7ce095682201264962656c76e6e0226f1bbf359316cf247c03317ee7 *out/L7-2-tautologies.jdg
    f925e0b804fb854ea66241fbe13a61d01df05e829484024a94cacfc8a0fa4535 *out/L7-3-quantifiers.jdg
    fdcaa25b28d9be7d97b7ab34998a35f519e736de2892de3ccf5e8d484f60bc14 *out/L7-4-omega-laws.jdg
    cd1fb74d59d0acbe6bd31573b779597cc4951afb3364080bb8161ea3f6f1bd04 *src/eq-v1.rkt
    7827b3781a02fa24285b12e8422810adfdf506ca1144e2dd6e761a870b53d087 *src/l7core-v1.rkt
    9ed06e26293545cc2e9949fa672bdefbabfd9cb302521b87d9cd785fa60f87f7 *src/omega-base-v1.rkt
    760c26abf397f45717c3ad254486b39fc58821727a93bfd81b75fc989aa55d43 *src/omega-kind-v5.rkt
    f875f0a85572de1a12cf5c70002941c8d00aa64b5eecdd0bcc5573fa06eddac1 *src/omega-laws-v3.rkt
    8328439f819d04f5bc510ea6442aa510810ebdb1ca5c59eaa1d02a78e8ab7203 *src/pnx-extra-v2.rkt
    984eafceab6c331e6c7cedd915df319090c3523886119aab1663803398bf7c53 *src/pnx-v1.rkt
    0cd5ff76c78fb207c7379bf27d4f0a815198bcc0657a00f178f032741c2f4068 *src/taut-v3.rkt
    c12b986d18c27493cd7e66d9465d1e681d70b8dd701afd6761a6c6a41c0c67cf *src/eqchain-v1.pmp
Full list: L7\sha256-r4.txt (46 entries). Receipts: judge-r4-order.txt 3515c8e3..., judge-r4-farkas.txt 9e25e5e6..., judge-r4-farkas-mutA.txt 628a447c..., judge-r4-farkas-mutB.txt ac2670ee... (full hashes in this folder via sha256sum).

## Cited, not L7's work
- C:\ClaudeOutput\utilization-20261009-185137\derived-repair\polynomial-pmp-v3.pmp, sha256 c360e490fdde64948c76cfea7ab8dce2998c06efc53577c5addc55e4f0d9e883 (CEO repair): one identity x*(y+z) = y*x + z*x. Not a general normalizer.

## Open (exact items not delivered)
1. Farkas beyond L2D's four: cyclic chains (genfarkas-v1.rkt cyclic 2..7) and planted systems were derived and accepted by the checker copy in scratch before 19:30, but no file of them has judge receipts. G2's corpus (lanes\G2-farkas) had no INDEX.tsv when last read (19:11). Observed resource facts: a 7.4 MB Farkas file passes pmp in 374.8 s; the emitter's unary chains grow with |coefficients| x multipliers, so G2-size coefficients (up to 50) are out of reach of this encoding.
2. Polynomial identities over ω (general normalizer): not written. Design only (degree <= 2 via Ch chains and DistL/DistR chain lemmas).
3. Native pmp emitters for tautology, Farkas-linear, rank and general polynomial families: not written. The only L7 pmp emitter is src\eqchain-v1.pmp (equality chains).
4. Mul-chain lemma families (MCh, MIns) and DistRCh/DistLCh: not written.
5. Lt <-> membership (x in y) for naturals: not proved.

## Process record
order2-v3.rkt (scratch) was changed in place by sed -i and its .bak deleted (19:00 approx.); later versions are new files. Superseded drafts remain in the scratch folder.
