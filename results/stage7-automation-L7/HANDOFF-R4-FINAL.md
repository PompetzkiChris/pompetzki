# L7 HANDOFF-R4-FINAL (written 20:45, date)

HANDOFF-R4.md (sha256 8e2cc83fba3ba922e74e023cf03ec543eeccc9202667b79efded8e0471696445) stands. One addition after it:

## Added: out-r4\L7-5-farkas-cyc.jdg
- Certificates (src-r4\genfarkas-v1.rkt): cyclic chains x1 - x2 <= -1, ..., xk - x1 <= -1 for k = 2, 3, 4, 5 (y = all ones), and planted systems planted-120-n1-m2, planted-121-n1-m2, planted-122-n1-m2 (exact LCG seed 20261009; A, b, y listed in out-r4\L7-5-farkas-cyc.manifest.txt). Statement form and encoding as L7-5-farkas-l2d.jdg (no rational solution, x = (u - v)/w).
- 293 theorems, 6,620 steps, 13,976,123 bytes, final registry 970.
- pmp ACCEPT exit 0 (581.4 s), Racket ACCEPT exit 0 (2.8 s). 13 mutants: pmp REJECT exit 1 and Racket REJECT exit 1 on all 13. Window 20:34 to 20:44:49 (judge-r4-cyc*.start/end.txt).
- Reproduce: cd src-r4; racket emit-r4-v2.rkt OUTDIR.

## SHA-256 of the addition
    1aaec277b03114b5235baecb5f08295455393e44dfb22f89d2eb2ab3ac73438b *out-r4/L7-5-farkas-cyc.jdg
    ff3be0ee36d5f62d0f16f5d4379c92b53d49a776d9ecd2e6eb11391adc7331ac *src-r4/emit-r4-v2.rkt
    453919e9dd5f52a2179f0a0022d106a88d3ccc056ad6e4272e5269b303337d86 *judge-r4-cyc.txt
    50152ea1b618dd45f05a9e58a796154980e083192eb1bd1ddc0713813dc955f1 *judge-r4-cyc-m1.txt
    609a5bcbf6c12f0e103b76e5bcff853fb16904157b9f5e99acbe488c4d985076 *judge-r4-cyc-m2.txt
    ccfc6c0c220a7ea935407259dc502bb68848aba28e0b13d6be7feff3a5fc6fda *judge-r4-cyc-m3.txt
    944420b1f231a3bd1fe84a214770bbf5b9298a00dda2e7ecd7d3d6203b2e7470 *out-r4/L7-5-farkas-cyc.manifest.txt
    8e2cc83fba3ba922e74e023cf03ec543eeccc9202667b79efded8e0471696445 *HANDOFF-R4.md

## Release list (all ACCEPT on both judges, mutants all REJECT on both)
- Round 1: out\L7-4-omega-laws.jdg, out\L7-1-equality.jdg, out\L7-1-eqchain-pmp.jdg, out\L7-2-tautologies.jdg, out\L7-2-direct-control.jdg, out\L7-3-quantifiers.jdg (42 mutants).
- Recovery: out-r4\L7-6-order.jdg (13 mutants), out-r4\L7-5-farkas-l2d.jdg (13), out-r4\L7-5-farkas-cyc.jdg (13).
- Totals: 9 files ACCEPT on both judges; 81 mutants REJECT on both.

## Open (unchanged from HANDOFF-R4.md, items 2 to 5; item 1 reduced)
1. Farkas: G2 corpus not processed (no INDEX.tsv read); cyclic k = 6, 7 and the other 24 planted systems have no judge receipts.
2. General polynomial normalizer over ω: not written.
3. Native pmp emitters for tautology, Farkas-linear, rank, general polynomial: not written (only src\eqchain-v1.pmp exists).
4. Mul-chain and distributive chain lemma families: not written.
5. Lt <-> membership for naturals: not proved.
No pmp resource stop (too deep / memory block full) occurred in any L7 run.
