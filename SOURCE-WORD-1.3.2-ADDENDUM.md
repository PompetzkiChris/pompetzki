# Current RECORDCOUNT source and word operations

The current judge's eight RECORDCOUNT instructions retain their 182 bytes and SHA256 `33a8406f4545f199f8772b839c9058f62543f3fe2a9f0af3a208df97f41dbca8`. The prior operational source proof retains its original contract and statements. This new development connects both actual subtraction prefixes and the actual negative test to unsigned 64-bit words.

Under `0 <= num <= 999999999999` and `0 <= pos <= lim <= hp < 2^62`, the two wrapped results decode to the corresponding source integers. The checked word's top bit equals the actual CNeg test and characterizes the existing return and FAIL outcomes. The retained signed projection models agree on those bounded results.

The native primitive theorems unfold the unchanged X86Native3 execution definitions for SUB and `TEST r,r`. They derive result, sign flag, register and memory frames under explicit operand representation. Address encoding, LA48 canonicality and readable-region access are checked separately. The closed `2^47` counterexample shows that the numeric source contract alone does not imply LA48 canonicality; it is a theorem about that premise, not a reported runtime failure.

All 36 new declarations are closed. Fresh compilation covers 22 modules plus one separate readable-type module; the explicit recursive kernel check covers all 23 targets, exits 0, and reports no axioms. The public archive retains 87 payload files and four controls, the full MIT license, original Pompetzki/C2Link/Groebner/CX4/Grok credits, unchanged source/map, complete selected types and successful raw receipts. A second deterministic archive matches byte for byte.

`recordcount-source-word-proof-public.zip` is 107,759 bytes, SHA256 `f0d1a3c64b39c1c8940d40f8a9540269a57d06d19e0e2c9012556e639de3acb3`. `SOURCE-WORD-SHA256SUMS.txt` covers that archive alone. Sources and receipts are in `repair/recordcount-word-bridge-v1/public-v1`.

Text-to-AST extraction remains trusted. Native variable layout and loads/stores, compiler template/image/fetched-step correspondence, the missing JS condition/decoder in the preserved model, permissions, allocation capacity, stack, final FAIL handler, OS process, caller contracts and complete judge remain separate obligations. No runtime, judge or earlier proof source was changed by this development.
