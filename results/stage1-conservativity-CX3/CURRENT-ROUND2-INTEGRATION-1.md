# Current Round 2 Gam and pure-ZF integration

Receipt clock from date.exe: 2026-10-09T20:52:28-04:00. CX3 reused completed APIs and receipts; no compiler, kernel checker or judge job was started.

3/46 targets have completed recursive kernel receipts: 480 theorems and 26286 steps. 13 targets have completed compiler receipts: 7442 theorems and 215169 steps. The remaining rows retain their stated pending status.

The seven baseline batches remain separately completed: 1,656 theorems and 53,069 steps. INTEGRATION-RECOVERY-1.md/json contains their source, object, module and kernel receipts.

Each completed member theorem gives prov Gam (tof (t_stmt t)) and prov ZFpure of its faithful expansion. The 11-definition stage2_expand applies to wave-2 and L71-L75; L6 and L76 use the 18-definition dependency-closed round2_expand. Both preserve registered definitions. Their proof paths reuse CX3.Stage2Conservativity2.accepted_member_Gam, covered_expansion_pure and CX3.Conservativity2.expanded_theorem_pure.

The registry at the start is the canonical 677 prefix. Completed identities and metadata discharge reg_ok, empty theorem hypotheses and exact expansion coverage. Pending targets acquire closure only after those certificates and their recursive kernel receipts complete. Any explicit qualified-registry premise must remain in the exported theorem. The JSON records the exact statement and status separately.

No pmp interpreter resource condition is used by these mathematical closure theorems. A recorded gosub/memory resource stop is retained as a resource stop. Actual interpreter-to-check_batch and actual ELF-to-check_batch proofs remain with their owners. Assumption summaries below belong to these named completed modules; no assertion is made about other modules or global Corelib contexts.

| ID | Theorems | Steps | Final module | Expansion | Status | Closed assumption prints |
|---|---:|---:|---|---|---|---:|
| W00 | 140 | 7262 | CX3B.Round2CertificateW00 | stage2_expand | KERNEL_CHECKED_CLOSED_MEMBERS | 7 |
| W01 | 160 | 8762 | CX3B.Round2CertificateW01 | stage2_expand | KERNEL_CHECKED_CLOSED_MEMBERS | 7 |
| W02 | 180 | 10262 | CX3B.Round2CertificateW02 | stage2_expand | KERNEL_CHECKED_CLOSED_MEMBERS | 7 |
| W03 | 200 | 11762 | CX3B.Round2CertificateW03 | stage2_expand | COMPILED_KERNEL_PENDING | 7 |
| W04 | 300 | 6353 | CX3B.Round2CertificateW04 | stage2_expand | TARGET_PENDING | 0 |
| W05 | 324 | 6775 | CX3B.Round2CertificateW05 | stage2_expand | TARGET_PENDING | 0 |
| W06 | 351 | 7242 | CX3B.Round2CertificateW06 | stage2_expand | TARGET_PENDING | 0 |
| W07 | 381 | 7754 | CX3B.Round2CertificateW07 | stage2_expand | TARGET_PENDING | 0 |
| W08 | 414 | 8312 | CX3B.Round2CertificateW08 | stage2_expand | TARGET_PENDING | 0 |
| W09 | 117 | 2092 | CX3B.Round2CertificateW09 | stage2_expand | TARGET_PENDING | 0 |
| W10 | 132 | 2377 | CX3B.Round2CertificateW10 | stage2_expand | TARGET_PENDING | 0 |
| W11 | 147 | 2662 | CX3B.Round2CertificateW11 | stage2_expand | TARGET_PENDING | 0 |
| W12 | 162 | 2947 | CX3B.Round2CertificateW12 | stage2_expand | COMPILED_KERNEL_PENDING | 7 |
| W13 | 592 | 14287 | CX3B.Round2CertificateW13R | stage2_expand | COMPILED_KERNEL_PENDING | 7 |
| W14 | 656 | 16197 | CX3B.Round2CertificateW14 | stage2_expand | COMPILED_KERNEL_PENDING | 7 |
| W15 | 715 | 18081 | CX3B.Round2CertificateW15 | stage2_expand | COMPILED_KERNEL_PENDING | 7 |
| W16 | 785 | 20288 | CX3B.Round2CertificateW16 | stage2_expand | COMPILED_KERNEL_PENDING | 7 |
| W17 | 850 | 22471 | CX3B.Round2CertificateW17 | stage2_expand | COMPILED_KERNEL_PENDING | 7 |
| W18 | 926 | 24995 | CX3B.Round2CertificateW18 | stage2_expand | COMPILED_KERNEL_PENDING | 7 |
| W19 | 997 | 27497 | CX3B.Round2CertificateW19 | stage2_expand | COMPILED_KERNEL_PENDING | 7 |
| W20 | 1079 | 30358 | CX3B.Round2CertificateW20 | stage2_expand | COMPILED_KERNEL_PENDING | 7 |
| W21 | 259 | 8906 | CX3B.Round2CertificateW21 | stage2_expand | TARGET_PENDING | 0 |
| W22 | 370 | 22872 | CX3B.Round2CertificateW22 | stage2_expand | TARGET_PENDING | 0 |
| W23 | 178 | 5388 | CX3B.Round2CertificateW23 | stage2_expand | TARGET_PENDING | 0 |
| W24 | 213 | 6548 | CX3B.Round2CertificateW24 | stage2_expand | TARGET_PENDING | 0 |
| W25 | 203 | 6883 | CX3B.Round2CertificateW25 | stage2_expand | TARGET_PENDING | 0 |
| W26 | 210 | 7025 | CX3B.Round2CertificateW26 | stage2_expand | TARGET_PENDING | 0 |
| W27 | 229 | 7963 | CX3B.Round2CertificateW27 | stage2_expand | TARGET_PENDING | 0 |
| W28 | 218 | 7310 | CX3B.Round2CertificateW28 | stage2_expand | TARGET_PENDING | 0 |
| W29 | 177 | 5689 | CX3B.Round2CertificateW29 | stage2_expand | TARGET_PENDING | 0 |
| W30 | 203 | 5989 | CX3B.Round2CertificateW30 | stage2_expand | TARGET_PENDING | 0 |
| W31 | 224 | 5710 | CX3B.Round2CertificateW31 | stage2_expand | TARGET_PENDING | 0 |
| W32 | 207 | 7541 | CX3B.Round2CertificateW32 | stage2_expand | TARGET_PENDING | 0 |
| W33 | 200 | 5508 | CX3B.Round2CertificateW33 | stage2_expand | TARGET_PENDING | 0 |
| W34 | 217 | 7208 | CX3B.Round2CertificateW34 | stage2_expand | TARGET_PENDING | 0 |
| W35 | 209 | 6828 | CX3B.Round2CertificateW35 | stage2_expand | TARGET_PENDING | 0 |
| W36 | 202 | 6894 | CX3B.Round2CertificateW36 | stage2_expand | TARGET_PENDING | 0 |
| W37 | 204 | 6144 | CX3B.Round2CertificateW37 | stage2_expand | TARGET_PENDING | 0 |
| W38 | 195 | 6017 | CX3B.Round2CertificateW38 | stage2_expand | TARGET_PENDING | 0 |
| L6 | 345 | 37714 | CX3B.Round2CertificateL6 | round2_expand | TARGET_PENDING | 0 |
| L71 | 40 | 1720 | CX3B.Round2CertificateL71 | stage2_expand | TARGET_PENDING | 0 |
| L72 | 98 | 7057 | CX3B.Round2CertificateL72 | stage2_expand | TARGET_PENDING | 0 |
| L73 | 5 | 5 | CX3B.Round2CertificateL73 | stage2_expand | TARGET_PENDING | 0 |
| L74 | 17 | 79 | CX3B.Round2CertificateL74 | stage2_expand | TARGET_PENDING | 0 |
| L75 | 47 | 10690 | CX3B.Round2CertificateL75 | stage2_expand | TARGET_PENDING | 0 |
| L76 | 102 | 2360 | CX3B.Round2CertificateL76 | round2_expand | TARGET_PENDING | 0 |

The JSON lists exact JDG/source/object hashes, closure theorem names, registry/resource conditions, compiler/kernel receipt paths and candidate comparisons. The copy plan lists immutable source and completed receipt inputs for the COO overlay. Local .vo hashes are evidence of checked objects; this source package excludes .vo files.

Candidate inspected: C:/ClaudeOutput/pompetzki/lanes/CEO/executive-20261009-183208/package/coo-candidate-20261009-200631. MIT license, copyright 2026 Christopher Pompetzki; the exact LICENSE hash is recorded in the JSON. Candidate outer-manifest/archive checks must be refreshed after its owner incorporates the overlay.
