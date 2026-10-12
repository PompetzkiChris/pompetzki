# Current v6 RECORDCOUNT controller

The v6 judge refuses a certificate record count greater than the remaining input bytes before allocation. This addendum proves the actual eight-instruction `RECORDCOUNT` subroutine in the existing C2Link.PmpCore semantics. The unchanged judge source has SHA256 `87562735cf20dfd18eb5f26348878b2ac6306bc78714d6953565df9c833d0dc7`; its 182-byte fragment at lines 398–405 has SHA256 `33a8406f4545f199f8772b839c9058f62543f3fe2a9f0af3a208df97f41dbca8`.

The checked source execution returns in five instruction steps exactly when `num <= lim - pos`. It reaches the explicit `FAIL` label in seven steps exactly when `num > lim - pos`. Both directions identify the exact final state. The two stored subtraction results are proved after their actual two- and three-step prefixes. No execution-equals-model premise is used.

Return preserves every memory byte, the heap pointer and every variable except `t`. Failure writes the 44-byte diagnostic and its NUL terminator at the old heap pointer, advances the heap by 45 bytes, and changes only `t`, `WHY` and `WHY_len`. Memory below the old heap and at or above old heap plus 45 remains unchanged. Both outcomes preserve the original input bytes.

The count and address hypotheses remain explicit: `0 <= num <= 999999999999` and `0 <= pos <= lim <= hp < 2^62`. The unchanged Grok Bot count model supplies its separate count/remainder arithmetic premise. The checked bounds establish signed-64 representability of both subtraction results, agreement of the negative test, and representability of the diagnostic pointer, length and heap result.

The public subset contains 52 payloads and four controls, including the full MIT license, original C2Link/Groebner and Grok credits, retained source bytes, source-to-instruction map and raw proof receipts. A fresh build compiled 13 modules; recursive kernel checking covered the five controller modules and imported closure. All 19 selected new statement types and eight retained Grok declarations are closed. A second deterministic archive matched byte for byte.

Sources and receipts are in `repair/recordcount-source-proof/public-v1`. The release archive is `recordcount-source-controller-proof-public.zip`, 72,833 bytes, SHA256 `261c4d15c50745ed3844569270459fe440bc913778563132748c04e1e0e8b638`. `RECORDCOUNT-SHA256SUMS.txt` covers that archive alone. The existing ten release assets and tag retain their identities and bytes.

PmpCore uses mathematical integers and a total byte-memory function. The text-to-AST extractor remains trusted. Native/interpreter compiler correspondence, OS input, allocation capacity and permissions, caller contracts, complete-judge embedding, and the final FAIL output/exit handler remain separate obligations. This addendum proves the extracted subroutine under its stated contract.
