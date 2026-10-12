# Current v6 RECORDCOUNT source controller

This new development retains judge-v6.pmp SHA256
87562735cf20dfd18eb5f26348878b2ac6306bc78714d6953565df9c833d0dc7
and mechanically maps its eight RECORDCOUNT instructions, lines 398–405,
into the unchanged existing C2Link.PmpCore.exec semantics. The 182-byte
fragment has SHA256 33a8406f4545f199f8772b839c9058f62543f3fe2a9f0af3a208df97f41dbca8.
The exact retained bytes, constructor controller and source-line/PC map
are in source/ and Proof/RecordCountSource.v.

The source prefix theorems execute the first subtraction in two PMP steps
and the second in three. RECORDCOUNT_returns_iff proves actual entry returns
exactly when num<=lim-pos, with final state equal to the two actual updates.
RECORDCOUNT_fails_iff proves actual entry reaches explicit FAIL exactly when
num>lim-pos, with final state equal to the actual diagnostic allocation.
The fixed executions consume five and seven PMP instruction steps respectively.
The instruction counts include labels, as prescribed by PmpCore semantics.

The exact t result is lim-pos-num. Successful return preserves every byte,
the heap pointer and every variable except t. Failure sets WHY to the old
heap pointer and WHY_len to 44, stores the 44 ASCII diagnostic bytes and a
zero terminator, and advances the heap by 45. Every byte below the old heap
or at/above oldheap+45 is preserved. Every variable except t, WHY and WHY_len
is preserved. These effects are tied to actual controller execution rather
than assumed equality to a declared arithmetic model.

The explicit count_address_contract is:
0<=num<=999999999999; 0<=pos<=lim; lim<=hp; hp<2^62.
RECORDCOUNT_actual_subtractions_fit imports the unchanged Grok Bot
rem_sub_num_fits declaration with its separate count/remainder premises.
It proves both actual stored subtraction results fit signed64 and the second
is negative exactly when num>lim-pos. The signed64 projection identity and
negative-test agreement are checked separately. Diagnostic pointer, length
and heap result also fit signed64. Every original input byte at an address
pos<=a<lim remains unchanged under either result.

PmpCore has a total byte-memory function and mathematical-integer arithmetic.
The ordered-address contract states numeric and frame assumptions; it does
not prove native memory permissions or allocation capacity. The source
extractor is a trusted mechanical text-to-AST translation. Interpreter/native
compiler correspondence, OS input, complete-judge embedding/caller contracts
and the final FAIL output/exit handler remain separate obligations. This is
the operational theorem of the extracted eight-instruction subroutine; no
source-execution-equals-model premise is used.

Vendor semantics are exact unchanged copies from the preserved project
C2Link and Groebner developments. Both Grok Bot sources are exact unchanged
copies of the reviewed count-guard arithmetic/list-model delivery; its eight
original declarations and their scope remain intact. New source-step, frame,
byte-memory and bound proofs are by Codex 2026-10-12. Existing runtime, judge,
reader proofs and public assets were not edited.

Run python build-proof.py --coqc COQC --coqchk COQCHK with Rocq 9.1 and the
existing MathComp/HB dependencies. It creates a new output directory and
freshly compiles all 13 modules, then recursively checks the five RECORDCOUNT
modules and imported closure. RecordCountReceipt prints the exact 19 selected
new statement types, controller and address contract. GrokRecordCountVerify
prints the eight retained arithmetic/list-model types separately.

Development iterations and failed compiler runs are retained. A concrete
diagnostic-memory conversion stalled in iteration 050535-215229; only that
owned compiler/worker was stopped. Generic text-memory lemmas avoid that
literal expansion; the exact memory statements and source bytes are unchanged.
