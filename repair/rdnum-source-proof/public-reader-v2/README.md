# Current RDNUM source controller and finite-reader proof

The development executes all 77 instructions of the mechanically extracted
current reader fragment in the unchanged existing `C2Link.PmpCore.exec`
semantics. Its state retains the byte memory, heap pointer, word-variable
dictionary, return stack, instruction cursor, label lookup and finite fuel.
The controller is `Proof/RDNUMSource.v`; the retained bytes and their exact
source-line/instruction mapping are included. The same fragment occurs in
judge-v5 and judge-v6, as recorded by SOURCE-IDENTITY-v5-v6.json.

`RDNUM_buffer_parse_success` and `RDNUM_buffer_parse_failure` relate execution
from the actual RDNUM entry label to the pure `parse_buffer` definition over
an arbitrary finite list of input bytes. The two assumptions are a readable
byte-buffer relation `buffer_segment s (vars s "pos") raw` and the endpoint
equation `vars s "lim" = vars s "pos" + Z.of_nat (List.length raw)`.
The pure lexer itself finds the maximal prefix of the four ASCII whitespace
bytes 32, 10, 13 and 9, then the maximal ASCII digit prefix 48 through 57.
It uses the existing significant-decimal model with arbitrary leading zero
padding, a required nonempty digit token and at most 12 significant digits.
The next byte must be whitespace, or the buffer must end there.

The successful-execution theorem proves the exact returned integer and cursor,
leaves the terminating delimiter and complete suffix unconsumed, preserves the
whole byte memory and heap pointer, and bounds the value by 999999999999 and
signed64. The failure theorem covers empty tokens, significant-digit overflow
and malformed delimiters, reaches the explicit FAIL boundary, and preserves
all bytes below the old heap pointer. If the input endpoint is below or at
that pointer, `RDNUM_buffer_failure_input_unchanged` preserves the complete
original input byte buffer. `RDNUM_buffer_returns_iff` and
`RDNUM_buffer_stops_iff` prove both directions of the result classification.
No hypothesis states that RDNUM already computes its model.

The source loop proof uses the checked 17/23/24-instruction digit branches,
the 18-instruction thirteenth-significant refusal, actual SKIPWS and ENDTOK
execution and call/stop-stack composition. `scan_state_accumulator_invariant`
proves the count/range invariant at every successful finite digit-prefix state.
`source_prefix_next_arithmetic_fits` bounds the actual multiplication
intermediate and subsequent addition, not just the final accepted value.
The cursor subtraction/increment and every fixed scratch subtraction/count
operation agree with signed64 under the stated ordered-address conditions
below 2^62. Diagnostic heap advances are exactly 45, 22 and 36 bytes and fit
signed64 when the old heap pointer is nonnegative and below 2^62.

The text-to-AST extractor remains a trusted mechanical translation. The kernel
proofs establish the operational semantics of that extracted controller;
quoting and hashing source text alone do not establish its denotation.
PmpCore uses mathematical integers; the word-bound theorems show the relevant
operations fit signed64 under their explicit hypotheses. Native interpreter
or compiler correspondence, OS file reading, memory permissions/allocation
capacity, embedding in the complete judge and the final FAIL output/exit
handler remain separate obligations. This is a reader-subroutine theorem,
not a whole-judge or whole-compiler theorem. Original project semantics and
original theorem statements remain in their original development.

Build prerequisites are Python and Rocq 9.1 with MathComp/HB. Run
`python build-proof.py --coqc COQC --coqchk COQCHK` to create a new output tree,
compile all 24 modules and recursively kernel-check the reader modules.
`Proof/RDNUMReceipt.v` prints the exact 33 selected theorem types and their
assumptions. The explicit public whitelist includes source and raw fresh
compiler/kernel logs; generated object files and development iterations
are excluded. Source credits and original module hashes are included.
