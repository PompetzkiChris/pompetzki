# Finite-buffer reader proof for Abschluss 1.3.1

The expanded reader development proves correspondence between an arbitrary finite input byte buffer and execution of the current RDNUM source controller. It compiles 24 modules, recursively kernel-checks all 17 reader modules, and prints 33 selected closed theorem types with no axioms in their global contexts.

The proof executes the actual 77 extracted instructions in the retained `C2Link.PmpCore.exec` semantics, including the RDNUM entry, SKIPWS, counter resets, digit loop and ENDTOK. The buffer assumptions are a readable byte-buffer relation and the equation relating its endpoint to its length. The pure lexer derives the leading whitespace and digit spans itself.

Successful execution returns the exact decimal integer and cursor, leaves the delimiter and suffix unconsumed, and preserves byte memory and the heap pointer. Failure reaches the explicit FAIL boundary for empty tokens, more than twelve significant digits, or malformed delimiters, while preserving bytes below the original heap pointer. Both directions of the success and failure classifications are proved. Separate statements bound the actual intermediate multiplication and addition at each successful digit prefix, with explicit signed-64 and ordered-address hypotheses.

The 1,724-byte controller fragment is identical in judge v5 and judge v6, SHA-256 `7a282dc71308a1796a0690bce400938a936dd60efcdc70257671660f842a3826`. The public addendum selects 87 source and receipt files plus four controls. It includes exact theorem statements, source credit, the instruction map, and raw fresh compiler and recursive kernel outputs.

The text-to-AST extractor remains trusted. Interpreter/compiler correspondence, OS file reading, memory permissions and allocation capacity, embedding in the complete judge, and the final FAIL output/exit handler remain separate obligations. The operational semantics uses mathematical integers; the word-bound lemmas require their declared hypotheses.

The [proof source and receipts](repair/rdnum-source-proof/public-reader-v2/README.md) are supplied separately as `rdnum-finite-reader-proof-public.zip` in [release 1.3.1](https://github.com/PompetzkiChris/pompetzki/releases/tag/v1.3.1). `READER-V2-SHA256SUMS.txt` covers that addendum. The earlier instruction-step archive remains a separate asset.
