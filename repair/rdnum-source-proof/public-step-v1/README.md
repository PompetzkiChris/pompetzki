# Current RDNUM instruction-step proofs

This subset executes the mechanically extracted 77 instructions of the retained
judge-v5 reader fragment in the unchanged existing `C2Link.PmpCore.exec`
semantics. It preserves that semantics' byte memory, heap pointer, variable
dictionary, call stack, label lookup, fuel, and explicit failure stops.

The completed statements prove the leading-zero path (17 instructions), later
significant-digit path (23), first nonzero-digit path (24), and refusal of a
thirteenth significant digit (18). The refusal leaves `num`, `nd`, and `pos`
unchanged and preserves memory below the old free address. The whitespace
routine consumes exactly a prescribed prefix of bytes 32, 10, 13, and 9 and
preserves all memory and the heap. The token-end routine accepts EOF or those
four whitespace bytes, leaves the delimiter unconsumed, and otherwise stops
at FAIL with the corresponding diagnostic text.

`RDNUM_finish_success` composes the actual current source's digit-loop exit,
ENDTOK call, and return. It preserves memory, heap, and every variable outside
the three scratch names `t`, `c`, and `d`. The source multiplication and addition
updates fit signed64 under the stated significant-count and accumulator
invariant. The cursor subtraction also agrees with signed64 and integer order
when the ordered cursor/end addresses lie below 2^62.

The source snapshot is pinned to SHA256
`4d936cb8103c6aa97fb6ec290f88b3ee636c69f94f0cdb089a4621d9ba251d1b`.
The fragment is lines 477 through 561, 1,724 bytes, SHA256
`7a282dc71308a1796a0690bce400938a936dd60efcdc70257671660f842a3826`.
The raw bytes, instruction-to-line map, and explicit PmpCore controller are
included. The v6 source shares the retained reader block; its identity receipt
states the precise compared spans.

The text-to-AST extractor remains a trusted mechanical translation. The
kernel-checked instruction theorems establish semantics of that extracted
controller; source quotation and hashing alone do not establish semantics.
`PmpCore` performs arithmetic on mathematical integers. The stated bounds
show that the relevant operations fit signed64; the development does not
prove the interpreter or native compiler implements all PmpCore operations,
OS file reading, memory permissions, or the full judge's parser/registry/body.
FAIL is the existing explicit stop boundary, rather than the full output/exit
handler. The arbitrary-sequence and complete-entry proofs continue separately.

Build prerequisites are Python and Rocq 9.1 with the existing MathComp/HB
libraries. Run `python build-proof.py --coqc COQC --coqchk COQCHK` to compile
fresh copies and recursively kernel-check the selected modules. Every output
directory is new. `Proof/RDNUMReceipt.v` prints the exact 12 selected statement
types and their assumptions; the original theorem types remain at their
original project source paths.
