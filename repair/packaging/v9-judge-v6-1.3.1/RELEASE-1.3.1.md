# Abschluss 1.3.1 candidate

Judge v6 checks necessary remaining-input byte bounds before allocating registry,
theorem or proof-step arrays. This rejects short malformed inputs whose count
fields previously requested large allocations. The authenticated canonical
registry and exact decimal-token reader are unchanged from v5. The pmp judge
remains the primary checker; Racket is an independent cross-check.

Book v7 selects judge v6 and verifies a posting through the recorded, hash-bound
native or interpreted route. It rejects artifact paths ending in a slash or
backslash. Current Book source and finite execution receipts are selected through
an explicit manifest.

Math Workbench v2 and interpreter runtime v2 retain their frozen source inputs.
The Windows package includes its Racket runtime and support DLLs. The source
package includes the NASM interpreter, direct pmp compiler and Linux runtime
adapter, portable builders, explicit source selections and retained finite test
evidence. Its new packaging recipe supports a fresh source-archive-only rebuild.

The cockpit source selection includes its program, libraries and mathematical
helpers. Historical brainstorm/event journals, digests, conversation instructions,
old local configuration and Chrome DevTools client code are excluded from this
new selection.

The included Rocq proofs establish their stated Gallina/parser-model propositions.
Compilation, matching source hashes, matching native allocated sections and
finite execution tests do not establish a general compiler-preservation theorem
or a whole-executable correspondence theorem.

This candidate is prepared for review. Publication is a separate parent task.
