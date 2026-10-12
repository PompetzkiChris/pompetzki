# Grok Bot count-guard arithmetic and record syntax model

The two original Grok Bot Rocq source files are retained byte for byte. A fresh
independent Windows Rocq 9.1.0 compilation passed for both modules, followed
by a recursive kernel check with no axioms, type-in-type dependencies, unsafe
fixpoints or assumed positivity. All eight proof declarations print as closed
under the global context. Source credit, sender report, exact printed types,
fresh compiler/kernel output and an explicit source manifest are included.

`fits64 x` means `-2^63 <= x <= 2^63-1`. The closed statements are:

- `rem_sub_num_fits`: with `0 <= num <= 999999999999` and
  `0 <= rem <= 2^63-1`, the difference `rem-num` fits signed64, and it is
  negative exactly when `num > rem`.
- `num_mul8_fits`: the same decimal bound on `num` makes `num*8` fit signed64.
- `num_prefix_sum_fits` and `num_prefix_mul24_fits`: the separate premises
  `0 <= num <= 999999999999` and `0 <= prefix <= 706` suffice for the sum and
  `(num+prefix)*24`. The count is not constrained by the prefix's bound.
- `num_prefix_mul24_bound`: under those separate premises the product lies
  between zero and exactly `24000000016920`.
- `records_le_bytes`: for every type A and list of records, each record must
  be a nonempty list of A; record count is then at most concatenated length.
  Choosing A as bytes gives the minimum-one-byte-per-record model.
- `records_le_rem`: additionally assuming concatenated length <= rem yields
  record count <= rem. Its serialized-length premise is explicit.
- `pow2_63`: `2^63 = 9223372036854775808`.

These are universal integer and list-model theorems. They do not prove that
the actual reader supplies these hypotheses, that pmp/Racket/native code
implements these guard expressions, that real serialization or remaining
input agrees with the list model, or that compiler/executable preservation,
memory capacity or allocation behavior holds. The sender's report describes
its own run; the receipt directory contains the independent Windows run.

Build prerequisites are Python and Rocq 9.1.0 with Stdlib. Run
`python build-proof.py --coqc COQC --coqchk COQCHK`; it creates a new tree,
copies only the pinned `.v` sources, compiles both modules, and recursively
checks them. No delivered binary objects are used. Private transport records
and the sender's machine-specific shell recipe are excluded from this public
subset. The raw independent command/diagnostic receipts retain their local
C:\ClaudeOutput toolchain and build paths.
