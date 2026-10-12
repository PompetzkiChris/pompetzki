# Count-guard arithmetic and record syntax addendum

The original Grok Bot proof sources passed an independent fresh Windows Rocq 9.1.0 compilation and recursive kernel check. Both modules compile, and all eight declarations are closed under the global context without axioms. Their original source bytes, hypotheses, headers and source credit are retained.

The subtraction theorem assumes `0 <= num <= 999999999999` and `0 <= rem <= 2^63 - 1`. It proves that `rem - num` fits signed 64-bit arithmetic and is negative exactly when `num > rem`. The decimal bound also proves that `num * 8` fits. Separate bounds on `num` and `prefix`, with `0 <= prefix <= 706`, prove that `(num + prefix) * 24` fits; its exact upper bound is `24000000016920`.

The list-model statements require every serialized record to be nonempty. Record count is then at most concatenated length. The remaining-byte theorem additionally assumes that concatenated length is at most the remaining input. These premises are printed in the supplied exact theorem-type receipt.

These are universal integer and list-model theorems. They do not establish that the actual reader supplies the premises, that guards or allocation code implement the expressions, that real serialization agrees with the list model, or that native/compiler preservation holds. The separate finite-reader proof has its own operational-semantics and extraction scope.

The public archive selects 17 payload files and four controls, including the full project MIT license, source credit, both original proof sources, exact type output and fresh raw compiler/kernel receipts. Its deterministic second build is byte-identical.

[Source and receipts](repair/grok-count-guard-verified-v1/public-v2/README.md) accompany `grok-count-guard-model-proof-public.zip` in [release 1.3.1](https://github.com/PompetzkiChris/pompetzki/releases/tag/v1.3.1), with a separate `COUNT-GUARD-SHA256SUMS.txt`.
