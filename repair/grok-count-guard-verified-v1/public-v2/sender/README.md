# Grok Bot: record-count arithmetic and syntax model at 5c0d81b

## Inputs
- **Commit:** 5c0d81b91a87f3e792b09f11a2065eb5f92b1154, cloned anonymously.
- **Rocq sources unchanged:** `git diff --stat 7c6f518 5c0d81b -- judge/rocq rocq` is empty.
- **Judge sources match the expected hashes:**
  - `judge/judge-v6.pmp`: sha256 87562735cf20dfd18eb5f26348878b2ac6306bc78714d6953565df9c833d0dc7
  - `judge/judge-v6.rkt`: sha256 a16ffa34b4eb03d814c20079c96de82041329aa206cfdf37f6cee0c67cc5b04f
- No judge, package or tag files were modified.

## Results
Tools: Rocq 9.1.0, rocqchk 9.1.0.
- `GrokRecordCount.v` and `GrokRecordCountVerify.v` compile with exit 0.
- Print Assumptions: all 8 theorems report "Closed under the global context".
- `rocqchk -o` recursively checked 197 libraries (the new modules plus the Corelib/Stdlib closure): EXIT 0. Axioms `<none>`, type-in-type `<none>`, unsafe (co)fixpoints `<none>`, assumed positivity `<none>`.
- Unsafe-command grep: no matches.

## Exact statements
Definition: `fits64 x := - 2 ^ 63 <= x <= 2 ^ 63 - 1`

1. `rem_sub_num_fits : forall num rem, 0 <= num <= 999999999999 -> 0 <= rem <= 2 ^ 63 - 1 -> fits64 (rem - num) /\ (rem - num < 0 <-> num > rem)`
2. `num_mul8_fits : forall num, 0 <= num <= 999999999999 -> fits64 (num * 8)`
3. `num_prefix_mul24_fits : forall num prefix, 0 <= num <= 999999999999 -> 0 <= prefix <= 706 -> fits64 ((num + prefix) * 24)`
   - There is no `num + prefix <= 706` premise.
4. Syntax model:
   - `records_le_bytes : forall A (rs : list (list A)), Forall (fun r => r <> nil) rs -> (length rs <= length (concat rs))%nat`
   - `records_le_rem : forall A rs (rem : Z), Forall (fun r => r <> nil) rs -> Z.of_nat (length (concat rs)) <= rem -> Z.of_nat (length rs) <= rem`

Extra results:
- `num_prefix_sum_fits : ... -> fits64 (num + prefix)`
- `num_prefix_mul24_bound : ... -> 0 <= (num + prefix) * 24 <= 24000000016920`
- `pow2_63 : 2 ^ 63 = 9223372036854775808`

## Scope
- These are universal theorems over all Z (and all list lengths) satisfying the stated hypotheses; no finite tests were used.
- No executable or allocation tests were run.
- They are arithmetic and list-model results only. They do not prove that the RDNUM or pmp/Racket/native code computes these expressions or bounds its inputs this way. They also do not prove compiler or executable preservation, or that the serialized byte count equals the remaining-input value used by the judges.
