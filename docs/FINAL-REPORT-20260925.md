# Con(ZFC) → Con(ZFC + notCH*): final report, 2026-09-25

## The conclusion

In Rocq 9.1, namespace `Cohen`, `forcing-src/general`:

    RpFinal.cohen_relative_consistency_closed : prov Gam0 Bot -> prov ZFpure Bot
    RpFinal.con_zfc_con_notch_closed          : ~ prov ZFpure Bot -> ~ prov Gam0 Bot

- `Print Assumptions`: closed under the global context.
- Clean rebuild of 49 files from sources (`build-closed.sh`).
- coqchk `-o Cohen.RpFinal`, 336 s: Axioms: <none>. Nothing relies on type-in-type, on unsafe fixpoints, or on
  assumed positivity.
- Receipt R10.

Definitions:

- `prov A` is a Hilbert calculus for first-order logic with equality. Its rules are K, S, contraposition, modus
  ponens, generalization, instantiation, vacuous quantification, distribution, reflexivity and Leibniz's law, over the
  axiom set A. Open formulas stand for their universal closures.
- `ZFpure` is ZFC in the pure language (E and =):
  - Ext, Pair, Union, Power, Inf, Found and Choice, as the kernel's table in lib/zfc.pmp states them;
  - every instance of Separation and of Collection, in the kernel's forms, over pure formulas.
- `Gam0` is the input theory:
  - the same seven axioms;
  - every instance of Separation and of Collection, with any symbols;
  - the 23 definitions of lib/zfcbase.pmp ZB_BASE;
  - notCH* = `X w X x X y K K K K Om1 w A u I E u x Sub2 u w A u I E u y Sub2 u w N Le2 x w N Le2 y x`.
- `Bot` = `N A x = x x`.

The statement covers every derivation from Gam0.

## How it is proved

1. **General correctness** (receipt R7). Pure.v purifies an input formula: each ZB_BASE symbol is unfolded down to
   the pure language, and every other symbol becomes `A x = x x`. Inv2.v and Sub3.v show that the value of every
   pure formula satisfies the invariants. Claim.v is an induction on derivations: every formula that Gam0 derives
   has value pp at every coherent pp. Each axiom and each rule is one interface template, instantiated by uniform
   substitution. Notch.v handles TNotchT through a certificate over the 127 Vw/Vz definitions, with a checker proved
   sound; the value formula is exponential and is never built. Elim.v eliminates the 670 definitions (last first),
   then the remaining symbols. Final.v concludes, with the premises KERNEL, TNOTCH and COHEX.
2. **The premises in the kernel.**
   - KERNEL: tpl1, 1066 theorems, nbad 0 (R8).
   - TNOTCH: TNotchT in tvn2b (R5), and again in the chapter (R9).
   - COHEX: CohEx in fn8 (R3), and again in the chapter (R9).
3. **The premises in Rocq** (receipt R10). The same derivations are checked again by a checker proved sound:
   - Replay.v: renaming is admissible in every axiom set; the derived rules.
   - ReplayT.v: tautologies by Shannon expansion.
   - Replay2.v and Replay3.v: the step language of the kernel's rules, the checker, and its soundness.
   - mkreplay.pl transcribes 4551 theorems: zfcbase 24, lambda 47, lhull 253, the chain 3161, tpl1 1066. That is
     the closure of the 46 interface theorems, TNotchT and CohEx. Every rule is re-derived by fcore.pl as it goes.
   - RpC0..10.v check the batches by vm_compute, 2 to 8 s each.
   - RpFinal.v proves KERNEL, TNOTCH and COHEX, and the theorem with no premise.

## What rests on what

- **The proof** rests on the Rocq kernel alone (coqchk).
- **The statement's meaning** uses texts parsed in Rocq:
  - the seven axioms (Checks.v);
  - the ZB_BASE definitions (Data.v);
  - notCH* (Pure.v).
- **Audits.** Data.v's 747 texts equal the kernel's sources and run files byte for byte. The chain's run files
  register only r_all's definitions. The runs' hypotheses are placeholders or theorems of accepted batches.
- **The kernel runs.** They are a second, independent derivation of the finite part. They are not needed by the
  Rocq theorem.

## Receipts (forcing-src/RECEIPTS.md)

| receipt | content |
|---|---|
| R1 | tvo1p1 |
| R2 | tvo1p2 |
| R3 | fn3–fn8 (CohEx) |
| R4 | tvn2a |
| R5 | tvn2b (TNotchT) |
| R6 | tvn3t (NotchV) |
| R7 | the general proof with its premises |
| R8 | tpl1 (the interface): 1066 theorems, nbad 0, 31,929 s |
| R9 | the chapter cohen-relcon: claims 9 of 9, 12,710 s |
| R10 | the closed theorem |

## The native transformer

forcing-src/pmx/tau5.pmx (run px_tvn3-01) reproduced tvn3.src byte for byte (sha256 31fe1b54…). tvo1, tvn2a, tvn2b
and tvn3t are pieces of it.

## Book, packages

{{BOOK}}

FinTNotchF, the harness with the test hypothesis VBot, is a test of the final glue and not a consistency result.
