# Soundness of the pmp Judge (Revision 2 — Post-Reboot Final)

This document specifies the formal mathematical soundness chain of the `pmp` judge. It quotes the exact theorem statements formalized in Rocq, details the definition of theory $\Gamma$ (`Gam`), documents initial registry validity (`REG0_ok`), and explains the exact boundary between mechanized proofs and executable machine bytes.

---

## 1. Deductive Foundation: Hilbert Calculus `prov` and Theory $\Gamma$ (`Gam`)

The target logic is a classical Hilbert calculus for first-order logic with equality over an arbitrary axiom set `Ax : form -> Prop` (`Prov.v:11-22`). The deduction relation `prov Ax f` is defined by:
- Axiom rule: `p_ax f : Ax f -> prov Ax f`
- Propositional Hilbert axioms: `p_k`, `p_s`, `p_c`
- Modus ponens: `p_mp a b : prov Ax a -> prov Ax (Imp a b) -> prov Ax b`
- Quantification rules: `p_gen`, `p_inst`, `p_vac`, `p_dist`
- Equality axioms: `p_refl`, `p_leib`

### 1.1 Definition of the Base Theory $\Gamma$ (`Gam`, `Ax.v:90`)
```coq
Definition Gam (f : form) : Prop := ZFC7 f \/ SepAx f \/ CollAx f \/ DefAx Dall f.
```
(`Ax.v:90`).

$\Gamma$ consists of four disjoint classes:
1. **The Seven ZFC Base Axioms (`ZFC7`, `Ax.v:85`):**
   ```coq
   Definition ZFC7 (f : form) : Prop := exists i, i < 7 /\ f = axf i.
   ```
   Closed universal closures of: Empty Set, Extensionality, Pairing, Union, Power Set, Infinity, and Choice (`Checks.v:52`). Verified closed (`axioms_closed_ok`, `Ax.v:97`) and pure of uninterpreted symbols (`axioms_pure_ok`, `Ax.v:98`).
2. **Separation Axiom Schema (`SepAx`, `Ax.v:86`):**
   ```coq
   Definition SepAx (f : form) : Prop := exists g, f = SepF g.
   ```
   For all formulas $g$: $\text{SepF}(g) = \forall. \exists. \forall. ((0 \in 1) \leftrightarrow ((0 \in 2) \land \text{ren skip1 } g))$ (`Checks.v:27`).
3. **Collection Axiom Schema (`CollAx`, `Ax.v:87`):**
   ```coq
   Definition CollAx (f : form) : Prop := exists g, f = CollF g.
   ```
   For all formulas $g$: $\text{CollF}(g) = \forall. [(\forall.(0 \in 1 \to \exists g)) \to \exists. \forall.(0 \in 2 \to \exists. (0 \in 2 \land \text{ren ins2 } g))]$ (`Checks.v:28-29`).
4. **Registered Definitions (`DefAx Dall`, `Ax.v:88`):**
   ```coq
   Definition DefAx (D : list (nat * nat * form)) (f : form) : Prop :=
     exists d s, In d D /\ f = ren s (defax d).
   ```
   Where `Dall` contains all 670 definitions of `lib/zfcbase.pmp` (`all_defs_parse_ok`, `Ax.v:96`), closed under arbitrary renamings $s$.

$\Gamma$ is closed under renaming: `Gam_ren` (`Ax.v:112`) and `prov_Gam_ren` (`Ax.v:121`). Furthermore, Lane CX3 established in Rocq that $\Gamma$ is conservative over pure ZF:
$$\text{syms } f = [] \to \text{prov Gam } f \to \text{prov ZFpure } f$$
(`lanes/CX3/`, `coqchk Axioms: <none>`).

---

## 2. Initial Registry Soundness: `REG0_ok`

The initial registry `REG0` (`RpInitOk.v:13-15`) contains:
- `AX0`: The 7 axioms of ZFC (`len_AX0 : length AX0 = 7`, `RpInitOk.v:28`), verified by `ax_check_x` (`RpInitOk.v:24-25`).
- `DEF0`: The 670 closed definitions (`len_DEF0 : length DEF0 = length Dall`, `RpInitOk.v:29`), verified by `def_check_x` (`RpInitOk.v:26-27`).
- `HYPD`: The 29 placeholder hypotheses ($0 \le i < 29$).
- Total: 706 entries.

### 2.1 Theorem `REG0_ok` (`RpInitOk.v:64`)
```coq
Theorem REG0_ok : reg_ok hypf REG0.
```
**Exact Theorem Statement:**
`Theorem REG0_ok : reg_ok hypf REG0.` (`RpInitOk.v:64`).

**Proof Architecture (`RpInitOk.v:65-85`):**
1. Entries $0 \le i < 7$ are verified against `axf` by `ax_check_x` and proven via `p_ax (ZFC7 ...)`.
2. Entries $7 \le i < 677$ are verified against `closed_def` by `def_check_x` and proven via `closed_def_prov` from `DefAx Dall`.
3. Entries $677 \le i < 706$ are proven via `p_ax` directly from the hypothesis extension $\text{AH } [i - 677]$.

### 2.2 Canonical Registry Slices
- **`PREFIX-677`:** The first 677 entries of `REG0` (`AX0 ++ DEF0`, with $h = []$). Because `nth_error` on an initial slice agrees with `REG0`, `PREFIX-677` unconditionally satisfies `reg_ok` with empty hypotheses.
- **`REG0-706`:** The full 706-entry registry, pinned by SHA-256 `a202ed994929c8484f053219047d854729af4a3d97ad8f804bb3cdef3b4a52ae`.

---

## 3. Soundness of Verification: `check_thm_ok` and `check_batch_ok`

The core soundness theorems are formalized in `Replay3.v:1-143` with zero admitted axioms (`coqchk Axioms: <none>`):

### 3.1 Theorem `check_thm_ok` (`Replay3.v:111`)
```coq
Theorem check_thm_ok reg t :
  reg_ok reg ->
  check_thm reg t = true ->
  prov (AH (t_hyps t)) (tof (t_stmt t)).
```
**Exact Theorem Statement:**
`Theorem check_thm_ok reg t : reg_ok reg -> check_thm reg t = true -> prov (AH (t_hyps t)) (tof (t_stmt t)).` (`Replay3.v:111`).

**Semantic Guarantee:**
If the registry `reg` is sound (`reg_ok reg`), and `check_thm reg t` returns `true`, then the statement $\text{tof}(t\_stmt(t))$ is formally provable in Hilbert calculus `prov` from theory $\Gamma$ augmented by the theorem's declared hypotheses $t\_hyps(t)$.
For pure theorems ($t\_hyps = []$), this establishes:
$$\text{prov } \Gamma\ (\text{tof }(t\_stmt\ t))$$

### 3.2 Theorem `check_batch_ok` (`Replay3.v:130`)
```coq
Theorem check_batch_ok reg ts :
  reg_ok reg ->
  check_batch reg ts = true ->
  reg_ok (reg ++ map ent ts).
```
**Exact Theorem Statement:**
`Theorem check_batch_ok reg ts : reg_ok reg -> check_batch reg ts = true -> reg_ok (reg ++ map ent ts).` (`Replay3.v:130`).

**Semantic Guarantee:**
Starting from a sound registry (`REG0_ok`), verifying a batch of theorems $ts$ with `check_batch` guarantees that appending the accepted theorems preserves registry validity. Every accepted theorem is soundly established.

---

## 4. What Remains Owed: The Implementation Gap

While the Rocq formalization establishes that the functional specification `check_batch` soundly implies `prov Gam`, there remains an open engineering gap between the Rocq Gallina equations and executable binaries:

> **What is still owed:** A formal proof that the machine instructions and bytes of `judge-v3.pmp` (executed by `pompetzki.exe` / `pompetzki`) and the native Linux ELF `jdgchk` compute the Gallina function `check_batch`.

### 4.1 Status of the Compilation Stages
- **Stage 1 (pmp execution semantics):** `judge-v3.pmp` is an imperative verifier in PmpCore. Proving equivalence between `PmpCore.v` operational execution and Gallina `check_batch` remains an open target.
- **Stage 4 (Native ELF verification):** Lane L4 has produced a native Linux x86-64 ELF binary (`jdgchk`, SHA-256 `4d153bea472d8a540cdef00cf9513e47d5f86ff382b428f81058f949113365d9`). The formal simulation proof relating x86-64 instruction semantics in Rocq to `check_batch` is in progress.
- **Current Status:** All ten stages remain **OPEN** in the project's formal validation matrix. No unsupported full completion claims are made.

### 4.2 Empirical Safeguards Enforced Tonight
1. **Independent Dual Judges:** Every derivation must be accepted with identical counts by both `pompetzki.exe judge-v3.pmp` and `racket judge.rkt` (`RELEASE-DAY-ORDERS-2026-10-09.md` Rule 4).
2. **Mutant Rejection:** Systematic negative test suites (e.g. 70 mutants across 7 files in Stage 2, 10 mutants in Stage 6, 42 mutants in Stage 7) reject 100% on both judges at identical theorems and steps.
3. **Canonical Registry Gating:** Proof transcripts must match pinned canonical registry hashes before entry into the posting ledger.

---

## 5. Exact Interpreter Resource Bounds

The pmp interpreter enforces explicit memory and recursion constraints (`lanes/FINDINGS-pmp-interpreter-bounds-20261009.md`):

1. **Recursion Call Depth Limit:**
   - Message: `line 386: gosub: too deep`
   - Occurs when formulas nest numerals above $n = 38$ (e.g. numerals 41–50 in Stage 2 big waves).
2. **Memory Block Allocation Limit:**
   - Message: `LIMIT a memory block is full` (followed by `line 348: check zero failed`)
   - Occurs when the cumulative final registry size exceeds **1,091 entries** (tested: layer 8 with 1,091 accepted; layer 13 with 1,269 stopped).

**Soundness Clarification:**
On files that exceed these bounds, the reference judge `judge.rkt` accepts the derivations as mathematically sound (`ACCEPT`, exit 0). An interpreter resource stop is an execution constraint of the current runtime, not a rule rejection or a logical contradiction.

---

## 6. Corrected Mathlib-versus-Init Attribution (Lane L6)

In Lane L6 (`lanes/L6/out/L6-nat.jdg`, 345 theorems, 37,714 steps; both judges ACCEPT, exit 0), 252 theorems from the environment of `import Mathlib` are proved as closed ZF theorems over $\omega$ under their exact Lean names.

Their canonical provenance is:
- **243 theorems (96.4%) originate in Lean 4's core library (`Init`):**
  - `Init.Data.Nat.Basic`: 156
  - `Init.Data.Nat.Lemmas`: 51
  - `Init.Prelude`: 25
  - `Init.Grind.Offset`: 5
  - `Init.Omega.Int`: 2
  - `Init.Data.Nat.Mod`: 2
  - `Init.Core`: 2
- **9 theorems (3.6%) originate in `Mathlib` proper:**
  - `Mathlib.Data.Nat.Init`: 5 (`LT.lt.nat_succ_le`, `Nat.succ_pos'`, `Nat.of_le_succ`, `Nat.two_le_iff`, `Nat.two_lt_of_ne`)
  - `Mathlib.Data.Nat.SuccPred`: 1 (`Nat.le_succ_iff_eq_or_le`)
  - `Mathlib.Tactic.Ring.Common`: 2 (`Mathlib.Tactic.Ring.add_pos_left`, `Mathlib.Tactic.Ring.add_pos_right`)
  - `Mathlib.NumberTheory.PellMatiyasevic`: 1 (`Pell.asq_pos`)

This precise attribution correctly reflects that Mathlib relies on Lean's `Init` prelude for its core $\mathbb{N}$ foundation.

---

## 7. Licensing Scope and Retained Third-Party Notices

1. **Original Pompetzki Code and Documentation:**
   - Released under the **MIT License**, Copyright (c) 2026 Christopher Pompetzki.
   - Pinned SHA-256: `65084df2bd72a7c943559f2c6984868804e01d102231ddcd6cc848de54258827`.
   - Approved in `docs/license/LICENSE-APPROVAL.json`.
2. **Retained Third-Party Licenses (Not Relicensed):**
   - **Metamath `set.mm` Derived Material:** Creative Commons Zero v1.0 Universal (`licenses/CC0-1.0.txt`).
   - **Lean 4 / Mathlib Derived Statements:** Apache License 2.0 (`licenses/Apache-2.0.txt`).
   - The release does not relicense third-party mathematical statements or source derivations.
