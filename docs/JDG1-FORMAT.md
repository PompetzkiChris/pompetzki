# JDG1 Format Specification (Revision 2 — Post-Reboot Final)

This document is the authoritative reference specification of the **JDG1** format: the concrete proof exchange format checked by the `pmp` judge (`judge-v3.pmp`), the native Linux binary (`jdgchk`), and the reference Racket judge (`judge/racket/judge.rkt`).

Revision 2 updates the original specification with canonical registry provenance (`PREFIX-677` vs `REG0-706`), explicit interpreter resource bounds, cross-platform execution definitions, and cross-checks against the post-reboot release package.

---

## 1. Lexical Grammar and Stream Grammar

A JDG1 document is a stream of ASCII whitespace-separated tokens (`judge.rkt:399-405`):
- **Whitespace:** Space (32), newline (10), carriage return (13), and horizontal tab (9) (`judge.rkt:399`). All whitespace between tokens is insignificant.
- **Numbers:** Non-negative integers written in decimal ASCII digits `0`–`9` (`judge.rkt:407-410`). No floating-point or negative representations exist.
- **Lists:** Serialized as `<count> <elem_0> ... <elem_{count-1}>` (`judge.rkt:415`, `rocq2jdg.rkt:7, 105`). An empty list is serialized simply as `0`.
- **Top-Level Stream:**
  ```text
  JDG1
  R <nreg>
  <entry_0>
  ...
  <entry_{nreg-1}>
  T <nthm>
  <thm_0>
  ...
  <thm_{nthm-1}>
  ```
  (`judge.rkt:8-14, 462-488`, `rocq2jdg.rkt:5-12, 138-145`, `judge-v3.pmp:30-36`).
  
  The file begins with the ASCII magic header `JDG1`, followed by the initial registry declaration `R <nreg>`, the $nreg$ registry entries, the theorem block declaration `T <nthm>`, and the $nthm$ theorems. No trailing non-whitespace input is permitted after the last theorem (`judge.rkt:485`).

---

## 2. Canonical Registry Provenance and Gating

The registry is the accumulator of established mathematical facts. Every theorem verified in a JDG1 file is appended to the registry and made available for subsequent theorems to cite (`Replay2.v:168-170`, `judge.rkt:477`).

The release enforces strict canonical registry provenance via `tools/registry-gate/registry-gate.rkt`:

### 2.1 The Two Canonical Registry Shapes
1. **`PREFIX-677` (The Pure Base Theory):**
   - Contains exactly 677 entries: the 7 axioms of ZFC (`AX0`, `len_AX0`, `RpInitOk.v:28`) followed by the 670 closed definitions of the standard library (`DEF0`, `len_DEF0`, `RpInitOk.v:29`).
   - Every entry carries an empty hypothesis list (`0`).
   - Every theorem verified against `PREFIX-677` claiming hypothesis list `0` is an unconditional theorem of $\text{ZFC}$ (`prov Gam`, `Ax.v:90`, `Replay3.v:111`).
   - Used by all pure mathematics derivations: `sigma1/out/*.jdg` (7 files, 1,656 theorems), `lanes/L6/out/L6-nat.jdg` (345 theorems), and `lanes/L7/out/*.jdg` (6 files).
2. **`REG0-706` (The Replay Registry with Forcing Placeholders):**
   - Contains all 706 entries: `AX0` (7) ++ `DEF0` (670) ++ `HYPD` (29 placeholder hypotheses, indexed $0 \le i < 29$) (`RpInitOk.v:13-15`).
   - Used for the full Theorem 29 Cohen forcing replay (`judge/replay-all.jdg`).
   - Pinned SHA-256: `a202ed994929c8484f053219047d854729af4a3d97ad8f804bb3cdef3b4a52ae`.
   - Distinct posting classes: 4,373 unconditional theorems (relying on no hypotheses) and 178 conditional theorems (relying on non-empty forcing hypotheses) (`POSTING-GATE.md`).

Any derivation attempting to use an unauthenticated or non-canonical initial registry is rejected at the registry gate.

---

## 3. Formula Syntax (`dform` and `form`)

The logical foundation is first-order set theory with de Bruijn variable indexing (`Syn.v:1-13`). Data formulas (`dform`, `Replay2.v:11-14`) represent formulas in serializable form. The function `tof : dform -> form` (`Replay2.v:16-28`, `judge.rkt:226-237`) expands abbreviations into core formulas (`form`, `Syn.v:7-13`).

### 3.1 Primitive Formula Constructors

| JDG1 Syntax | Rocq Constructor (`Syn.v:7-13`, `Replay2.v:11-14`) | Expanded `form` (`Syn.v:7-13`, `Replay2.v:16-28`) | Description | Reference Judge (`judge.rkt:417-430`) |
| :--- | :--- | :--- | :--- | :--- |
| `e <x> <y>` | `dE (x y : N)` | `Mem (to_nat x) (to_nat y)` | Set membership $x \in y$ | `[(#\e) (vector 'e (num!) (num!))]` |
| `q <x> <y>` | `dEq (x y : N)` | `Eqv (to_nat x) (to_nat y)` | Variable equality $x = y$ | `[(#\q) (vector 'q (num!) (num!))]` |
| `p <P> <LIST>` | `dP (p : N) (a : list N)` | `Pr (to_nat p) (map to_nat a)` | Predicate symbol $P$ with argument vector $a$ | `[(#\p) (vector 'p (num!) (list!))]` |
| `n <F>` | `dN (a : dform)` | `Neg (tof a)` | Negation $\neg a$ | `[(#\n) (vector 'n (form!))]` |
| `i <F> <G>` | `dI (a b : dform)` | `Imp (tof a) (tof b)` | Implication $a \to b$ | `[(#\i) (vector 'i (form!) (form!))]` |
| `a <F>` | `dA (a : dform)` | `All (tof a)` | Universal quantifier $\forall. a$ | `[(#\a) (vector 'a (form!))]` |

### 3.2 Kernel Macro Abbreviations (`Syn.v:28-33`, `Replay2.v:14, 24-27`, `judge.rkt:56-59, 234-237`)

1. `k <F> <G>` (`dK a b`): Conjunction $a \land b \equiv \neg (a \to \neg b)$ (`Kf a b`, `Syn.v:30`).
2. `d <F> <G>` (`dD a b`): Disjunction $a \lor b \equiv \neg a \to b$ (`Df a b`, `Syn.v:31`).
3. `b <F> <G>` (`dQ a b`): Equivalence $a \leftrightarrow b \equiv (a \to b) \land (b \to a)$ (`Qf a b`, `Syn.v:32`). *Tag is ASCII `b` (`judge.rkt:429`, `rocq2jdg.rkt:70, 111`).*
4. `x <F>` (`dX a`): Existential quantification $\exists. a \equiv \neg \forall \neg a$ (`Xf a`, `Syn.v:33`).

---

## 4. Binding Primitives and Renamings

- **Renaming `ren s f`:** Maps free variables according to $s : \mathbb{N} \to \mathbb{N}$ (`Syn.v:18-26`, `judge.rkt:65-82`).
- **Identity Renaming `sid`:** $n \mapsto n$ (`Prov.v:9`, `judge.rkt:84`).
- **Single-Variable Extension `scons y s`:** $0 \mapsto y$ and $(n+1) \mapsto s(n)$ (`Syn.v:148-149`, `judge.rkt:85`).
- **Successor Renaming `S` (`succ`):** $n \mapsto n+1$ (`Prov.v:19`, `judge.rkt:87`).
- **Abstraction Mapping `absk k`:** Abstracting free variable $k$ into binder index 0:
  $$\text{absk}(k)(j) = \begin{cases} 0 & \text{if } j = k \\ j + 1 & \text{if } j \ne k \end{cases}$$
  (`Replay.v:40`, `judge.rkt:86`).
- **Separation Shift `skip1`:** $0 \mapsto 0$, and $(m+1) \mapsto m+2$ (`Checks.v:25`, `judge.rkt:88`).
- **Collection Shift `ins2`:** $0 \mapsto 0$, $1 \mapsto 1$, and $(m+2) \mapsto m+3$ (`Checks.v:26`, `judge.rkt:89`).
- **Unskip Mapping `unskip`:** $0 \mapsto 0$, $1 \mapsto 0$, and $(m+2) \mapsto m+1$ (`Replay2.v:47`, `judge.rkt:90`).
- **Free Variable Predicate `free n f`:** Returns `true` iff variable index $n$ occurs free in $f$ (`Syn.v:138-145`, `judge.rkt:93-110`).
- **Bounded Closeness `closedk k f`:** Returns `true` iff every free variable in $f$ is strictly less than $k$ (`Ax.v:22-29`, `judge.rkt:113-125`).
- **Structural Equality `form_eqb f g`:** Decidable syntactic equality on formulas (`Syn.v:161-170`, `judge.rkt:61-62`).

---

## 5. Specification of Every Step Letter (U, S, G, M, T, E, L, H, V, Z, Y)

The judge supports exactly 11 step types (`Replay2.v:30-41`, `judge.rkt:11-12, 303-358`, `rocq2jdg.rkt:10-11, 73-89`):

### `U` — Registry Use (`SUse`)
- **Syntax:** `U <r> <LIST(sig)>` (`rocq2jdg.rkt:78, 114`, `judge.rkt:304-309`).
- **Rocq Definition:** `SUse (r : N) (sig : list N)` (`Replay2.v:31, 96`).
- **Semantics & Side Conditions:** Lookup registry entry $r$: `nthN reg r = Some (d, h)`. Derived formula: $\text{ren }(\text{sigf}(\sigma))\ (\text{tof } d)$, where $\text{sigf}(\sigma)(i) = \text{nth } i\ (\text{map to\_nat }\sigma)\ 0$ (`Replay2.v:80`). Contributed hypotheses: $h$.
- **Fails if:** $r \ge \text{length}(reg)$.

### `S` — Multi-Quantifier Specialization (`SSpec`)
- **Syntax:** `S <l> <LIST(ts)>` (`rocq2jdg.rkt:79, 114`, `judge.rkt:310-311`).
- **Rocq Definition:** `SSpec (l : N) (ts : list N)` (`Replay2.v:32, 97`).
- **Semantics & Side Conditions:** Lookup line $l$: `nthN lines l = Some F`. Applies recursive specialization `specn F ts` (`Replay2.v:82-86`, `judge.rkt:296-299`), instantiating variable 0 under each universal quantifier. Contributed hypotheses: `[]`.
- **Fails if:** Line $l$ does not exist or has fewer than $\text{length}(ts)$ universal quantifiers.

### `G` — Universal Generalization (`SGen`)
- **Syntax:** `G <l> <k>` (`rocq2jdg.rkt:80, 115`, `judge.rkt:312-313`).
- **Rocq Definition:** `SGen (l : N) (k : N)` (`Replay2.v:33, 98`).
- **Semantics & Side Conditions:** Lookup line $l$: `nthN lines l = Some F`. Derived formula: $\text{All } (\text{ren } (\text{absk } k)\ F)$. Contributed hypotheses: `[]`.
- **Fails if:** Line $l$ does not exist.

### `M` — Modus Ponens (`SMp`)
- **Syntax:** `M <i> <j>` (`rocq2jdg.rkt:81, 115`, `judge.rkt:314-316`).
- **Rocq Definition:** `SMp (i j : N)` (`Replay2.v:34, 99-103`).
- **Semantics & Side Conditions:** Lookup line $i$ ($a$) and line $j$ ($a' \to b$). Requires `form_eqb a a' = true`. Derived formula: $b$. Contributed hypotheses: `[]`.
- **Fails if:** Lines missing, line $j$ is not an implication, or antecedent does not match line $i$.

### `T` — Propositional Tautology (`STaut`)
- **Syntax:** `T <LIST(prems)> <FORM>` (`rocq2jdg.rkt:82, 116`, `judge.rkt:317-321`).
- **Rocq Definition:** `STaut (ls : list N) (g : dform)` (`Replay2.v:35, 104-106`).
- **Semantics & Side Conditions:** Resolve premises `ps = prems lines ls`. Form $\Phi = \text{fold\_right Imp } (\text{tof } g)\ ps$. Evaluates propositional tautology decider `tautchk2 `$\Phi$ ` = true` (`ReplayT.v:100-106`, `judge.rkt:220-223`). Derived formula: $\text{tof } g$. Contributed hypotheses: `[]`.
- **Fails if:** Premise missing or formula is not a propositional tautology.

### `E` — Existential Introduction (`SExi`)
- **Syntax:** `E <t> <FORM>` (`rocq2jdg.rkt:83, 117`, `judge.rkt:322-327`).
- **Rocq Definition:** `SExi (t : N) (g : dform)` (`Replay2.v:36, 107-112`).
- **Semantics & Side Conditions:** Let $G = \text{tof } g$. Shape: $G = F \to \neg \forall \neg f \equiv F \to \exists f$. Requires `form_eqb F (ren (scons t sid) f) = true`. Derived formula: $G$. Contributed hypotheses: `[]`.
- **Fails if:** Shape mismatch or $F \ne f[t/0]$.

### `L` — Existential Elimination (`SExel`)
- **Syntax:** `L <l> <k> <FORM>` (`rocq2jdg.rkt:84, 118`, `judge.rkt:328-336`).
- **Rocq Definition:** `SExel (l k : N) (g : dform)` (`Replay2.v:37, 113-120`).
- **Semantics & Side Conditions:** Let $G = \text{tof } g$, and lookup line $l$: $P \to G_3$. Goal shape: $(\exists P') \to G_2$. Requires: `form_eqb G2 G3 = true`, `form_eqb P' (ren (absk k) P) = true`, and `negb (free k G2) = true`. Derived formula: $G$. Contributed hypotheses: `[]`.
- **Fails if:** Line $l$ is not an implication, shapes mismatch, $P' \ne P[0/k]$, or variable $k$ is free in $G_2$.

### `H` — Universal Introduction into Consequent (`SAlli`)
- **Syntax:** `H <k> <l> <FORM>` (`rocq2jdg.rkt:85, 118`, `judge.rkt:337-344`).
- **Rocq Definition:** `SAlli (k l : N) (g : dform)` (`Replay2.v:38, 121-128`).
- **Semantics & Side Conditions:** Variable $k$ precedes line $l$. Lookup line $l$: $H_2 \to f$. Goal shape: $H \to \forall f'$. Requires: `form_eqb H H2 = true`, `form_eqb f' (ren (absk k) f) = true`, and `negb (free k H) = true`. Derived formula: $G$. Contributed hypotheses: `[]`.
- **Fails if:** Shapes mismatch, $f' \ne f[0/k]$, or $k$ occurs free in antecedent $H$.

### `V` — Universal Instantiation (`SInst`)
- **Syntax:** `V <t> <FORM>` (`rocq2jdg.rkt:86, 117`, `judge.rkt:345-350`).
- **Rocq Definition:** `SInst (t : N) (g : dform)` (`Replay2.v:39, 129-134`).
- **Semantics & Side Conditions:** Let $G = \text{tof } g$. Shape: $(\forall f) \to G_2$. Requires: `form_eqb G2 (ren (scons t sid) f) = true`. Derived formula: $G$. Contributed hypotheses: `[]`.
- **Fails if:** Shape mismatch or $G_2 \ne f[t/0]$.

### `Z` — Leibniz Equality Substitution (`SLeib`)
- **Syntax:** `Z <FORM(a)> <FORM(g)>` (`rocq2jdg.rkt:87, 119`, `judge.rkt:351-356`).
- **Rocq Definition:** `SLeib (a : dform) (g : dform)` (`Replay2.v:40, 135-141`).
- **Semantics & Side Conditions:** Template $A = \text{tof } a$. Goal $G = (s = t) \to (X \to Y)$. Requires: `form_eqb X (ren (scons s sid) A) = true` and `form_eqb Y (ren (scons t sid) A) = true`. Derived formula: $G$. Contributed hypotheses: `[]`.
- **Fails if:** Shape mismatch, $X \ne A[s/0]$, or $Y \ne A[t/0]$.

### `Y` — Axiom Instance (`SAx`)
- **Syntax:** `Y <FORM>` (`rocq2jdg.rkt:88, 120`, `judge.rkt:357-358`).
- **Rocq Definition:** `SAx (g : dform)` (`Replay2.v:41, 142`).
- **Semantics & Side Conditions:** Let $G = \text{tof } g$. Requires `axshape G = true` (`Replay2.v:59-76`, `judge.rkt:271-291`). Derived formula: $G$. Contributed hypotheses: `[]`.
- **Recognized Shapes in `axshape`:**
  1. $K$: $a \to (b \to a)$.
  2. $S$: $(a \to (b \to c)) \to ((a \to b) \to (a \to c))$.
  3. $C$ (contraposition): $(\neg a \to \neg b) \to (b \to a)$.
  4. $\text{Dist}$ (distribution): $(\forall.(a \to b)) \to ((\forall.a) \to (\forall.b))$.
  5. $\text{Vac}$ (vacuous quantification): $a \to \forall.(\text{ren } S\ a)$.
  6. $\text{Refl}$ (equality reflexivity): $x = x$.
  7. $\text{Sep}$ (`isSepN`): Any universal prefix over canonical Separation $\text{SepF}(F)$.
  8. $\text{Coll}$ (`isCollN`): Any universal prefix over canonical Collection $\text{CollF}(F)$.

---

## 6. Verification and Five Conditions of `check_thm`

For theorem $t = (S, \sigma, steps, hyps)$, proof steps run sequentially via `run` (`Replay2.v:145-149`), producing resulting lines and accumulated hypotheses $(lines, hs)$.

`check_thm` accepts iff all five conditions hold (`Replay2.v:155-164`, `judge.rkt:381-392`):
1. **Non-Empty Proof:** $\text{length}(lines) \ge 1$.
2. **Statement Conformance:** $\text{last } lines = \text{ren }(\text{sigf}(\sigma))\ (\text{tof } S)$.
3. **No Duplicate Frame Variables:** $\text{nodupb } \sigma = \text{true}$.
4. **Statement Bounded Scope:** $\text{closedk } (\text{length }\sigma)\ (\text{tof } S) = \text{true}$.
5. **Hypothesis Soundness:** $\text{subsetb } hs\ hyps = \text{true}$.

When accepted, the theorem entry $(S, hyps)$ is appended to the registry (`check_batch`, `Replay2.v:168-170`, `judge.rkt:477`).

---

## 7. Exact Interpreter Resource Bounds

The pmp interpreter (`pompetzki.exe` on Windows, `pompetzki` on Linux) enforces explicit execution bounds (`lanes/FINDINGS-pmp-interpreter-bounds-20261009.md`):

1. **Recursion Call Depth Limit:**
   - Message: `line 386: gosub: too deep`
   - Occurs when formulas nest numerals above $n = 38$ (e.g. numerals 41–50 in Stage 2 big waves).
2. **Memory Block Allocation Limit:**
   - Message: `LIMIT a memory block is full` followed by `line 348: check zero failed`
   - Occurs when the cumulative final registry size exceeds **1,091 entries** (tested: layer 8 with 1,091 accepted; layer 13 with 1,269 stopped).

**Critical Distinction:**
A stop caused by a resource bound is **NOT** a proof rejection. On all files triggering these bounds, the reference judge `judge.rkt` accepts the derivations as mathematically sound (`ACCEPT`, exit 0). The compiled judge (`pmpc`) and native ELF binary (`jdgchk`) eliminate these fixed interpreter bounds.
