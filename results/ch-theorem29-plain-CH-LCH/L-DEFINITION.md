# The class L of lane LCH (obligation O0), frozen 19:10:08 (`date`)

This is one formula with v0 free, over ZB_BASE symbols only, so `Pure.pi` unfolds it to the pure language. It is written by `lch-part-L.rkt.txt` (function `LF` in lch6.rkt). Rocq copies:

- `rocq\LDef.v`: `Ld : dform` literal, `Lsym = tof Ld`.
- `rocq\LRed.v`: `Lpure = pi Lsym`, a literal, with closedk 1 and no symbols. The sentence V = L is `VLpure = All Lpure`.

## Gödel's operations

Jech, Set Theory, (13.7); triples are (u,v,w) = ((u,v),w).

| | operation |
|---|---|
| G1(a,b) | {a,b} (`Upr3`) |
| G2(a,b) | a × b |
| G3(a,b) | {t ∈ a : t = (u,v), u ∈ v} |
| G4(a,b) | a − b |
| G5(a,b) | a ∩ b |
| G6(a) | ⋃a |
| G7(a) | dom a |
| G8(a) | {(u,v) : (v,u) ∈ a} |
| G9(a) | {(u,v,w) : (u,w,v) ∈ a} |
| G10(a) | {(u,v,w) : (v,w,u) ∈ a} |

`Clo(C)` := for all a, b ∈ C and i = 1..10, some z ∈ C equals G_i(a,b). In the formula this is a balanced conjunction.

## The hierarchy

- U_b(s) := ⋃{ s(g) : g ∈ b }, written BM(s,b,z): ∃g (g ∈ b ∧ ∃w (App(s,g,w) ∧ z ∈ w)).
- Step(s,b,v) := ∀X ( X ∈ v ↔ X ⊆ U_b(s) ∧ ∀C ( Clo(C) → U_b(s) ⊆ C → (∃u ∈ C, u = U_b(s)) → X ∈ C ) ). That is, v = cl(U ∪ {U}) ∩ P(U) with U = U_b(s), which is def(U) by Jech 13.8.
- Lev(s) := Fnc(s) ∧ ∃d ( Ord(d) ∧ Tot(s,d) ∧ ∀b ∀v ( App(s,b,v) → b ∈ d ∧ Step(s,b,v) ) ).
- L(x) := ∃s ( Lev(s) ∧ ∃b ∃v ( App(s,b,v) ∧ x ∈ v ) ).

With M_b = s(b), one has M_b = L_{b+1} of the usual hierarchy, so the union of all values is L.

Size 1,170 nodes and depth 82 (de Bruijn `form`), below the pmp interpreter's measured depth bound.
