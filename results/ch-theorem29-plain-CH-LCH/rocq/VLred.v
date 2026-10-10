(* VLred.v - the obligation LCH split in two: the axiom V = L relativized to the class, and a derivation of CH from
   pure ZFC + V = L. VL is any closed sentence (the intended one: every set is constructible, written with the same
   defining formula as the class). Rel2.rel_closed relativizes the derivation of CH: its ZFC axioms by LAX, LSEP, LCOLL,
   its axiom VL by the premise VLrel.
     lch_from_vl      : LEX, LAX, LSEP, LCOLL, ZFpure |- rel M VL, ZFpure + VL |- pi ch  ->  LCH
     goedel_from_vl   : the same premises  ->  GamCH |- Bot -> ZFpure |- Bot
     goedel_final_red : for a pure class formula Mf: LEX, the six plain properties HT i (LAXred2.v), Choice
                        relativized, LSEP, LCOLL, ZFpure |- rel Mf VL, ZFpure + VL |- pi ch  ->  GamCH |- Bot -> ZFpure |- Bot
   Lane LCH, 2026-10-09. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Use Expand Pure Elim.
From LCH Require Import Rel2 GoedelCH LAXred2.
Import ListNotations.
Open Scope nat_scope.

Section VL.
Variable M : form.
Hypothesis HM : closedk 1 M = true.
Variable VL : form.
Hypothesis HV : closedk 0 VL = true.

Theorem lch_from_vl : LEX M -> LAX M -> LSEP M -> LCOLL M ->
  prov ZFpure (rel M VL) -> prov (ZFE VL) (pi ch) -> LCH M.
Proof.
  intros Hex Hax Hsep Hcoll Hv D. unfold LCH.
  refine (rel_closed M HM (ZFE VL) ZFpure (ZFE_ren VL HV) _ Hex (pi ch) D pi_ch_closed).
  intros f [[[[i [Hi ->]]|[[g ->]|[g ->]]] Hp]| ->] n Hn Hc.
  - apply chain_k. exact (Hax i Hi).
  - exact (Hsep g (syms_SepF g Hp) n Hn Hc).
  - exact (Hcoll g (syms_CollF g Hp) n Hn Hc).
  - apply chain_k. exact Hv.
Qed.

Theorem goedel_from_vl : LEX M -> LAX M -> LSEP M -> LCOLL M ->
  prov ZFpure (rel M VL) -> prov (ZFE VL) (pi ch) -> prov GamCH Bot -> prov ZFpure Bot.
Proof.
  intros Hex Hax Hsep Hcoll Hv D.
  exact (goedel_relative_consistency M HM Hex Hax Hsep Hcoll (lch_from_vl Hex Hax Hsep Hcoll Hv D)).
Qed.
End VL.

Section Final.
Variable Mf : form.
Hypothesis HM : closedk 1 Mf = true.
Hypothesis Hp : syms Mf = [].
Variable VL : form.
Hypothesis HV : closedk 0 VL = true.

Theorem goedel_final_red : LEX Mf ->
  (forall i, i < 6 -> prov ZFpure (psub (tauM Mf) sid (HT i))) ->
  prov ZFpure (rel Mf (axf 6)) ->
  LSEP Mf -> LCOLL Mf ->
  prov ZFpure (rel Mf VL) -> prov (ZFE VL) (pi ch) ->
  prov GamCH Bot -> prov ZFpure Bot.
Proof.
  intros Hex H6 Hc Hsep Hcoll Hv D.
  assert (Hax : LAX Mf).
  { intros i Hi. destruct (Nat.lt_ge_cases i 6) as [L|L]; [exact (lax_reduced Mf HM Hp i L (H6 i L))|].
    assert (i = 6) by lia. subst i. exact Hc. }
  exact (goedel_from_vl Mf HM VL HV Hex Hax Hsep Hcoll Hv D).
Qed.
End Final.
