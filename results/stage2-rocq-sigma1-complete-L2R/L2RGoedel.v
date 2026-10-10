(* L2RGoedel.v - lane L2R round 2, 2026-10-09. LCH's VLred.goedel_final_red with its premises LSEP Mf (O8) and
   LCOLL Mf (O9) replaced by L2RRefl's hypotheses about a hierarchy of levels Lev for Mf: the single statements STR,
   SSUB, SIN, SCOV, the reflection schema GREFL and the definability schema DEFsep. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith String.
From Cohen Require Import Syn Prov Kal Ax Checks Replay Expand Pure Elim.
From LCH Require Import Rel2 GoedelCH LAXred2 VLred.
From L2R Require Import L2RLogicA L2RSepL L2RRefl.
Import ListNotations.
Open Scope nat_scope.

Theorem goedel_final_red_levels (Mf : form) (HM : closedk 1 Mf = true) (Hp : syms Mf = [])
  (Lev : form) (HL : closedk 1 Lev = true) (VL : form) (HV : closedk 0 VL = true) :
  LEX Mf ->
  (forall i, i < 6 -> prov ZFpure (psub (tauM Mf) sid (HT i))) ->
  prov ZFpure (rel Mf (axf 6)) ->
  prov ZFpure (STR Lev) -> prov ZFpure (SSUB Mf Lev) -> prov ZFpure (SIN Mf Lev) -> prov ZFpure (SCOV Mf Lev) ->
  GREFL Mf Lev ->
  (forall g n, syms g = [] -> closedk (S (S n)) g = true -> DEFsep Mf Lev g n) ->
  prov ZFpure (rel Mf VL) -> prov (ZFE VL) (pi ch) ->
  prov GamCH Bot -> prov ZFpure Bot.
Proof.
  intros Hex H6 Hc Htr Hsub Hin Hcov Hgr Hd Hv D.
  exact (goedel_final_red Mf HM Hp VL HV Hex H6 Hc (lsep_from_grefl Mf HM Lev HL Htr Hcov Hgr Hd)
    (lcoll_from_grefl Mf HM Lev HL Htr Hsub Hin Hcov Hgr) Hv D).
Qed.
