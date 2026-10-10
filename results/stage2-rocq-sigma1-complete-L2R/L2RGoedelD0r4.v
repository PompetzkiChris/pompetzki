(* L2RGoedelD0r4.v - lane L2R, recovery 4, 2026-10-09. VLred.goedel_final_red with LSEP Mf (O8) and LCOLL Mf (O9)
   replaced by: the single statements STR, SSUB, SIN, SCOV about a hierarchy of levels Lev, the reflection schema
   GREFL (L2RRefl.v) and the Delta_0 separation schema DSEP0 (L2RDef.v). *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith String.
From Cohen Require Import Syn Prov Kal Ax Checks Replay Expand Pure Elim.
From LCH Require Import Rel2 GoedelCH LAXred2 VLred Abs2.
From L2R Require Import L2RLogicA L2RSepL L2RRefl L2RDef.
Import ListNotations.
Open Scope nat_scope.

Theorem goedel_final_red_d0 (Mf : form) (HM : closedk 1 Mf = true) (Hp : syms Mf = [])
  (Lev : form) (HL : closedk 1 Lev = true) (VL : form) (HV : closedk 0 VL = true) :
  LEX Mf ->
  (forall i, i < 6 -> prov ZFpure (psub (tauM Mf) sid (HT i))) ->
  prov ZFpure (rel Mf (axf 6)) ->
  prov ZFpure (STR Lev) -> prov ZFpure (SSUB Mf Lev) -> prov ZFpure (SIN Mf Lev) -> prov ZFpure (SCOV Mf Lev) ->
  GREFL Mf Lev ->
  (forall psi n, d0 psi -> closedk (S (S n)) psi = true -> DSEP0 Mf psi n) ->
  prov ZFpure (rel Mf VL) -> prov (ZFE VL) (pi ch) ->
  prov GamCH Bot -> prov ZFpure Bot.
Proof.
  intros Hex H6 Hc Htr Hsub Hin Hcov Hgr Hds Hv D.
  exact (goedel_final_red Mf HM Hp VL HV Hex H6 Hc (lsep_from_grefl_dsep0 Mf HM Lev HL Htr Hsub Hin Hcov Hgr Hds)
    (lcoll_from_grefl Mf HM Lev HL Htr Hsub Hin Hcov Hgr) Hv D).
Qed.
