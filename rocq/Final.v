(* Final.v - Con(ZFC) -> Con(ZFC + notCH-star), for every input derivation.
   Input theory Gam0: the seven axioms, Separation, Collection, the 23 ZB_BASE definitions, notCH-star.
   Pure ZFC (ZFpure): the seven axioms (Ext Pair Union Power Inf Found Choice) and every Separation and Collection
   instance of the pure language (E and = only).
   Premises, each a statement the kernel accepted, parsed from the kernel's own text (Data.v):
     KERNEL  the 46 interface theorems are derivable from Gam and their placeholder hypotheses (tpl1.src, runs/r_tpl1-01)
     TNOTCH  TNotchT: I CohP1 pp Vw439x2 pp pp is derivable from Gam (tvn3.src, receipt R6)
     COHEX   CohEx: X pp CohP1 pp is derivable from Gam (fn8.src)
   Theorem: if Gam0 derives Bot, pure ZFC derives Bot. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Use Sub Inv2 Sub2 Sub3 Expand Pure Notch Claim Elim.
Import ListNotations.
Open Scope nat_scope.

Definition COHEX : Prop := forall f, pstmt symtab [] cohex = Some f -> prov Gam f.

Lemma cohex_parse : pstmt symtab [] cohex = Some (Xf (Pr coh [0])).
Proof. vm_compute. reflexivity. Qed.

Theorem gam0_gam : KERNEL -> TNOTCH -> COHEX -> prov Gam0 Bot -> prov Gam Bot.
Proof.
  intros K TN CE D.
  pose proof (claim K TN Bot D) as H1. rewrite (pi_fix Bot eq_refl) in H1.
  assert (H2 : prov Gam (Imp Coh (Neg (TOPf (V Bot))))) by (apply prov_nohyp; apply (useK K "TplFN"); vm_compute; reflexivity).
  pose proof (CE _ cohex_parse) as H3.
  (* Coh -> TOP, Coh -> ~TOP: ~Coh; for every pp: A pp ~Coh; with X pp Coh: Bot *)
  assert (H4 : prov Gam (Neg Coh)).
  { apply (mp2 _ _ _ _ H1 H2).
    pose proof (ptaut_prov Gam (PI (PI (PV 0) (PV 1)) (PI (PI (PV 0) (PN (PV 1))) (PN (PV 0))))
      (lv [Coh; TOPf (V Bot)]) ltac:(vm_compute; reflexivity)) as T. exact T. }
  pose proof (p_gen _ _ H4) as H5.
  apply (mp2 _ _ _ _ H5 H3).
  pose proof (ptaut_prov Gam (PI (PV 0) (PI (PN (PV 0)) (PV 1))) (lv [All (Neg Coh); Bot])
    ltac:(vm_compute; reflexivity)) as T. exact T.
Qed.

Theorem cohen_relative_consistency : KERNEL -> TNOTCH -> COHEX -> prov Gam0 Bot -> prov ZFpure Bot.
Proof. intros K TN CE D. apply zfsym_pure, gam_zfsym, (gam0_gam K TN CE D). Qed.

Corollary con_zfc_con_notch : KERNEL -> TNOTCH -> COHEX -> ~ prov ZFpure Bot -> ~ prov Gam0 Bot.
Proof. intros K TN CE C D. exact (C (cohen_relative_consistency K TN CE D)). Qed.

(* notCH-star as Gam0 states it: the kernel's text, parsed *)
Lemma notch_is_notch_text : pstmt symtab [] notch_text = Some notch.
Proof. vm_compute. reflexivity. Qed.
