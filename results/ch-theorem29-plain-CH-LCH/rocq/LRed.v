(* LRed.v - round 2 of lane LCH: obligations O0, O1, O2 of Goedel's half discharged for the class L of LDef.v.
   Lsym = tof Ld (LDef.v) is L over the ZB_BASE symbols; Lpure = pi Lsym is L in the pure language (Pure.pi unfolds
   every ZB_BASE symbol). The lane's judge-accepted files are replayed by Replay2.check_batch over REGP:
     out6/03-lex.jdg (LexB.v)  theorem 704:  X Lsym                                  (O1, exists x L(x))
     out6/04-ltr.jdg (LtrB.v)  theorem 677:  psub (tauM Lsym) sid (HT 0)              (O2, L transitive)
   gam_pi carries a theorem of Gam over ZB_BASE symbols to pure ZFC (AlignCH.down eliminates the other 647
   definitions, GoedelCH.pi_prov purifies). Then
     LEX_L       : LEX Lpure
     HT0_L, HT5_L: the hypotheses HT 0 and HT 5 of LAXred2 for Lpure
     LAX_Ext_L   : ZFpure |- rel Lpure (axf 0)        LAX_Found_L : ZFpure |- rel Lpure (axf 5)
     goedel_L    : the remaining premises (HT 1..4, Choice, LSEP, LCOLL, V = L relativized, ZFpure + V = L |- CH)
                   -> GamCH |- Bot -> ZFpure |- Bot,  with V = L the sentence  All Lpure.
   Lane LCH, 2026-10-09. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Use Expand Pure Elim Final.
From Cohen Require Import Replay Replay2 Replay3 RpInit RpInitOk RpFinal.
From LCH Require Import Rel2 GoedelCH AlignCH LAXred2 VLred LDef LexB LtrB.
Import ListNotations.
Open Scope nat_scope.

Definition Lsym : form := tof Ld.
Definition Lpure : form := Eval vm_compute in pi Lsym.
Lemma Lpure_eq : pi Lsym = Lpure. Proof. vm_compute. reflexivity. Qed.
Lemma Lpure_closed : closedk 1 Lpure = true. Proof. vm_compute. reflexivity. Qed.
Lemma Lpure_syms : syms Lpure = []. Proof. vm_compute. reflexivity. Qed.
Definition VLpure : form := All Lpure.
Lemma VLpure_closed : closedk 0 VLpure = true. Proof. vm_compute. reflexivity. Qed.

(* ---- the replays *)
Lemma LXB_ok : check_batch LAXred2.REGP LXB = true. Proof. vm_compute. reflexivity. Qed.
Lemma LTB_ok : check_batch LAXred2.REGP LTB = true. Proof. vm_compute. reflexivity. Qed.

Definition entry_in (B : list thm) (i : nat) (f : form) : bool :=
  match nth_error (LAXred2.REGP ++ map ent B) i with Some (d, []) => form_eqb (tof d) f | _ => false end.
Lemma entry_in_prov B (H : check_batch LAXred2.REGP B = true) i f : entry_in B i f = true -> prov Gam f.
Proof.
  pose proof (check_batch_ok hypf LAXred2.REGP B LAXred2.REGP_ok H) as R.
  unfold entry_in. destruct (nth_error (LAXred2.REGP ++ map ent B) i) as [[d [|h r]]|] eqn:E; try discriminate.
  intros Q. apply form_eqb_true in Q. subst f.
  apply (prov_mono (AH hypf [])); [|exact (R i d [] E)].
  intros g [G|[h [[] _]]]. exact G.
Qed.

Definition TrL : form := psub (LAXred2.tauM Lsym) sid (LAXred2.HT 0).
Lemma lex_entry : entry_in LXB 704 (Xf Lsym) = true. Proof. vm_compute. reflexivity. Qed.
Lemma ltr_entry : entry_in LTB 677 TrL = true. Proof. vm_compute. reflexivity. Qed.

(* ---- a theorem of Gam over ZB_BASE symbols, purified, is a theorem of pure ZFC *)
Lemma gam_pi f : forallb (fun d => negb (existsb (Nat.eqb (AlignCH.dsym d)) (syms f))) AlignCH.D1 = true ->
  prov Gam f -> prov ZFpure (pi f).
Proof.
  intros A P.
  assert (P1 : prov Gam (Imp Top f)) by (apply (p_mp _ f); [exact P|apply p_k]).
  assert (At : forallb (fun d => negb (existsb (Nat.eqb (AlignCH.dsym d)) (syms Top))) AlignCH.D1 = true)
    by (vm_compute; reflexivity).
  pose proof (AlignCH.down Top f At A P1) as Q.
  pose proof (pi_prov Top f Q) as R. rewrite (pi_fix Top eq_refl) in R.
  apply (prov_cut (ZFE Top)); [|exact R].
  intros g [Z| ->]; [apply p_ax; exact Z|apply p_gen; apply p_refl].
Qed.

(* ---- O1 and O2 *)
Theorem LEX_L : LEX Lpure.
Proof.
  unfold LEX. rewrite <- Lpure_eq.
  assert (E : pi (Xf Lsym) = Xf (pi Lsym)) by (unfold Xf; rewrite pi_neg, pi_all, pi_neg; reflexivity).
  rewrite <- E. apply gam_pi; [vm_compute; reflexivity|exact (entry_in_prov LXB LXB_ok _ _ lex_entry)].
Qed.

Lemma TrL_pi : form_eqb (pi TrL) (psub (LAXred2.tauM Lpure) sid (LAXred2.HT 0)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma HT5_HT0 : form_eqb (LAXred2.HT 5) (LAXred2.HT 0) = true. Proof. vm_compute. reflexivity. Qed.

Theorem HT0_L : prov ZFpure (psub (LAXred2.tauM Lpure) sid (LAXred2.HT 0)).
Proof.
  rewrite <- (form_eqb_true _ _ TrL_pi).
  apply gam_pi; [vm_compute; reflexivity|exact (entry_in_prov LTB LTB_ok _ _ ltr_entry)].
Qed.

Theorem HT5_L : prov ZFpure (psub (LAXred2.tauM Lpure) sid (LAXred2.HT 5)).
Proof. rewrite (form_eqb_true _ _ HT5_HT0). exact HT0_L. Qed.

Theorem LAX_Ext_L : prov ZFpure (rel Lpure (axf 0)).
Proof. exact (lax_reduced Lpure Lpure_closed Lpure_syms 0 ltac:(lia) HT0_L). Qed.
Theorem LAX_Found_L : prov ZFpure (rel Lpure (axf 5)).
Proof. exact (lax_reduced Lpure Lpure_closed Lpure_syms 5 ltac:(lia) HT5_L). Qed.

(* ---- Goedel's half for this L: what remains *)
Theorem goedel_L :
  (forall i, 1 <= i -> i < 5 -> prov ZFpure (psub (LAXred2.tauM Lpure) sid (LAXred2.HT i))) ->
  prov ZFpure (rel Lpure (axf 6)) ->
  LSEP Lpure -> LCOLL Lpure ->
  prov ZFpure (rel Lpure VLpure) -> prov (ZFE VLpure) (pi ch) ->
  prov GamCH Bot -> prov ZFpure Bot.
Proof.
  intros H14 Hc Hsep Hcoll Hv D.
  apply (goedel_final_red Lpure Lpure_closed Lpure_syms VLpure VLpure_closed LEX_L); try assumption.
  intros i Hi. destruct i as [|i]; [exact HT0_L|].
  destruct (Nat.eq_dec i 4) as [->|Ne]; [exact HT5_L|]. apply H14; lia.
Qed.
