(* LAXred2.v - six of the seven LAX obligations of GoedelCH.v reduced to plain properties of the class.
   (LAXred2.v = LAXred.v with three proof repairs: psub_rel's binder case, syms_psub_M without simpl in *, the
   arguments of gam_psub; LAXred.v stops at line 76.)
   The lane's judge-accepted file out4/02-relax.jdg (both judges ACCEPT, 6 theorems, 106 steps; RelB.v is its
   transcription by jdg2v.rkt) is replayed by Replay2.check_batch over REGP (the first 677 entries of REG0). Its theorem
   677 + i is  HT i -> rel M0 (axf i)  for i = 0..5 (Ext, Pair, Union, Power, Inf, Found), M0 = the predicate symbol
   5000 at v0, defined nowhere; HT i is its hypothesis, read from the replay:
     HT 0, HT 5   M transitive
     HT 1         M transitive is not used; M holds {x, y} for x, y in M
     HT 2         M holds the union of each member
     HT 3         M transitive, and for x in M some y in M holds every subset of x that is in M
     HT 4         M transitive, and some inductive set is in M
   For a pure class formula Mf (closedk 1, no symbols), uniform substitution of Mf for 5000 (Gam's definitions do not
   mention 5000) and the elimination of all 670 definitions from a pure theorem give
     lax_reduced    : ZFpure |- HT i [Mf]  ->  ZFpure |- rel Mf (axf i)            (i < 6)
     goedel_reduced : LEX, the six HT i [Mf], Choice relativized, LSEP, LCOLL, LCH  ->  GamCH |- Bot -> ZFpure |- Bot
   Lane LCH, 2026-10-09. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Use Expand Pure Elim.
From Cohen Require Import Replay Replay2 Replay3 RpInit RpInitOk.
From LCH Require Import Rel2 GoedelCH RelB.
Import ListNotations.
Open Scope nat_scope.

(* ---- the replay of out4/02-relax.jdg *)
Definition REGP : list entry := firstn 677 REG0.
Lemma REGP_ok : reg_ok hypf REGP.
Proof.
  intros i d h E. apply (REG0_ok i d h).
  assert (Hi : i < List.length REGP) by (apply nth_error_Some; congruence).
  rewrite <- (firstn_skipn 677 REG0). rewrite nth_error_app1 by exact Hi. exact E.
Qed.
Lemma RB_ok : check_batch REGP RB = true. Proof. vm_compute. reflexivity. Qed.
Lemma REGR_ok : reg_ok hypf (REGP ++ map ent RB). Proof. exact (check_batch_ok hypf REGP RB REGP_ok RB_ok). Qed.

Definition M0 : form := Pr 5000 [0].
Definition HT (i : nat) : form :=
  match nth_error (REGP ++ map ent RB) (677 + i) with
  | Some (d, _) => match tof d with Imp h _ => h | _ => Top end
  | None => Top end.
Definition rel_ok (i : nat) : bool :=
  match nth_error (REGP ++ map ent RB) (677 + i) with
  | Some (d, []) => match tof d with Imp _ c => form_eqb c (rel M0 (axf i)) | _ => false end
  | _ => false end.

Lemma rel_ok_prov i : rel_ok i = true -> prov Gam (Imp (HT i) (rel M0 (axf i))).
Proof.
  unfold rel_ok, HT. destruct (nth_error (REGP ++ map ent RB) (677 + i)) as [[d [|h r]]|] eqn:E; try discriminate.
  destruct (tof d) eqn:Td; try discriminate. intros Q. apply form_eqb_true in Q. subst f2.
  rewrite <- Td. apply (prov_mono (AH hypf [])); [|exact (REGR_ok _ d [] E)].
  intros g [G|[h [[] _]]]. exact G.
Qed.
Lemma rel_ok_all : forallb rel_ok (seq 0 6) = true. Proof. vm_compute. reflexivity. Qed.
Lemma HT_syms : forallb (fun i => forallb (Nat.eqb 5000) (syms (HT i))) (seq 0 6) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma defs_no5000 : forallb (fun d => negb (existsb (Nat.eqb 5000) (syms (defax d)))) Dall = true.
Proof. vm_compute. reflexivity. Qed.

(* ---- uniform substitution of a class formula for the symbol 5000 *)
Definition tauM (Mf : form) : nat -> option form := fun q => if Nat.eqb q 5000 then Some Mf else None.

Section Inst.
Variable Mf : form.
Hypothesis HM : closedk 1 Mf = true.
Hypothesis Hp : syms Mf = [].

Lemma psub_M0 rho : psub (tauM Mf) rho M0 = Mf.
Proof.
  simpl. unfold tauM. simpl. rewrite <- (ren_id Mf) at 2. apply ren_free. intros n Fn.
  pose proof (closedk_free Mf 1 n HM Fn) as L. assert (n = 0) by lia. subst n. reflexivity.
Qed.

Lemma psub_rel f : syms f = [] -> forall rho, psub (tauM Mf) rho (rel M0 f) = rel Mf f.
Proof.
  induction f; intros Hs rho; simpl in *; try reflexivity; try discriminate.
  - rewrite IHf; auto.
  - apply app_eq_nil in Hs as [H1 H2]. rewrite IHf1, IHf2; auto.
  - rewrite IHf by exact Hs. f_equal. f_equal. exact (psub_M0 (fun n => S (rho n))).
Qed.

Lemma syms_psub_M f : forallb (Nat.eqb 5000) (syms f) = true -> forall rho, syms (psub (tauM Mf) rho f) = [].
Proof.
  induction f; intros Hs rho.
  - reflexivity.
  - reflexivity.
  - cbn [syms forallb] in Hs. apply andb_true_iff in Hs as [E _]. apply Nat.eqb_eq in E. subst n.
    cbn [psub]. unfold tauM. rewrite Nat.eqb_refl. simpl. rewrite syms_ren. exact Hp.
  - cbn [syms] in Hs. cbn [psub syms]. apply IHf; exact Hs.
  - cbn [syms] in Hs. rewrite forallb_app in Hs. apply andb_true_iff in Hs as [H1 H2]. cbn [psub syms].
    rewrite IHf1, IHf2; auto.
  - cbn [syms] in Hs. cbn [psub syms]. apply IHf; exact Hs.
Qed.
Lemma gam_psub : forall f, prov Gam f -> forall rho, prov Gam (psub (tauM Mf) rho f).
Proof.
  intros f D rho. apply (prov_psub_to Gam Gam (tauM Mf) (fun _ => True)); [auto| |exact D|exact I].
  intros r g _ [[i [Hi ->]]|[[h ->]|[[h ->]|[d [s [Hd ->]]]]]].
  - apply p_ax. left. exists i. split; [exact Hi|]. apply psub_none. rewrite (axf_pure i Hi). simpl. tauto.
  - apply p_ax. right. left. rewrite SepF_psub. eexists. reflexivity.
  - apply p_ax. right. right. left. rewrite CollF_psub. eexists. reflexivity.
  - apply p_ax. right. right. right. exists d, s. split; [exact Hd|]. apply psub_none. rewrite syms_ren.
    intros q Hq. unfold tauM. destruct (Nat.eqb q 5000) eqn:E; [|reflexivity]. apply Nat.eqb_eq in E. subst q.
    pose proof defs_no5000 as C. rewrite forallb_forall in C. specialize (C d Hd). apply negb_true_iff in C.
    assert (existsb (Nat.eqb 5000) (syms (defax d)) = true)
      by (apply existsb_exists; exists 5000; split; [exact Hq|apply Nat.eqb_refl]).
    congruence.
Qed.
End Inst.

(* ---- a pure theorem of Gam is a theorem of pure ZFC: Elim.v's steps over all 670 definitions *)
Definition GamLE (L : list (nat * nat * form)) (e : form) (f : form) : Prop := GamL L f \/ f = e.

Lemma elim_step_e L p k B e : stepok L (p, k, B) = true -> negb (existsb (Nat.eqb p) (syms e)) = true ->
  forall f, prov (GamLE (L ++ [(p, k, B)]) e) f -> forall rho, prov (GamLE L e) (psub (tau1 p B) rho f).
Proof.
  intros Hs He. unfold stepok in Hs. apply andb_true_iff in Hs as [Hs Hpre]. apply andb_true_iff in Hs as [Hc Hn].
  intros f D rho.
  apply (prov_psub_to (GamLE (L ++ [(p, k, B)]) e) (GamLE L e) (tau1 p B) (fun _ => True)); [auto| |exact D|exact I].
  intros r g _ [[[[i [Hi ->]]|[[h ->]|[h ->]]]|[d [s [Hd ->]]]]| ->].
  - apply p_ax. left. left. left. exists i. split; [exact Hi|]. apply psub_none. rewrite (axf_pure i Hi). simpl. tauto.
  - apply p_ax. left. left. right. left. rewrite SepF_psub. eexists. reflexivity.
  - apply p_ax. left. left. right. right. rewrite CollF_psub. eexists. reflexivity.
  - apply in_app_or in Hd as [Hd|[<-|[]]].
    + apply p_ax. left. right. exists d, s. split; [exact Hd|]. apply psub_none. rewrite syms_ren.
      apply (tau1_none p B). rewrite forallb_forall in Hpre. exact (Hpre d Hd).
    + assert (E1 : psub (tau1 p B) r (ren s B) = ren s B).
      { apply psub_none. rewrite syms_ren. exact (tau1_none p B _ Hn). }
      assert (E2 : psub (tau1 p B) r (Pr p (map s (seq 0 k))) = ren s B).
      { simpl. unfold tau1. rewrite Nat.eqb_refl. apply ren_free. intros i Fi.
        pose proof (closedk_free B k i Hc Fi) as Lt. unfold inst_args. rewrite length_map, length_seq.
        replace (i <? k) with true by (symmetry; apply Nat.ltb_lt; exact Lt).
        rewrite (nth_indep _ 0 (s 0)) by (rewrite length_map, length_seq; exact Lt).
        rewrite map_nth, seq_nth by exact Lt. reflexivity. }
      unfold defax, Qf, Kf. simpl. simpl in E2. rewrite E1, E2. apply iff_refl.
  - apply p_ax. right. apply psub_none. exact (tau1_none p B _ He).
Qed.

Definition dsym (d : nat * nat * form) : nat := match d with (p, _, _) => p end.

Lemma elim_tail L1 e f : forall L2, okb L1 L2 = true ->
  (forall d, In d L2 -> negb (existsb (Nat.eqb (dsym d)) (syms e)) = true /\
                        negb (existsb (Nat.eqb (dsym d)) (syms f)) = true) ->
  prov (GamLE (L1 ++ L2) e) f -> prov (GamLE L1 e) f.
Proof.
  intros L2. induction L2 as [|d L2 IH] using rev_ind; intros Ok Hs D.
  - rewrite app_nil_r in D. exact D.
  - rewrite okb_app in Ok. apply andb_true_iff in Ok as [Ok1 Ok2]. destruct d as [[p k] B].
    assert (Hd : In (p, k, B) (L2 ++ [(p, k, B)])) by (apply in_or_app; right; left; reflexivity).
    destruct (Hs _ Hd) as [He Hf]. simpl in He, Hf.
    apply IH; [exact Ok1|intros d' Hd'; apply Hs; apply in_or_app; left; exact Hd'|].
    rewrite app_assoc in D. pose proof (elim_step_e (L1 ++ L2) p k B e Ok2 He f D sid) as P.
    rewrite psub_none in P; [exact P|]. exact (tau1_none p B _ Hf).
Qed.

Theorem gam_pure f : prov Gam f -> syms f = [] -> prov ZFpure f.
Proof.
  intros D Hs.
  assert (D1 : prov (GamLE ([] ++ Dall) (Eqv 0 0)) f).
  { apply (prov_mono Gam); [|exact D]. intros g [Z|[Sp|[Co|Df]]]; left;
      [left; left; exact Z|left; right; left; exact Sp|left; right; right; exact Co|right; exact Df]. }
  assert (D2 : prov (GamLE [] (Eqv 0 0)) f).
  { apply (elim_tail [] (Eqv 0 0) f Dall okb_Dall); [|exact D1]. intros d _. rewrite Hs. split; reflexivity. }
  assert (D3 : prov ZFsym f).
  { apply (prov_cut (GamLE [] (Eqv 0 0))); [|exact D2].
    intros g [[Z|[d [s [[] _]]]]| ->]; [apply p_ax; exact Z|apply p_refl]. }
  rewrite <- (psub_none f tauTop sid) by (rewrite Hs; simpl; tauto).
  apply (prov_psub_to ZFsym ZFpure tauTop (fun _ => True)); [auto| |exact D3|exact I].
  intros r g _ [[i [Hi ->]]|[[h ->]|[h ->]]].
  - apply p_ax. rewrite psub_none by (rewrite (axf_pure i Hi); simpl; tauto).
    split; [left; exists i; split; [exact Hi|reflexivity]|exact (axf_pure i Hi)].
  - apply p_ax. rewrite SepF_psub. split; [right; left; eexists; reflexivity|].
    unfold SepF, Qf, Kf, Xf. simpl. rewrite syms_ren, psub_top_pure. reflexivity.
  - apply p_ax. rewrite CollF_psub. split; [right; right; eexists; reflexivity|].
    unfold CollF, Kf, Xf. simpl. rewrite syms_ren, psub_top_pure. reflexivity.
Qed.

(* ---- six of the seven LAX obligations, from plain properties of the class *)
Lemma syms_rel_pure Mf (Hp : syms Mf = []) f : syms f = [] -> syms (rel Mf f) = [].
Proof.
  induction f; simpl; intros H; try reflexivity; try discriminate.
  - apply IHf; exact H.
  - apply app_eq_nil in H as [H1 H2]. rewrite IHf1, IHf2; auto.
  - rewrite Hp, IHf by exact H. reflexivity.
Qed.

Section Red.
Variable Mf : form.
Hypothesis HM : closedk 1 Mf = true.
Hypothesis Hp : syms Mf = [].

Theorem lax_reduced i : i < 6 -> prov ZFpure (psub (tauM Mf) sid (HT i)) -> prov ZFpure (rel Mf (axf i)).
Proof.
  intros Hi P.
  assert (Ok : rel_ok i = true).
  { pose proof rel_ok_all as C. rewrite forallb_forall in C. apply C. apply in_seq. lia. }
  assert (Sy : forallb (Nat.eqb 5000) (syms (HT i)) = true).
  { pose proof HT_syms as C. rewrite forallb_forall in C. apply C. apply in_seq. lia. }
  pose proof (gam_psub Mf (Imp (HT i) (rel M0 (axf i))) (rel_ok_prov i Ok) sid) as G. simpl in G.
  rewrite (psub_rel Mf HM (axf i) (axf_pure i ltac:(lia)) sid) in G.
  assert (Pu : syms (Imp (psub (tauM Mf) sid (HT i)) (rel Mf (axf i))) = []).
  { simpl. rewrite (syms_psub_M Mf Hp (HT i) Sy sid). simpl.
    exact (syms_rel_pure Mf Hp (axf i) (axf_pure i ltac:(lia))). }
  exact (p_mp _ _ _ P (gam_pure _ G Pu)).
Qed.

Theorem goedel_reduced : LEX Mf ->
  (forall i, i < 6 -> prov ZFpure (psub (tauM Mf) sid (HT i))) ->
  prov ZFpure (rel Mf (axf 6)) ->
  LSEP Mf -> LCOLL Mf -> LCH Mf -> prov GamCH Bot -> prov ZFpure Bot.
Proof.
  intros Hex H6 Hc Hsep Hcoll Hch D.
  apply (goedel_relative_consistency Mf HM Hex); [|exact Hsep|exact Hcoll|exact Hch|exact D].
  intros i Hi. destruct (Nat.lt_ge_cases i 6) as [L|L]; [exact (lax_reduced i L (H6 i L))|].
  assert (i = 6) by lia. subst i. exact Hc.
Qed.
End Red.
