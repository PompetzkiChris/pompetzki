(* AlignCH.v - Theorem 29 over the plain statement of not CH. The lane's judge-accepted file out/01-align.jdg (both
   judges ACCEPT, 5 theorems, 76 steps; AlignB.v is its transcription by jdg2v.rkt) is replayed by Replay2.check_batch,
   sound by Replay3.check_batch_ok, over the registry REGP = the first 677 entries of RpInitOk.REG0 (7 axioms, 670
   definitions; the lane files' registry, entry for entry). Two of its theorems:
     entry 679  notCH* -> not CH          entry 680  not CH -> notCH*
   with ch the plain CH of GoedelCH.v and notch the notCH* of Pure.v, each derivable in Gam (all 670 definitions).
   The 647 definitions after ZB_BASE are eliminated (Elim.v's step, carrying one extra axiom whose symbols they avoid),
   which gives Gam0 |- not CH and GamE (not CH) |- notCH*. Hence
     notch_plain_equiv        : prov (GamE (Neg ch)) Bot <-> prov Gam0 Bot
     con_zfc_con_notch_plain  : prov (GamE (Neg ch)) Bot -> prov ZFpure Bot         (no premise)
   The input theory GamE (Neg ch) is GamCH of GoedelCH.v with CH replaced by its negation: the two halves of the
   independence of CH now concern one statement.
   Lane LCH, 2026-10-09. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Use Expand Pure Elim Final.
From Cohen Require Import Replay Replay2 Replay3 RpInit RpInitOk RpFinal.
From LCH Require Import Rel2 GoedelCH AlignB.
Import ListNotations.
Open Scope nat_scope.

(* ---- the replay of out/01-align.jdg *)
Definition REGP : list entry := firstn 677 REG0.
Lemma REGP_ok : reg_ok hypf REGP.
Proof.
  intros i d h E. apply (REG0_ok i d h).
  assert (Hi : i < List.length REGP) by (apply nth_error_Some; congruence).
  rewrite <- (firstn_skipn 677 REG0). rewrite nth_error_app1 by exact Hi. exact E.
Qed.
Lemma AB_ok : check_batch REGP AB = true. Proof. vm_compute. reflexivity. Qed.
Lemma REGA_ok : reg_ok hypf (REGP ++ map ent AB). Proof. exact (check_batch_ok hypf REGP AB REGP_ok AB_ok). Qed.

Definition entry_isA (i : nat) (f : form) : bool :=
  match nth_error (REGP ++ map ent AB) i with Some (d, []) => form_eqb (tof d) f | _ => false end.
Lemma entry_isA_prov i f : entry_isA i f = true -> prov Gam f.
Proof.
  unfold entry_isA. destruct (nth_error (REGP ++ map ent AB) i) as [[d [|h r]]|] eqn:E; try discriminate.
  intros Q. apply form_eqb_true in Q. subst f.
  apply (prov_mono (AH hypf [])); [|exact (REGA_ok i d [] E)].
  intros g [G|[h [[] _]]]. exact G.
Qed.
Lemma notch_plain_entry : entry_isA 679 (Imp notch (Neg ch)) = true. Proof. vm_compute. reflexivity. Qed.
Lemma plain_notch_entry : entry_isA 680 (Imp (Neg ch) notch) = true. Proof. vm_compute. reflexivity. Qed.

(* ---- elimination of definitions, with one extra axiom e *)
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

(* Dall = ZB_BASE ++ the rest; the checks are stated expanded, so the kernel never unfolds Dall, D0 or D1 *)
Definition D1 : list (nat * nat * form) := somes (map pdef (skipn 23 defs)).
Lemma Dall_split : Dall = (D0 ++ D1)%list. Proof. vm_compute. reflexivity. Qed.

Lemma okb_app2 pre L1 L2 : okb pre (L1 ++ L2) = okb pre L1 && okb (pre ++ L1) L2.
Proof.
  revert pre. induction L1 as [|d r IH]; intros pre; simpl; [rewrite app_nil_r; reflexivity|].
  rewrite IH, <- app_assoc. simpl. rewrite andb_assoc. reflexivity.
Qed.
Lemma okb_D1 : okb D0 D1 = true.
Proof. pose proof okb_Dall as O. rewrite Dall_split, okb_app2, app_nil_l in O. apply andb_true_iff in O as [_ O]. exact O. Qed.

Lemma avoid_in (l : list (nat * nat * form)) f :
  forallb (fun d => negb (existsb (Nat.eqb (dsym d)) (syms f))) l = true ->
  forall d, In d l -> negb (existsb (Nat.eqb (dsym d)) (syms f)) = true.
Proof. intros A d H. rewrite forallb_forall in A. exact (A d H). Qed.
Lemma avoid_notch_x : forallb (fun d => negb (existsb (Nat.eqb (dsym d)) (syms notch))) D1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma avoid_nch_x : forallb (fun d => negb (existsb (Nat.eqb (dsym d)) (syms (Neg ch)))) D1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma gam_to_gamle e f : prov Gam (Imp e f) -> prov (GamLE Dall e) f.
Proof.
  intros P. apply (p_mp _ e); [apply p_ax; right; reflexivity|].
  apply (prov_mono Gam); [|exact P].
  intros g [Z|[Sp|[Co|Df]]]; left; [left; left; exact Z|left; right; left; exact Sp|left; right; right; exact Co|right; exact Df].
Qed.

Lemma down e f :
  forallb (fun d => negb (existsb (Nat.eqb (dsym d)) (syms e))) D1 = true ->
  forallb (fun d => negb (existsb (Nat.eqb (dsym d)) (syms f))) D1 = true ->
  prov Gam (Imp e f) -> prov (GamE e) f.
Proof.
  intros Ae Af P. pose proof (gam_to_gamle e f P) as Q. rewrite Dall_split in Q.
  pose proof (elim_tail D0 e f D1 okb_D1 (fun d Hd => conj (avoid_in D1 e Ae d Hd) (avoid_in D1 f Af d Hd)) Q) as R.
  apply (prov_mono (GamLE D0 e)); [|exact R].
  intros g [[[Z|[Sp|Co]]|Df]| ->]; unfold GamE; tauto.
Qed.

(* ---- the two theories prove the same; Theorem 29 over the plain statement *)
Theorem gam0_neg_ch : prov Gam0 (Neg ch).
Proof.
  pose proof (down notch (Neg ch) avoid_notch_x avoid_nch_x (entry_isA_prov _ _ notch_plain_entry)) as P.
  apply (prov_mono (GamE notch)); [|exact P]. intros g H. exact H.
Qed.

Theorem gamnch_notch : prov (GamE (Neg ch)) notch.
Proof. exact (down (Neg ch) notch avoid_nch_x avoid_notch_x (entry_isA_prov _ _ plain_notch_entry)). Qed.

Theorem notch_plain_equiv : prov (GamE (Neg ch)) Bot <-> prov Gam0 Bot.
Proof.
  split; intros D.
  - apply (prov_cut (GamE (Neg ch))); [|exact D].
    intros g [Z|[Sp|[Co|[Df| ->]]]]; try (apply p_ax; unfold Gam0; tauto). exact gam0_neg_ch.
  - apply (prov_cut Gam0); [|exact D].
    intros g [Z|[Sp|[Co|[Df| ->]]]]; try (apply p_ax; unfold GamE; tauto). exact gamnch_notch.
Qed.

Theorem con_zfc_con_notch_plain : prov (GamE (Neg ch)) Bot -> prov ZFpure Bot.
Proof. intros D. exact (cohen_relative_consistency_closed (proj1 notch_plain_equiv D)). Qed.

Corollary con_zfc_con_notch_plain' : ~ prov ZFpure Bot -> ~ prov (GamE (Neg ch)) Bot.
Proof. intros C D. exact (C (con_zfc_con_notch_plain D)). Qed.
