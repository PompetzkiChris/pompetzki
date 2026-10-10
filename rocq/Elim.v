(* Elim.v - from Gam to pure ZFC. The definitions go one at a time, the last registered first: substituting a
   definition's body for its symbol turns its own axiom into X <-> X and leaves every earlier definition, the seven axioms,
   Separation and Collection in place (checked: each body is closed over its arity and mentions neither its own symbol
   nor, among the definitions registered before it, any that would be substituted; okb). Then every remaining predicate
   symbol goes to the closed pure formula Top: Separation and Collection instances become pure instances. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Use Expand Pure.
Import ListNotations.
Open Scope nat_scope.

Definition ZFsym (f : form) : Prop := ZFC7 f \/ SepAx f \/ CollAx f.
Definition ZFpure (f : form) : Prop := ZFsym f /\ syms f = [].
Definition GamL (L : list (nat * nat * form)) (f : form) : Prop := ZFsym f \/ DefAx L f.

Definition tau1 (p : nat) (B : form) : nat -> option form := fun q => if Nat.eqb q p then Some B else None.

Definition stepok (pre : list (nat * nat * form)) (d : nat * nat * form) : bool :=
  match d with (p, k, B) =>
    closedk k B && negb (existsb (Nat.eqb p) (syms B)) &&
    forallb (fun e => negb (existsb (Nat.eqb p) (syms (defax e)))) pre
  end.

Fixpoint okb (pre L : list (nat * nat * form)) : bool :=
  match L with [] => true | d :: r => stepok pre d && okb (pre ++ [d]) r end.

Lemma okb_app pre L d : okb pre (L ++ [d]) = okb pre L && stepok (pre ++ L) d.
Proof.
  revert pre. induction L as [|e r IH]; intros pre; simpl.
  - rewrite app_nil_r. destruct (stepok pre d); reflexivity.
  - rewrite IH, <- app_assoc. simpl. rewrite andb_assoc. reflexivity.
Qed.

Lemma notin_syms p l : negb (existsb (Nat.eqb p) l) = true -> forall q, In q l -> q <> p.
Proof.
  intros H q Hq E. subst q. apply negb_true_iff in H.
  assert (existsb (Nat.eqb p) l = true) by (apply existsb_exists; exists p; split; [exact Hq|apply Nat.eqb_refl]).
  congruence.
Qed.

Lemma tau1_none p B l : negb (existsb (Nat.eqb p) l) = true -> forall q, In q l -> tau1 p B q = None.
Proof.
  intros H q Hq. unfold tau1. destruct (Nat.eqb q p) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E. exfalso. exact (notin_syms p l H q Hq E).
Qed.

Lemma elim_step L p k B : stepok L (p, k, B) = true ->
  forall f, prov (GamL (L ++ [(p, k, B)])) f -> forall rho, prov (GamL L) (psub (tau1 p B) rho f).
Proof.
  intros Hs. unfold stepok in Hs. apply andb_true_iff in Hs as [Hs Hpre]. apply andb_true_iff in Hs as [Hc Hn].
  intros f D rho.
  apply (prov_psub_to (GamL (L ++ [(p, k, B)])) (GamL L) (tau1 p B) (fun _ => True)); [auto| |exact D|exact I].
  intros r g _ [[[i [Hi ->]]|[[h ->]|[h ->]]]|[d [s [Hd ->]]]].
  - apply p_ax. left. left. exists i. split; [exact Hi|]. apply psub_none. rewrite (axf_pure i Hi). simpl. tauto.
  - apply p_ax. left. right. left. rewrite SepF_psub. eexists. reflexivity.
  - apply p_ax. left. right. right. rewrite CollF_psub. eexists. reflexivity.
  - apply in_app_or in Hd as [Hd|[<-|[]]].
    + apply p_ax. right. exists d, s. split; [exact Hd|]. apply psub_none. rewrite syms_ren.
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
Qed.

Lemma psub_Bot tau rho : psub tau rho Bot = Bot. Proof. reflexivity. Qed.

Theorem elim_all : forall L, okb [] L = true -> prov (GamL L) Bot -> prov ZFsym Bot.
Proof.
  intros L. induction L as [|d L IH] using rev_ind; intros Ok D.
  - apply (prov_mono (GamL [])); [|exact D]. intros f [Z|[d [s [[] _]]]]. exact Z.
  - rewrite okb_app in Ok. apply andb_true_iff in Ok as [Ok1 Ok2]. simpl in Ok2. destruct d as [[p k] B].
    apply IH; [exact Ok1|]. rewrite <- (psub_Bot (tau1 p B) sid). exact (elim_step L p k B Ok2 Bot D sid).
Qed.

(* the definitions in registration order satisfy the conditions *)
Lemma okb_Dall : okb [] Dall = true. Proof. vm_compute. reflexivity. Qed.

Theorem gam_zfsym : prov Gam Bot -> prov ZFsym Bot.
Proof.
  intros D. apply (elim_all Dall okb_Dall). apply (prov_mono Gam); [|exact D].
  intros f [Z|[Sp|[Co|Df]]]; [left; left; exact Z|left; right; left; exact Sp|left; right; right; exact Co|right; exact Df].
Qed.

(* ---- the remaining symbols *)
Definition tauTop : nat -> option form := fun _ => Some Top.

Lemma psub_top_pure f : forall rho, syms (psub tauTop rho f) = [].
Proof.
  induction f; intros rho; simpl; try reflexivity; try (apply IHf); try (rewrite IHf1, IHf2; reflexivity).
Qed.

Theorem zfsym_pure : prov ZFsym Bot -> prov ZFpure Bot.
Proof.
  intros D. rewrite <- (psub_Bot tauTop sid).
  apply (prov_psub_to ZFsym ZFpure tauTop (fun _ => True)); [auto| |exact D|exact I].
  intros r g _ [[i [Hi ->]]|[[h ->]|[h ->]]].
  - apply p_ax. rewrite psub_none by (rewrite (axf_pure i Hi); simpl; tauto).
    split; [left; exists i; split; [exact Hi|reflexivity]|exact (axf_pure i Hi)].
  - apply p_ax. rewrite SepF_psub. split; [right; left; eexists; reflexivity|].
    unfold SepF, Qf, Kf, Xf. simpl. rewrite syms_ren, psub_top_pure. reflexivity.
  - apply p_ax. rewrite CollF_psub. split; [right; right; eexists; reflexivity|].
    unfold CollF, Kf, Xf. simpl. rewrite syms_ren, psub_top_pure. reflexivity.
Qed.
