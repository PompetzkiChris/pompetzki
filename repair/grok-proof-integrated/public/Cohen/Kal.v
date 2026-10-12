(* Kal.v - every tautology is derivable (Kalmar): atoms are the subformulas that are not N or I. And a decidable test on
   propositional schemas (variables standing for any formulas), so a schematic propositional step is one instance. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
From Cohen Require Import Syn Prov.
Import ListNotations.

Fixpoint peval (v : form -> bool) (f : form) : bool :=
  match f with
  | Neg a => negb (peval v a)
  | Imp a b => implb (peval v a) (peval v b)
  | _ => v f
  end.

Definition taut (f : form) : Prop := forall v, peval v f = true.

Fixpoint atoms (f : form) : list form :=
  match f with
  | Neg a => atoms a
  | Imp a b => atoms a ++ atoms b
  | _ => [f]
  end.

(* ---- the propositional calculus with hypotheses *)
Inductive hp (G : list form) : form -> Prop :=
| h_hyp f : In f G -> hp G f
| h_k a b : hp G (Imp a (Imp b a))
| h_s a b c : hp G (Imp (Imp a (Imp b c)) (Imp (Imp a b) (Imp a c)))
| h_c a b : hp G (Imp (Imp (Neg a) (Neg b)) (Imp b a))
| h_mp a b : hp G a -> hp G (Imp a b) -> hp G b.

Lemma hp_weak G f : hp G f -> forall G', (forall x, In x G -> In x G') -> hp G' f.
Proof.
  induction 1; intros G' HG.
  - apply h_hyp; auto.
  - apply h_k.
  - apply h_s.
  - apply h_c.
  - eapply h_mp; [apply IHhp1|apply IHhp2]; auto.
Qed.

Lemma hp_id G a : hp G (Imp a a).
Proof.
  eapply h_mp; [apply (h_k G a a)|].
  eapply h_mp; [apply (h_k G a (Imp a a))|apply (h_s G a (Imp a a) a)].
Qed.

Theorem hp_dt G a b : hp (a :: G) b -> hp G (Imp a b).
Proof.
  induction 1.
  - destruct H as [<-|H]; [apply hp_id|]. eapply h_mp; [apply h_hyp; exact H|apply h_k].
  - eapply h_mp; [apply h_k|apply h_k].
  - eapply h_mp; [apply h_s|apply h_k].
  - eapply h_mp; [apply h_c|apply h_k].
  - eapply h_mp; [exact IHhp1|]. eapply h_mp; [exact IHhp2|apply h_s].
Qed.

Lemma hp_mp2 G a b : hp G (Imp a b) -> hp G a -> hp G b.
Proof. intros H1 H2. eapply h_mp; eauto. Qed.

Lemma hp_in G a : hp (a :: G) a.
Proof. apply h_hyp. left. reflexivity. Qed.

Lemma hp_lift G a f : hp G f -> hp (a :: G) f.
Proof. intros H. eapply hp_weak; [exact H|]. intros x Hx. right. exact Hx. Qed.

(* L3: N a -> (a -> b) *)
Lemma hp_L3 G a b : hp G (Imp (Neg a) (Imp a b)).
Proof.
  apply hp_dt. eapply hp_mp2; [apply h_c|]. eapply hp_mp2; [apply h_k|apply hp_in].
Qed.

(* L1: N N b -> b *)
Lemma hp_L1 G b : hp G (Imp (Neg (Neg b)) b).
Proof.
  apply hp_dt.
  assert (H3 : hp (Neg (Neg b) :: G) (Imp (Neg (Neg (Neg (Neg b)))) (Neg (Neg b)))).
  { eapply hp_mp2; [apply h_k|apply hp_in]. }
  assert (H5 : hp (Neg (Neg b) :: G) (Imp (Neg b) (Neg (Neg (Neg b))))).
  { eapply hp_mp2; [apply (h_c _ (Neg (Neg (Neg b))) (Neg b))|exact H3]. }
  assert (H7 : hp (Neg (Neg b) :: G) (Imp (Neg (Neg b)) b)).
  { eapply hp_mp2; [apply (h_c _ b (Neg (Neg b)))|exact H5]. }
  eapply hp_mp2; [exact H7|apply hp_in].
Qed.

(* L2: b -> N N b *)
Lemma hp_L2 G b : hp G (Imp b (Neg (Neg b))).
Proof. eapply hp_mp2; [apply (h_c _ (Neg (Neg b)) b)|apply hp_L1]. Qed.

Lemma hp_chain G a b c : hp G (Imp a b) -> hp G (Imp b c) -> hp G (Imp a c).
Proof.
  intros H1 H2. apply hp_dt. eapply hp_mp2; [apply hp_lift; exact H2|].
  eapply hp_mp2; [apply hp_lift; exact H1|apply hp_in].
Qed.

(* L5: (a -> b) -> (N b -> N a) *)
Lemma hp_L5 G a b : hp G (Imp (Imp a b) (Imp (Neg b) (Neg a))).
Proof.
  apply hp_dt. eapply hp_mp2; [apply (h_c _ (Neg a) (Neg b))|].
  eapply hp_chain; [apply hp_L1|]. eapply hp_chain; [apply hp_in|apply hp_L2].
Qed.

(* L6: a -> (N b -> N (a -> b)) *)
Lemma hp_L6 G a b : hp G (Imp a (Imp (Neg b) (Neg (Imp a b)))).
Proof.
  apply hp_dt. eapply hp_mp2; [apply hp_L5|].
  apply hp_dt. eapply hp_mp2; [apply hp_in|apply hp_lift; apply hp_in].
Qed.

(* L7: (a -> b) -> ((N a -> b) -> b) *)
Lemma hp_L7 G a b : hp G (Imp (Imp a b) (Imp (Imp (Neg a) b) b)).
Proof.
  apply hp_dt. apply hp_dt.
  set (i := Imp b b).
  assert (Hn : hp (Imp (Neg a) b :: Imp a b :: G) (Imp (Neg b) (Neg i))).
  { apply hp_dt.
    assert (Ha : hp (Neg b :: Imp (Neg a) b :: Imp a b :: G) (Neg a)).
    { eapply hp_mp2; [|apply hp_in]. eapply hp_mp2; [apply hp_L5|]. apply hp_lift, hp_lift, hp_in. }
    assert (Hna : hp (Neg b :: Imp (Neg a) b :: Imp a b :: G) (Neg (Neg a))).
    { eapply hp_mp2; [|apply hp_in]. eapply hp_mp2; [apply hp_L5|]. apply hp_lift, hp_in. }
    eapply hp_mp2; [|exact Ha]. eapply hp_mp2; [apply (hp_L3 _ (Neg a) (Neg i))|exact Hna]. }
  eapply hp_mp2; [|apply hp_id]. fold i. eapply hp_mp2; [apply (h_c _ b i)|exact Hn].
Qed.

Lemma hp_cases G a f : hp (a :: G) f -> hp (Neg a :: G) f -> hp G f.
Proof.
  intros H1 H2. apply hp_dt in H1. apply hp_dt in H2.
  eapply hp_mp2; [|exact H2]. eapply hp_mp2; [apply hp_L7|exact H1].
Qed.

(* ---- Kalmar *)
Definition lit (v : form -> bool) (a : form) : form := if v a then a else Neg a.

Lemma kalmar_lemma (v : form -> bool) f : forall G, (forall a, In a (atoms f) -> In (lit v a) G) ->
  hp G (if peval v f then f else Neg f).
Proof.
  induction f; intros G HG; simpl in *;
    try (specialize (HG _ (or_introl eq_refl)); unfold lit in HG; destruct (v _); apply h_hyp; exact HG).
  - specialize (IHf G HG). destruct (peval v f); simpl.
    + eapply hp_mp2; [apply hp_L2|exact IHf].
    + exact IHf.
  - assert (H1 := IHf1 G (fun a Ha => HG a (in_or_app _ _ _ (or_introl Ha)))).
    assert (H2 := IHf2 G (fun a Ha => HG a (in_or_app _ _ _ (or_intror Ha)))).
    destruct (peval v f1), (peval v f2); simpl.
    + eapply hp_mp2; [apply h_k|exact H2].
    + eapply hp_mp2; [|exact H2]. eapply hp_mp2; [apply hp_L6|exact H1].
    + eapply hp_mp2; [apply h_k|exact H2].
    + eapply hp_mp2; [apply hp_L3|exact H1].
Qed.

Definition upd (v : form -> bool) (a : form) (b : bool) : form -> bool :=
  fun x => if form_eq_dec x a then b else v x.

Lemma elim_atoms f : forall L, (forall v, hp (map (lit v) L) f) -> hp [] f.
Proof.
  induction L as [|a L IH]; intros H.
  - exact (H (fun _ => true)).
  - apply IH. intros v. apply (hp_cases _ a).
    + specialize (H (upd v a true)). simpl in H.
      eapply hp_weak; [exact H|]. intros x Hx. destruct Hx as [Hx|Hx].
      * left. rewrite <- Hx. unfold lit, upd. destruct (form_eq_dec a a); [reflexivity|congruence].
      * apply in_map_iff in Hx. destruct Hx as [y [Hy1 Hy2]]. subst x. unfold lit at 1, upd.
        destruct (form_eq_dec y a) as [->|Ne]; [left; reflexivity|right].
        apply in_map_iff. exists y. split; [unfold lit; reflexivity|exact Hy2].
    + specialize (H (upd v a false)). simpl in H.
      eapply hp_weak; [exact H|]. intros x Hx. destruct Hx as [Hx|Hx].
      * left. rewrite <- Hx. unfold lit, upd. destruct (form_eq_dec a a); [reflexivity|congruence].
      * apply in_map_iff in Hx. destruct Hx as [y [Hy1 Hy2]]. subst x. unfold lit at 1, upd.
        destruct (form_eq_dec y a) as [->|Ne]; [left; reflexivity|right].
        apply in_map_iff. exists y. split; [unfold lit; reflexivity|exact Hy2].
Qed.

Theorem taut_hp f : taut f -> hp [] f.
Proof.
  intros T. apply (elim_atoms f (atoms f)). intros v.
  pose proof (kalmar_lemma v f (map (lit v) (atoms f))) as K.
  rewrite (T v) in K. apply K. intros a Ha. apply in_map. exact Ha.
Qed.

Lemma hp_prov (A : form -> Prop) f : hp [] f -> prov A f.
Proof.
  induction 1.
  - destruct H.
  - apply p_k.
  - apply p_s.
  - apply p_c.
  - eapply p_mp; [exact IHhp1|exact IHhp2].
Qed.

Theorem taut_prov (A : form -> Prop) f : taut f -> prov A f.
Proof. intros T. apply hp_prov, taut_hp, T. Qed.

(* ---- propositional schemas *)
Inductive pform : Type := PV (i : nat) | PN (p : pform) | PI (p q : pform).

Fixpoint pinst (s : nat -> form) (p : pform) : form :=
  match p with PV i => s i | PN q => Neg (pinst s q) | PI q r => Imp (pinst s q) (pinst s r) end.

Fixpoint pval (w : nat -> bool) (p : pform) : bool :=
  match p with PV i => w i | PN q => negb (pval w q) | PI q r => implb (pval w q) (pval w r) end.

Lemma peval_pinst v s p : peval v (pinst s p) = pval (fun i => peval v (s i)) p.
Proof. induction p; simpl; congruence. Qed.

Fixpoint pmax (p : pform) : nat :=
  match p with PV i => S i | PN q => pmax q | PI q r => Nat.max (pmax q) (pmax r) end.

Fixpoint all_bools (n : nat) : list (list bool) :=
  match n with 0 => [[]] | S m => map (cons true) (all_bools m) ++ map (cons false) (all_bools m) end.

Lemma all_bools_in n : forall bs, length bs = n -> In bs (all_bools n).
Proof.
  induction n; intros [|b bs] H; simpl in *; try discriminate; auto.
  apply in_or_app. injection H as H. destruct b; [left|right]; apply in_map; auto.
Qed.

Definition ptautb (p : pform) : bool :=
  forallb (fun bs => pval (fun i => nth i bs false) p) (all_bools (pmax p)).

Lemma pval_ext p : forall w w', (forall i, i < pmax p -> w i = w' i) -> pval w p = pval w' p.
Proof.
  induction p; intros w w' H; simpl in *.
  - apply H. lia.
  - f_equal. apply IHp. auto.
  - f_equal; [apply IHp1|apply IHp2]; intros i Hi; apply H; lia.
Qed.

Lemma ptautb_sound p : ptautb p = true -> forall w, pval w p = true.
Proof.
  unfold ptautb. intros T w. rewrite forallb_forall in T.
  set (bs := map w (seq 0 (pmax p))).
  assert (Hin : In bs (all_bools (pmax p))) by (apply all_bools_in; unfold bs; rewrite length_map, length_seq; reflexivity).
  specialize (T bs Hin). rewrite <- T. apply pval_ext. intros i Hi. unfold bs.
  rewrite (nth_indep _ false (w 0)) by (rewrite length_map, length_seq; exact Hi).
  rewrite map_nth, seq_nth by exact Hi. reflexivity.
Qed.

Theorem ptaut_prov (A : form -> Prop) (p : pform) (s : nat -> form) : ptautb p = true -> prov A (pinst s p).
Proof.
  intros T. apply taut_prov. intros v. rewrite peval_pinst. apply ptautb_sound. exact T.
Qed.

(* the variables of a schema, read from a list *)
Definition lv (l : list form) : nat -> form := fun i => nth i l (Eqv 0 0).
