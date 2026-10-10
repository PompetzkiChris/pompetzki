(* L2RSent.v - lane L2R, 2026-10-09. The language and translation of sigma1.rkt (tr, wrap, bq-tr, rel-dsl), in de Bruijn
   form: sentence variables are indices (0 = the innermost bound one), rho places them among the ZF variables.
   Terms: numerals, variables, S, +, *. Formulas: = < <=, not and or imp iff, bounded quantifiers forall x < t,
   exists x < t, forall x <= t, exists x <= t, and some x (an unbounded existential over omega).
   Translation, as sigma1.rkt: a numeral n is exists u (N_n(u) & K(u)); t+s is [t](a. [s](b. exists u (Add(a,b,u) & K(u))));
   S t with Suc, t*s with Mul; < is membership, <= is (in or eq); forall x < t A is [t](b. forall x (x in b -> [A]));
   some x A is exists x (Nat(x) & [A]).
   Theorem (bounded_complete): for every closed sentence s without some, s true in N -> prov Gam [s], and
   s false in N -> prov Gam (not [s]). *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith.
From Cohen Require Import Syn Prov Kal Ax Checks Replay Replay2 Expand Pure RpInitOk RpFinal.
From L2R Require Import L2RLogic L2RArith L2RFin.
Import ListNotations.
Open Scope nat_scope.

Arguments Emp : simpl never.
Arguments Suc : simpl never.
Arguments Opr : simpl never.
Arguments App : simpl never.
Arguments Fnc : simpl never.
Arguments NatP : simpl never.

(* ---- syntax and the standard model *)
Inductive tm : Type := tnum (n : nat) | tvar (i : nat) | tS (t : tm) | tadd (t u : tm) | tmul (t u : tm).

Inductive fm : Type :=
| feq (t u : tm) | flt (t u : tm) | fle (t u : tm)
| fnot (A : fm) | fand (A B : fm) | fdis (A B : fm) | fimp (A B : fm) | fiff (A B : fm)
| fall (t : tm) (A : fm) | fex (t : tm) (A : fm) | falle (t : tm) (A : fm) | fexe (t : tm) (A : fm)
| fsome (A : fm).

Fixpoint ev (e : list nat) (t : tm) : nat :=
  match t with
  | tnum n => n | tvar i => nth i e 0 | tS t => S (ev e t)
  | tadd t u => ev e t + ev e u | tmul t u => ev e t * ev e u
  end.

Fixpoint sat (e : list nat) (A : fm) : Prop :=
  match A with
  | feq t u => ev e t = ev e u
  | flt t u => ev e t < ev e u
  | fle t u => ev e t <= ev e u
  | fnot A => ~ sat e A
  | fand A B => sat e A /\ sat e B
  | fdis A B => sat e A \/ sat e B
  | fimp A B => sat e A -> sat e B
  | fiff A B => (sat e A <-> sat e B)
  | fall t A => forall k, k < ev e t -> sat (k :: e) A
  | fex t A => exists k, k < ev e t /\ sat (k :: e) A
  | falle t A => forall k, k <= ev e t -> sat (k :: e) A
  | fexe t A => exists k, k <= ev e t /\ sat (k :: e) A
  | fsome A => exists k, sat (k :: e) A
  end.

(* the free variables of t are below m *)
Fixpoint wft (m : nat) (t : tm) : Prop :=
  match t with
  | tnum _ => True | tvar i => i < m | tS t => wft m t
  | tadd t u | tmul t u => wft m t /\ wft m u
  end.

Fixpoint wf (m : nat) (A : fm) : Prop :=
  match A with
  | feq t u | flt t u | fle t u => wft m t /\ wft m u
  | fnot A => wf m A
  | fand A B | fdis A B | fimp A B | fiff A B => wf m A /\ wf m B
  | fall t A | fex t A | falle t A | fexe t A => wft m t /\ wf (S m) A
  | fsome A => wf (S m) A
  end.

(* no unbounded quantifier *)
Fixpoint bounded (A : fm) : Prop :=
  match A with
  | feq _ _ | flt _ _ | fle _ _ => True
  | fnot A => bounded A
  | fand A B | fdis A B | fimp A B | fiff A B => bounded A /\ bounded B
  | fall _ A | fex _ A | falle _ A | fexe _ A => bounded A
  | fsome _ => False
  end.

(* ---- the translation *)
Definition shS (rho : nat -> nat) : nat -> nat := fun i => S (rho i).
Definition rho2 (rho : nat -> nat) : nat -> nat := scons 0 (fun i => S (S (rho i))).

Fixpoint wrap (t : tm) (rho : nat -> nat) (K : form) : form :=
  match t with
  | tnum n => Xf (Kf (Num n 0) K)
  | tvar i => ren (scons (rho i) sid) K
  | tS a => wrap a rho (Xf (Kf (Suc 0 1) (ren (up S) K)))
  | tadd a b => wrap a rho (wrap b (shS rho) (Xf (Kf (AddF 2 1 0) (ren (up (fun n => S (S n))) K))))
  | tmul a b => wrap a rho (wrap b (shS rho) (Xf (Kf (MulF 2 1 0) (ren (up (fun n => S (S n))) K))))
  end.

Fixpoint tr (A : fm) (rho : nat -> nat) : form :=
  match A with
  | feq t u => wrap t rho (wrap u (shS rho) (Eqv 1 0))
  | flt t u => wrap t rho (wrap u (shS rho) (Mem 1 0))
  | fle t u => wrap t rho (wrap u (shS rho) (Df (Mem 1 0) (Eqv 1 0)))
  | fnot A => Neg (tr A rho)
  | fand A B => Kf (tr A rho) (tr B rho)
  | fdis A B => Df (tr A rho) (tr B rho)
  | fimp A B => Imp (tr A rho) (tr B rho)
  | fiff A B => Qf (tr A rho) (tr B rho)
  | fall t A => wrap t rho (All (Imp (Mem 0 1) (tr A (rho2 rho))))
  | fex t A => wrap t rho (Xf (Kf (Mem 0 1) (tr A (rho2 rho))))
  | falle t A => wrap t rho (All (Imp (Df (Mem 0 1) (Eqv 0 1)) (tr A (rho2 rho))))
  | fexe t A => wrap t rho (Xf (Kf (Df (Mem 0 1) (Eqv 0 1)) (tr A (rho2 rho))))
  | fsome A => Xf (Kf (NatP 0) (tr A (scons 0 (shS rho))))
  end.

(* ---- decidability of bounded truth *)
Lemma dec_all_lt n (P : nat -> Prop) : (forall k, P k \/ ~ P k) -> (forall k, k < n -> P k) \/ (exists k, k < n /\ ~ P k).
Proof.
  intros Hd. induction n as [|n IH]; [left; intros k Hk; lia|].
  destruct IH as [IH|[k [Hk Hn]]]; [|right; exists k; split; [lia|exact Hn]].
  destruct (Hd n) as [Hp|Hn]; [left; intros k Hk; destruct (Nat.eq_dec k n) as [->|Ne]; [exact Hp|apply IH; lia]|].
  right. exists n. split; [lia|exact Hn].
Qed.

Lemma dec_ex_lt n (P : nat -> Prop) : (forall k, P k \/ ~ P k) -> (exists k, k < n /\ P k) \/ (forall k, k < n -> ~ P k).
Proof.
  intros Hd. induction n as [|n IH]; [right; intros k Hk; lia|].
  destruct IH as [[k [Hk Hp]]|IH]; [left; exists k; split; [lia|exact Hp]|].
  destruct (Hd n) as [Hp|Hn]; [left; exists n; split; [lia|exact Hp]|].
  right. intros k Hk. destruct (Nat.eq_dec k n) as [->|Ne]; [exact Hn|apply IH; lia].
Qed.

Lemma sat_dec A : bounded A -> forall e, sat e A \/ ~ sat e A.
Proof.
  induction A; cbn [bounded sat]; intros Hb e; try tauto.
  - destruct (Nat.eq_dec (ev e t) (ev e u)); tauto.
  - destruct (Nat.lt_ge_cases (ev e t) (ev e u)); [left; exact H|right; lia].
  - destruct (Nat.le_gt_cases (ev e t) (ev e u)); [left; exact H|right; lia].
  - destruct (IHA Hb e); tauto.
  - destruct Hb as [H1 H2]. destruct (IHA1 H1 e), (IHA2 H2 e); tauto.
  - destruct Hb as [H1 H2]. destruct (IHA1 H1 e), (IHA2 H2 e); tauto.
  - destruct Hb as [H1 H2]. destruct (IHA1 H1 e), (IHA2 H2 e); tauto.
  - destruct Hb as [H1 H2]. destruct (IHA1 H1 e), (IHA2 H2 e); tauto.
  - destruct (dec_all_lt (ev e t) (fun k => sat (k :: e) A) (fun k => IHA Hb (k :: e))) as [H|[k [Hk Hn]]];
      [left; exact H|right; intros H; exact (Hn (H k Hk))].
  - destruct (dec_ex_lt (ev e t) (fun k => sat (k :: e) A) (fun k => IHA Hb (k :: e))) as [H|H];
      [left; exact H|right; intros [k [Hk Hs]]; exact (H k Hk Hs)].
  - destruct (dec_all_lt (S (ev e t)) (fun k => sat (k :: e) A) (fun k => IHA Hb (k :: e))) as [H|[k [Hk Hn]]];
      [left; intros k Hk; apply H; lia|right; intros H; apply Hn; apply H; lia].
  - destruct (dec_ex_lt (S (ev e t)) (fun k => sat (k :: e) A) (fun k => IHA Hb (k :: e))) as [[k [Hk Hs]]|H];
      [left; exists k; split; [lia|exact Hs]|right; intros [k [Hk Hs]]; exact (H k ltac:(lia) Hs)].
Qed.

(* ---- renamings *)
Lemma map_ren2 G s t : map (ren s) (map (ren t) G) = map (ren (fun n => s (t n))) G.
Proof. rewrite map_map. apply map_ext. intros g. apply ren_comp. Qed.

Lemma map_ren_ext G s t : (forall n, s n = t n) -> map (ren s) G = map (ren t) G.
Proof. intros H. apply map_ext. intros g. apply ren_ext. exact H. Qed.

Lemma map_ren_back G y : map (ren (scons y sid)) (map (ren S) G) = G.
Proof.
  rewrite map_ren2. rewrite <- (map_id G) at 2. apply map_ext. intros g. apply ren_id'. intros n. reflexivity.
Qed.

Lemma ren_back P : ren (scons 0 sid) (ren (up S) P) = P.
Proof. rewrite ren_comp. apply ren_id'. intros [|n]; reflexivity. Qed.

Lemma D_into G K s G' : D G K -> (forall g, In g (map (ren s) G) -> D G' g) -> D G' (ren s K).
Proof. intros H I. exact (D_ctx _ _ _ I (D_ren _ _ s H)). Qed.

Lemma In_map_ren g G s t : (forall n, s n = t n) -> In g (map (ren s) G) -> In g (map (ren t) G).
Proof. intros H I. rewrite (map_ren_ext G t s); [exact I|]. intros n. symmetry. apply H. Qed.

(* a member of a shifted copy of G, found in the current context *)
Lemma In_map_ren2 g G s t : In g (map (ren s) G) -> (forall n, s n = t n) -> In g (map (ren t) G).
Proof. intros I H. exact (In_map_ren g G s t H I). Qed.
Ltac inG Hg := rewrite ?map_ren2 in Hg; rewrite ?map_ren2; apply D_hyp; repeat right; eapply In_map_ren2; [exact Hg|intros ?; reflexivity].

Lemma D_negT G P : D (P :: G) (Neg Top) -> D G (Neg P).
Proof. intros H. apply (D_t2 _ (Imp P (Neg Top)) Top); [pt|apply D_intro; exact H|apply D_thm; exact Top_pv]. Qed.

(* a numeral exists: a fresh variable with N_k may be assumed for an existential *)
Lemma num_exI k G P : D (Num k 0 :: map (ren S) G) P -> D G (Xf P).
Proof.
  intros H. apply (D_exE _ _ _ (D_NumEx G k)). rewrite ren_Xf. apply (D_exI _ _ 0). rewrite ren_back. exact H.
Qed.

Lemma MemCharLe n G x y : D G (Num n y) -> D G (Qf (Df (Mem x y) (Eqv x y)) (Disj (S n) x)).
Proof.
  intros Hy. rewrite Disj_S. pose proof (MemChar n G x y Hy) as H1.
  have H2 (Qf (Eqv x y) (Num n x)).
  { apply D_iffi.
    - apply (D_Num_eq _ n y x); [apply D_sym; hyp|apply D_add; exact Hy].
    - apply (NumUq n); [hyp|apply D_add; exact Hy]. }
  dt2 H1 H2.
Qed.

(* ---- the environment: sentence variable i has the value nth i e 0, and rho i is that numeral *)
Definition Env (e : list nat) (rho : nat -> nat) (G : list form) : Prop :=
  forall i, i < length e -> D G (Num (nth i e 0) (rho i)).

Lemma Env_weak e rho G G' : (forall g, In g G -> In g G') -> Env e rho G -> Env e rho G'.
Proof. intros I H i Hi. exact (D_weak _ _ _ I (H i Hi)). Qed.

Lemma Env_sh e rho G : Env e rho G -> Env e (shS rho) (map (ren S) G).
Proof. intros H i Hi. pose proof (D_ren _ _ S (H i Hi)) as H'. rewrite ren_Num in H'. exact H'. Qed.

Lemma Env_sh1 e rho G a : Env e rho G -> Env e (shS rho) (a :: map (ren S) G).
Proof. intros H. apply (Env_weak _ _ (map (ren S) G)); [intros g Hg; right; exact Hg|]. apply Env_sh. exact H. Qed.

Lemma Env_bind k e rho G : Env e rho G -> forall G', (forall g, In g (map (ren S) (map (ren S) G)) -> In g G') ->
  D G' (Num k 0) -> Env (k :: e) (rho2 rho) G'.
Proof.
  intros H G' I Hk [|i] Hi; [exact Hk|]. cbn [nth length] in *.
  apply (D_weak _ _ _ I). pose proof (D_ren _ _ S (D_ren _ _ S (H i ltac:(lia)))) as H'. rewrite !ren_Num in H'. exact H'.
Qed.

(* ---- terms: proving and refuting [t](K) through a variable holding the value of t *)
Lemma WrapPos t : forall e rho G K, wft (length e) t -> Env e rho G ->
  D (Num (ev e t) 0 :: map (ren S) G) K -> D G (wrap t rho K).
Proof.
  induction t as [n|i|a IH|a IHa b IHb|a IHa b IHb]; intros e rho G K Hw He H; cbn [wrap ev wft] in *.
  - apply num_exI with (k := n). apply D_and; [hyp|exact H].
  - pose proof (D_ren _ _ (scons (rho i) sid) H) as H1. cbn [map] in H1. rewrite ren_Num, map_ren_back in H1.
    cbn in H1. exact (D_cut _ _ _ (He i Hw) H1).
  - apply (IH e rho G _ Hw He).
    apply (D_exE _ (Suc 0 1)); [apply D_thm; exact (F_SucEx 0)|]. rs3. apply (D_exI _ _ 0). rewrite ren_Kf, ren_back. rs3.
    apply D_and; [hyp|].
    apply (D_into _ _ _ _ H). intros g Hg. cbn [map] in Hg. destruct Hg as [<-|Hg].
    + rs3. rewrite Num_S. apply (D_exI _ _ 1). rs3. apply D_and; hyp.
    + inG Hg.
  - destruct Hw as [Hwa Hwb]. apply (IHa e rho G _ Hwa He).
    apply (IHb e (shS rho) _ _ Hwb (Env_sh1 _ _ _ _ He)).
    rs3. apply (D_exE2 _ (Num (ev e a + ev e b) 0) (AddF 2 1 0)); [apply AddExist; hyp|]. rs3.
    apply (D_exI _ _ 0). rs3. apply D_and; [hyp|].
    rewrite ren_back.
    apply (D_into _ _ _ _ H). intros g Hg. cbn [map] in Hg. destruct Hg as [<-|Hg]; [rs3; hyp|inG Hg].
  - destruct Hw as [Hwa Hwb]. apply (IHa e rho G _ Hwa He).
    apply (IHb e (shS rho) _ _ Hwb (Env_sh1 _ _ _ _ He)).
    rs3. apply (D_exE2 _ (Num (ev e b * ev e a) 0) (MulF 2 1 0)); [apply MulExist; hyp|]. rs3.
    apply (D_exI _ _ 0). rs3. apply D_and; [hyp|].
    rewrite ren_back.
    apply (D_into _ _ _ _ H). intros g Hg. cbn [map] in Hg. destruct Hg as [<-|Hg]; [rs3; rewrite Nat.mul_comm; hyp|inG Hg].
Qed.

Lemma WrapNeg t : forall e rho G K, wft (length e) t -> Env e rho G ->
  D (Num (ev e t) 0 :: map (ren S) G) (Neg K) -> D G (Neg (wrap t rho K)).
Proof.
  induction t as [n|i|a IH|a IHa b IHb|a IHa b IHb]; intros e rho G K Hw He H; cbn [wrap ev wft] in *.
  - apply D_negT. apply (D_exE2 _ (Num n 0) K); [hyp|]. rs3.
    apply (D_absurd _ K); [hyp|].
    apply (D_ctx (Num n 0 :: map (ren S) G)); [intros g Hg; destruct Hg as [<-|Hg]; [hyp|apply D_hyp; repeat right; exact Hg]|exact H].
  - pose proof (D_ren _ _ (scons (rho i) sid) H) as H1. cbn [map] in H1. rewrite ren_Num, map_ren_back in H1.
    cbn in H1. exact (D_cut _ _ _ (He i Hw) H1).
  - apply (IH e rho G _ Hw He). apply D_negT.
    apply (D_exE2 _ (Suc 0 1) (ren (up S) K)); [hyp|]. rs3.
    addh (Num (S (ev e a)) 0). { rewrite Num_S. apply (D_exI _ _ 1). rs3. apply D_and; hyp. }
    apply (D_absurd _ (ren (up S) K)); [hyp|].
    change (Neg (ren (up S) K)) with (ren (up S) (Neg K)).
    apply (D_into _ _ _ _ H). intros g Hg. cbn [map] in Hg. destruct Hg as [<-|Hg]; [rs3; hyp|inG Hg].
  - destruct Hw as [Hwa Hwb]. apply (IHa e rho G _ Hwa He).
    apply (IHb e (shS rho) _ _ Hwb (Env_sh1 _ _ _ _ He)). rs3. apply D_negT.
    apply (D_exE2 _ (AddF 2 1 0) (ren (up (fun n => S (S n))) K)); [hyp|]. rs3.
    addh (Num (ev e a + ev e b) 0). { apply (AddVal _ _ _ 2 1); hyp. }
    apply (D_absurd _ (ren (up (fun n => S (S n))) K)); [hyp|].
    change (Neg (ren (up (fun n => S (S n))) K)) with (ren (up (fun n => S (S n))) (Neg K)).
    apply (D_into _ _ _ _ H). intros g Hg. cbn [map] in Hg. destruct Hg as [<-|Hg]; [rs3; hyp|inG Hg].
  - destruct Hw as [Hwa Hwb]. apply (IHa e rho G _ Hwa He).
    apply (IHb e (shS rho) _ _ Hwb (Env_sh1 _ _ _ _ He)). rs3. apply D_negT.
    apply (D_exE2 _ (MulF 2 1 0) (ren (up (fun n => S (S n))) K)); [hyp|]. rs3.
    addh (Num (ev e a * ev e b) 0).
    { rewrite Nat.mul_comm. apply (D_iffl _ (MulF 2 1 0)); [apply MulChar; hyp|hyp]. }
    apply (D_absurd _ (ren (up (fun n => S (S n))) K)); [hyp|].
    change (Neg (ren (up (fun n => S (S n))) K)) with (ren (up (fun n => S (S n))) (Neg K)).
    apply (D_into _ _ _ _ H). intros g Hg. cbn [map] in Hg. destruct Hg as [<-|Hg]; [rs3; hyp|inG Hg].
Qed.

(* ---- formulas *)
Lemma Env_G2 k e rho G G' : Env e rho G -> (forall g, In g (map (ren S) (map (ren S) G)) -> In g G') ->
  In (Num k 0) G' -> Env (k :: e) (rho2 rho) G'.
Proof. intros He I Ik. apply (Env_bind k e rho G He G' I). apply D_hyp. exact Ik. Qed.

Ltac inmap := intros ? ?; repeat right; assumption.
Ltac ihp IH Hb Hw He k e rho G := match goal with |- D ?G1 _ =>
  apply (proj1 (IH Hb (k :: e) (rho2 rho) G1 Hw (Env_G2 k e rho G G1 He ltac:(inmap) ltac:(repeat (first [left; reflexivity | right]))))) end.
Ltac ihn IH Hb Hw He k e rho G := match goal with |- D ?G1 _ =>
  apply (proj2 (IH Hb (k :: e) (rho2 rho) G1 Hw (Env_G2 k e rho G G1 He ltac:(inmap) ltac:(repeat (first [left; reflexivity | right]))))) end.

Lemma main A : bounded A -> forall e rho G, wf (length e) A -> Env e rho G ->
  (sat e A -> D G (tr A rho)) /\ (~ sat e A -> D G (Neg (tr A rho))).
Proof.
  induction A as [t u|t u|t u|A IH|A IHA B IHB|A IHA B IHB|A IHA B IHB|A IHA B IHB|t A IH|t A IH|t A IH|t A IH|A IH];
    intros Hb e rho G Hw He; cbn [bounded wf sat tr] in *.
  - (* = *)
    destruct Hw as [Ht Hu]. split; intros Hs.
    + apply (WrapPos t e rho G _ Ht He). apply (WrapPos u e (shS rho) _ _ Hu (Env_sh1 _ _ _ _ He)). rs3.
      apply (NumUq (ev e u)); [rewrite <- Hs; hyp|hyp].
    + apply (WrapNeg t e rho G _ Ht He). apply (WrapNeg u e (shS rho) _ _ Hu (Env_sh1 _ _ _ _ He)). rs3.
      apply (NumNe (ev e t) (ev e u)); [exact Hs|hyp|hyp].
  - (* < *)
    destruct Hw as [Ht Hu]. split; intros Hs.
    + apply (WrapPos t e rho G _ Ht He). apply (WrapPos u e (shS rho) _ _ Hu (Env_sh1 _ _ _ _ He)). rs3.
      apply (NumIn (ev e t) (ev e u)); [exact Hs|hyp|hyp].
    + apply (WrapNeg t e rho G _ Ht He). apply (WrapNeg u e (shS rho) _ _ Hu (Env_sh1 _ _ _ _ He)). rs3.
      apply (NumNotIn (ev e t) (ev e u)); [lia|hyp|hyp].
  - (* <= *)
    destruct Hw as [Ht Hu]. split; intros Hs.
    + apply (WrapPos t e rho G _ Ht He). apply (WrapPos u e (shS rho) _ _ Hu (Env_sh1 _ _ _ _ He)). rs3.
      destruct (Nat.lt_ge_cases (ev e t) (ev e u)) as [L|L].
      * apply D_orl. apply (NumIn (ev e t) (ev e u)); [exact L|hyp|hyp].
      * apply D_orr. apply (NumUq (ev e u)); [replace (ev e u) with (ev e t) by lia; hyp|hyp].
    + apply (WrapNeg t e rho G _ Ht He). apply (WrapNeg u e (shS rho) _ _ Hu (Env_sh1 _ _ _ _ He)). rs3.
      have N1 (Neg (Mem 1 0)). { apply (NumNotIn (ev e t) (ev e u)); [lia|hyp|hyp]. }
      have N2 (Neg (Eqv 1 0)). { apply (NumNe (ev e t) (ev e u)); [lia|hyp|hyp]. }
      dt2 N1 N2.
  - (* not *)
    destruct (IH Hb e rho G Hw He) as [P N]. split; intros Hs.
    + exact (N Hs).
    + destruct (sat_dec A Hb e) as [S0|S0]; [|tauto]. pose proof (P S0) as H. dt1 H.
  - (* and *)
    destruct Hb as [Ha Hb']. destruct Hw as [Hwa Hwb].
    destruct (IHA Ha e rho G Hwa He) as [PA NA]. destruct (IHB Hb' e rho G Hwb He) as [PB NB]. split; intros Hs.
    + destruct Hs as [S1 S2]. apply D_and; [exact (PA S1)|exact (PB S2)].
    + destruct (sat_dec A Ha e) as [S1|S1].
      * assert (S2 : ~ sat e B) by tauto. pose proof (NB S2) as H. dt1 H.
      * pose proof (NA S1) as H. dt1 H.
  - (* or *)
    destruct Hb as [Ha Hb']. destruct Hw as [Hwa Hwb].
    destruct (IHA Ha e rho G Hwa He) as [PA NA]. destruct (IHB Hb' e rho G Hwb He) as [PB NB]. split; intros Hs.
    + destruct Hs as [S1|S2]; [apply D_orl; exact (PA S1)|apply D_orr; exact (PB S2)].
    + assert (S1 : ~ sat e A) by tauto. assert (S2 : ~ sat e B) by tauto.
      pose proof (NA S1) as H1. pose proof (NB S2) as H2. dt2 H1 H2.
  - (* imp *)
    destruct Hb as [Ha Hb']. destruct Hw as [Hwa Hwb].
    destruct (IHA Ha e rho G Hwa He) as [PA NA]. destruct (IHB Hb' e rho G Hwb He) as [PB NB]. split; intros Hs.
    + destruct (sat_dec A Ha e) as [S1|S1].
      * pose proof (PB (Hs S1)) as H. dt1 H.
      * pose proof (NA S1) as H. dt1 H.
    + destruct (sat_dec A Ha e) as [S1|S1]; [|tauto]. destruct (sat_dec B Hb' e) as [S2|S2]; [tauto|].
      pose proof (PA S1) as H1. pose proof (NB S2) as H2. dt2 H1 H2.
  - (* iff *)
    destruct Hb as [Ha Hb']. destruct Hw as [Hwa Hwb].
    destruct (IHA Ha e rho G Hwa He) as [PA NA]. destruct (IHB Hb' e rho G Hwb He) as [PB NB].
    destruct (sat_dec A Ha e) as [S1|S1]; destruct (sat_dec B Hb' e) as [S2|S2]; split; intros Hs; try tauto.
    + pose proof (PA S1) as H1. pose proof (PB S2) as H2. dt2 H1 H2.
    + pose proof (PA S1) as H1. pose proof (NB S2) as H2. dt2 H1 H2.
    + pose proof (NA S1) as H1. pose proof (PB S2) as H2. dt2 H1 H2.
    + pose proof (NA S1) as H1. pose proof (NB S2) as H2. dt2 H1 H2.
  - (* forall x < t *)
    destruct Hw as [Ht Hw]. split; intros Hs.
    + apply (WrapPos t e rho G _ Ht He). apply D_all. apply D_intro. rs3.
      addh (Disj (ev e t) 0). { apply (D_iffl _ (Mem 0 1)); [apply MemChar; hyp|hyp]. }
      apply DisjE. intros k Hk.
      ihp IH Hb Hw He k e rho G.
      exact (Hs k Hk).
    + destruct (dec_all_lt (ev e t) (fun k => sat (k :: e) A) (fun k => sat_dec A Hb (k :: e))) as [H|[k [Hk Hn]]];
        [tauto|].
      apply (WrapNeg t e rho G _ Ht He). apply D_negT.
      apply (D_exE _ (Num k 0)); [apply D_NumEx|]. rs3.
      addh (Imp (Mem 0 1) (tr A (rho2 rho))).
      { replace (Imp (Mem 0 1) (tr A (rho2 rho))) with (ren (scons 0 sid) (Imp (Mem 0 2) (ren (up S) (tr A (rho2 rho)))))
          by (cbn; rewrite ren_back; reflexivity).
        apply D_inst. hyp. }
      addh (tr A (rho2 rho)). { apply (D_mp _ (Mem 0 1)); [hyp|]. apply (NumIn k (ev e t)); [exact Hk|hyp|hyp]. }
      apply (D_absurd _ (tr A (rho2 rho))); [hyp|].
      ihn IH Hb Hw He k e rho G.
      exact Hn.
  - (* exists x < t *)
    destruct Hw as [Ht Hw]. split; intros Hs.
    + destruct Hs as [k [Hk Hs]]. apply (WrapPos t e rho G _ Ht He). apply (num_exI k). rs3. apply D_and.
      * apply (NumIn k (ev e t)); [exact Hk|hyp|hyp].
      * ihp IH Hb Hw He k e rho G.
        exact Hs.
    + apply (WrapNeg t e rho G _ Ht He). apply D_negT.
      apply (D_exE2 _ (Mem 0 1) (tr A (rho2 rho))); [hyp|]. rs3.
      addh (Disj (ev e t) 0). { apply (D_iffl _ (Mem 0 1)); [apply MemChar; hyp|hyp]. }
      apply DisjE. intros k Hk.
      apply (D_absurd _ (tr A (rho2 rho))); [hyp|].
      ihn IH Hb Hw He k e rho G.
      intros S1. exact (Hs (ex_intro _ k (conj Hk S1))).
  - (* forall x <= t *)
    destruct Hw as [Ht Hw]. split; intros Hs.
    + apply (WrapPos t e rho G _ Ht He). apply D_all. apply D_intro. rs3.
      addh (Disj (S (ev e t)) 0). { apply (D_iffl _ (Df (Mem 0 1) (Eqv 0 1))); [apply MemCharLe; hyp|hyp]. }
      apply DisjE. intros k Hk.
      ihp IH Hb Hw He k e rho G.
      apply Hs. lia.
    + destruct (dec_all_lt (S (ev e t)) (fun k => sat (k :: e) A) (fun k => sat_dec A Hb (k :: e))) as [H|[k [Hk Hn]]].
      { exfalso. apply Hs. intros k Hk. apply H. lia. }
      apply (WrapNeg t e rho G _ Ht He). apply D_negT.
      apply (D_exE _ (Num k 0)); [apply D_NumEx|]. rs3.
      addh (Imp (Df (Mem 0 1) (Eqv 0 1)) (tr A (rho2 rho))).
      { replace (Imp (Df (Mem 0 1) (Eqv 0 1)) (tr A (rho2 rho)))
          with (ren (scons 0 sid) (Imp (Df (Mem 0 2) (Eqv 0 2)) (ren (up S) (tr A (rho2 rho)))))
          by (rs3; rewrite ren_back; reflexivity).
        apply D_inst. hyp. }
      addh (tr A (rho2 rho)).
      { apply (D_mp _ (Df (Mem 0 1) (Eqv 0 1))); [hyp|].
        apply (D_iffr _ _ (Disj (S (ev e t)) 0)); [apply MemCharLe; hyp|].
        apply (D_t1 _ (Num k 0)); [apply DisjI; exact Hk|hyp]. }
      apply (D_absurd _ (tr A (rho2 rho))); [hyp|].
      ihn IH Hb Hw He k e rho G.
      exact Hn.
  - (* exists x <= t *)
    destruct Hw as [Ht Hw]. split; intros Hs.
    + destruct Hs as [k [Hk Hs]]. apply (WrapPos t e rho G _ Ht He). apply (num_exI k). rs3. apply D_and.
      * apply (D_iffr _ _ (Disj (S (ev e t)) 0)); [apply MemCharLe; hyp|].
        apply (D_t1 _ (Num k 0)); [apply DisjI; lia|hyp].
      * ihp IH Hb Hw He k e rho G.
        exact Hs.
    + apply (WrapNeg t e rho G _ Ht He). apply D_negT.
      apply (D_exE2 _ (Df (Mem 0 1) (Eqv 0 1)) (tr A (rho2 rho))); [hyp|]. rs3.
      addh (Disj (S (ev e t)) 0). { apply (D_iffl _ (Df (Mem 0 1) (Eqv 0 1))); [apply MemCharLe; hyp|hyp]. }
      apply DisjE. intros k Hk.
      apply (D_absurd _ (tr A (rho2 rho))); [hyp|].
      ihn IH Hb Hw He k e rho G.
      intros S1. apply Hs. exists k. split; [lia|exact S1].
  - (* some: not bounded *)
    destruct Hb.
Qed.

(* ---- the theorem *)
Theorem bounded_complete (A : fm) : bounded A -> wf 0 A ->
  (sat [] A -> prov Gam (tr A sid)) /\ (~ sat [] A -> prov Gam (Neg (tr A sid))).
Proof.
  intros Hb Hw.
  assert (He : Env [] sid []) by (intros i Hi; cbn in Hi; lia).
  destruct (main A Hb [] sid [] Hw He) as [P N].
  split; intros Hs; apply D_nil; [exact (P Hs)|exact (N Hs)].
Qed.
