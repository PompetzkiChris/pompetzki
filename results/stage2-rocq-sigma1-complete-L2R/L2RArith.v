(* L2RArith.v - lane L2R, 2026-10-09. The numerals of sigma1.rkt and their facts in Gam, for every n:
   N_0(x) = Emp(x), N_(n+1)(x) = exists y (N_n(y) & Suc(x,y)).
   NumEx: exists x N_n(x).  NumUq: N_n(x) & N_n(y) -> x = y.  MemChar: N_n(y) -> (x in y <-> N_0(x) v .. v N_(n-1)(x)).
   NumIn / NumNotIn: N_k(x) & N_n(y) -> x in y (k < n), not x in y (k >= n).  NumNe: N_k(x) & N_n(y) -> x <> y (k <> n). *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith.
From Cohen Require Import Syn Prov Kal Ax Checks Replay Replay2 Expand Pure RpInitOk RpFinal.
From L2R Require Import L2RLogic.
Import ListNotations.
Open Scope nat_scope.

Arguments Emp : simpl never.
Arguments Suc : simpl never.
Arguments Opr : simpl never.
Arguments App : simpl never.
Arguments Fnc : simpl never.
Arguments NatP : simpl never.

Lemma ren_Emp s x : ren s (Emp x) = Emp (s x). Proof. reflexivity. Qed.
Lemma ren_Suc s a b : ren s (Suc a b) = Suc (s a) (s b). Proof. reflexivity. Qed.
Lemma ren_Opr s a b c : ren s (Opr a b c) = Opr (s a) (s b) (s c). Proof. reflexivity. Qed.
Lemma ren_App s a b c : ren s (App a b c) = App (s a) (s b) (s c). Proof. reflexivity. Qed.
Lemma ren_Fnc s a : ren s (Fnc a) = Fnc (s a). Proof. reflexivity. Qed.
Lemma ren_NatP s a : ren s (NatP a) = NatP (s a). Proof. reflexivity. Qed.

Fixpoint Num (n x : nat) : form :=
  match n with 0 => Emp x | S m => Xf (Kf (Num m 0) (Suc (S x) 0)) end.
Arguments Num : simpl never.
Lemma Num_0 x : Num 0 x = Emp x. Proof. reflexivity. Qed.
Lemma Num_S n x : Num (S n) x = Xf (Kf (Num n 0) (Suc (S x) 0)). Proof. reflexivity. Qed.

Lemma ren_Num n : forall s x, ren s (Num n x) = Num n (s x).
Proof.
  induction n as [|n IH]; intros s x; [reflexivity|].
  rewrite !Num_S, ren_Xf, ren_Kf, IH, ren_Suc. reflexivity.
Qed.

(* the members of N_n: N_0(x) v .. v N_(n-1)(x), with N_(-1) false *)
Fixpoint Disj (n x : nat) : form := match n with 0 => Neg Top | S m => Df (Disj m x) (Num m x) end.
Arguments Disj : simpl never.
Lemma Disj_0 x : Disj 0 x = Neg Top. Proof. reflexivity. Qed.
Lemma Disj_S n x : Disj (S n) x = Df (Disj n x) (Num n x). Proof. reflexivity. Qed.
Lemma ren_Disj n : forall s x, ren s (Disj n x) = Disj n (s x).
Proof.
  induction n as [|n IH]; intros s x; [reflexivity|].
  rewrite !Disj_S, ren_Df, IH, ren_Num. reflexivity.
Qed.

Ltac rs2 := repeat progress (rewrite ?ren_Kf, ?ren_Df, ?ren_Qf, ?ren_Xf, ?ren_Top, ?ren_Emp, ?ren_Suc, ?ren_Opr,
  ?ren_App, ?ren_Fnc, ?ren_NatP, ?ren_Num, ?ren_Disj; cbn).
Ltac rs2in H := repeat progress (rewrite ?ren_Kf, ?ren_Df, ?ren_Qf, ?ren_Xf, ?ren_Top, ?ren_Emp, ?ren_Suc, ?ren_Opr,
  ?ren_App, ?ren_Fnc, ?ren_NatP, ?ren_Num, ?ren_Disj in H; cbn in H).

(* a fact of the outer context, carried under one or two new binders *)
Lemma D_sh1 G a f : D G f -> D (a :: map (ren S) G) (ren S f).
Proof. intros H. apply (D_weak (map (ren S) G)); [intros g Hg; right; exact Hg|]. apply D_ren. exact H. Qed.
Lemma D_sh2 G a b f : D G f -> D (a :: b :: map (ren S) G) (ren S f).
Proof. intros H. apply (D_weak (map (ren S) G)); [intros g Hg; right; right; exact Hg|]. apply D_ren. exact H. Qed.
Lemma D_sh0 G f : D G f -> D (map (ren S) G) (ren S f).
Proof. apply D_ren. Qed.
Lemma D_add G a f : D G f -> D (a :: G) f.
Proof. intros H. apply (D_weak G); [intros g Hg; right; exact Hg|exact H]. Qed.

Ltac sh1 H := let H' := fresh in pose proof (D_sh1 _ _ _ H) as H'; rs2in H'; clear H; rename H' into H.

(* ---- single facts in context, from the replay and the definitions *)
Lemma D_Emp_nomem G x d : D G (Emp x) -> D G (Neg (Mem d x)).
Proof.
  intros H. pose proof (D_iffl _ _ _ (D_thm _ _ (U_Emp x)) H) as H2.
  pose proof (D_inst _ _ d H2) as H3. simpl in H3. exact H3.
Qed.

Lemma D_Suc_mem G s y d : D G (Suc s y) -> D G (Qf (Mem d s) (Df (Mem d y) (Eqv d y))).
Proof.
  intros H. pose proof (D_iffl _ _ _ (D_thm _ _ (U_Suc s y)) H) as H2.
  pose proof (D_inst _ _ d H2) as H3. rsin H3. exact H3.
Qed.

Lemma D_Suc_intro G s y : D (map (ren S) G) (Qf (Mem 0 (S s)) (Df (Mem 0 (S y)) (Eqv 0 (S y)))) -> D G (Suc s y).
Proof. intros H. apply (D_iffr _ _ _ (D_thm _ _ (U_Suc s y))). apply D_all. exact H. Qed.

Lemma D_App_E G f x y : D G (App f x y) -> D G (Xf (Kf (Mem 0 (S f)) (Opr 0 (S x) (S y)))).
Proof. intros H. exact (D_iffl _ _ _ (D_thm _ _ (U_App f x y)) H). Qed.

Lemma D_EmpUq G a b : D G (Emp a) -> D G (Emp b) -> D G (Eqv a b).
Proof. intros H1 H2. exact (D_t1 _ _ _ (F_EmpUq a b) (D_and _ _ _ H1 H2)). Qed.
Lemma D_SucUq G a b c : D G (Suc a c) -> D G (Suc b c) -> D G (Eqv a b).
Proof. intros H1 H2. exact (D_t1 _ _ _ (F_SucUq a b c) (D_and _ _ _ H1 H2)). Qed.
Lemma D_SucInj G a b c : D G (Suc a b) -> D G (Suc a c) -> D G (Eqv b c).
Proof. intros H1 H2. exact (D_t1 _ _ _ (F_SucInj a b c) (D_and _ _ _ H1 H2)). Qed.
Lemma D_NoSelf G x c : D G (Mem x x) -> D G c.
Proof. intros H. exact (D_absurd _ _ _ H (D_thm _ _ (F_NoSelf x))). Qed.
Lemma D_NoTwo G x y c : D G (Mem x y) -> D G (Mem y x) -> D G c.
Proof. intros H1 H2. exact (D_absurd _ _ _ (D_and _ _ _ H1 H2) (D_thm _ _ (F_NoTwo x y))). Qed.
Lemma D_Kur1 G a b c d e : D G (Opr a b c) -> D G (Opr a d e) -> D G (Eqv b d).
Proof. intros H1 H2. exact (D_t1 _ _ _ (F_Kur1 a b c d e) (D_and _ _ _ H1 H2)). Qed.
Lemma D_Kur2 G a b c d e : D G (Opr a b c) -> D G (Opr a d e) -> D G (Eqv c e).
Proof. intros H1 H2. exact (D_t1 _ _ _ (F_Kur2 a b c d e) (D_and _ _ _ H1 H2)). Qed.
Lemma D_MemApp G f a b d : D G (Mem d f) -> D G (Opr d a b) -> D G (App f a b).
Proof. intros H1 H2. exact (D_t1 _ _ _ (F_MemApp f a b d) (D_and _ _ _ H1 H2)). Qed.
Lemma D_FncApp G f a b c : D G (Fnc f) -> D G (App f a b) -> D G (App f a c) -> D G (Eqv b c).
Proof. intros H1 H2 H3. exact (D_t2 _ _ _ _ (F_FncApp f a b c) H1 (D_and _ _ _ H2 H3)). Qed.

(* Leibniz for the numeral formula *)
Lemma D_Num_eq G n x y : D G (Eqv x y) -> D G (Num n x) -> D G (Num n y).
Proof.
  intros H1 H2. pose proof (D_leib G (Num n 0) x y H1) as L. rewrite !ren_Num in L. simpl in L. exact (L H2).
Qed.

(* ---- existence and uniqueness of N_n *)
Lemma NumEx n : Pv (Xf (Num n 0)).
Proof.
  induction n as [|n IH]; [exact F_EmpEx|]. apply D_nil.
  apply (D_exE [] _ _ (D_thm _ _ IH)). rs2.
  apply (D_exE _ (Suc 0 1)); [apply D_thm; exact (F_SucEx 0)|]. rs2. rewrite Num_S.
  apply (D_exI _ _ 0). rs2. apply (D_exI _ _ 1). rs2.
  apply D_and; hyp.
Qed.

Lemma D_NumEx G n : D G (Xf (Num n 0)).
Proof. apply D_thm. apply NumEx. Qed.

Lemma NumUq n : forall G x y, D G (Num n x) -> D G (Num n y) -> D G (Eqv x y).
Proof.
  induction n as [|n IH]; intros G x y Hx Hy.
  - exact (D_EmpUq _ _ _ Hx Hy).
  - rewrite Num_S in Hx, Hy.
    apply (D_exE2 _ _ _ _ Hx). rs2.
    pose proof (D_sh2 _ (Num n 0) (Suc (S x) 0) _ Hy) as Hy'. rs2in Hy'.
    apply (D_exE2 _ _ _ _ Hy'). rs2.
    have E (Eqv 1 0). { apply IH; hyp. }
    have S1 (Suc (S (S x)) 0).
    { pose proof (D_leib _ (Suc (S (S (S x))) 0) 1 0 E) as L. rs2in L. apply L. hyp. }
    exact (D_SucUq _ _ _ _ S1 ltac:(hyp)).
Qed.

(* ---- the members of N_n *)
Lemma DisjI n k x : k < n -> Pv (Imp (Num k x) (Disj n x)).
Proof.
  induction n as [|n IH]; intros Hk; [lia|]. rewrite Disj_S.
  destruct (Nat.eq_dec k n) as [->|Ne]; [pt|].
  apply (pmp _ _ (IH ltac:(lia))). pt.
Qed.

Lemma DisjE n x G c : (forall k, k < n -> D (Num k x :: G) c) -> D (Disj n x :: G) c.
Proof.
  induction n as [|n IH]; intros H.
  - rewrite Disj_0. apply (D_absurd _ Top); [apply D_thm; exact Top_pv|hyp].
  - rewrite Disj_S. apply (D_orE _ (Disj n x) (Num n x)); [hyp| |].
    + apply (D_weak (Disj n x :: G)); [intros g Hg; simpl in Hg |- *; tauto|].
      apply IH. intros k Hk. apply H. lia.
    + apply (D_weak (Num n x :: G)); [intros g Hg; simpl in Hg |- *; tauto|]. apply H. lia.
Qed.

Lemma MemChar n : forall G x y, D G (Num n y) -> D G (Qf (Mem x y) (Disj n x)).
Proof.
  induction n as [|n IH]; intros G x y Hy.
  - rewrite Disj_0. rewrite Num_0 in Hy. pose proof (D_Emp_nomem _ _ x Hy) as H.
    apply D_iffi; [apply (D_absurd _ (Mem x y)); [hyp|apply D_add; exact H]|].
    apply (D_absurd _ Top); [apply D_thm; exact Top_pv|hyp].
  - rewrite Num_S in Hy. apply (D_exE2 _ _ _ _ Hy). rs2. rewrite Disj_S. rs2.
    set (G1 := Num n 0 :: Suc (S y) 0 :: map (ren S) G).
    assert (I1 : D G1 (Qf (Mem (S x) 0) (Disj n (S x)))) by (apply IH; unfold G1; hyp).
    assert (I2 : D G1 (Qf (Mem (S x) (S y)) (Df (Mem (S x) 0) (Eqv (S x) 0))))
      by (apply D_Suc_mem; unfold G1; hyp).
    assert (I3 : D G1 (Qf (Eqv (S x) 0) (Num n (S x)))).
    { apply D_iffi.
      - apply (D_Num_eq _ n 0 (S x)); [apply D_sym; hyp|]. apply D_add. unfold G1. hyp.
      - apply (NumUq n); [hyp|]. apply D_add. unfold G1. hyp. }
    dt3 I1 I2 I3.
Qed.

(* ---- membership and equality of numerals *)
Lemma NumIn k n G x y : k < n -> D G (Num k x) -> D G (Num n y) -> D G (Mem x y).
Proof.
  intros Hk Hx Hy. apply (D_iffr _ _ _ (MemChar n G x y Hy)). exact (D_t1 _ _ _ (DisjI n k x Hk) Hx).
Qed.

Lemma NumDist k n G x c : k < n -> D G (Num k x) -> D G (Num n x) -> D G c.
Proof. intros Hk Hk' Hn. apply (D_NoSelf _ x). exact (NumIn k n G x x Hk Hk' Hn). Qed.

Lemma NumNe k n G x y : k <> n -> D G (Num k x) -> D G (Num n y) -> D G (Neg (Eqv x y)).
Proof.
  intros Hkn Hx Hy. apply D_negI.
  assert (Hy' : D (Eqv x y :: G) (Num k y)) by (apply (D_Num_eq _ k x y); [hyp|apply D_add; exact Hx]).
  destruct (Nat.lt_ge_cases k n) as [L|L].
  - exact (NumDist k n _ y _ L Hy' (D_add _ _ _ Hy)).
  - exact (NumDist n k _ y _ ltac:(lia) (D_add _ _ _ Hy) Hy').
Qed.

Lemma NumNotIn k n G x y : n <= k -> D G (Num k x) -> D G (Num n y) -> D G (Neg (Mem x y)).
Proof.
  intros Hkn Hx Hy. apply D_negI.
  assert (Hd : D (Mem x y :: G) (Disj n x)) by (apply (D_iffl _ (Mem x y)); [apply D_add; apply MemChar; exact Hy|hyp]).
  apply (D_cut _ _ _ Hd). apply DisjE. intros j Hj.
  apply (NumDist j k _ x _ ltac:(lia)); [hyp|]. apply D_add. apply D_add. exact Hx.
Qed.
