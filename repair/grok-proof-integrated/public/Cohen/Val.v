(* Val.v - the Boolean value of a formula, as the transformer writes it (proto2.pl, body), in de Bruijn form.
   An object formula f has free variables 0, 1, ..; its value formula val f has free variables 0 = b (the value),
   1 = pp (the conditions), 2 + i = the name of the object variable i.
     E x y   VE4 b pp x y          = x y   VQ4 b pp x y
     N g     X fa K VAL(g,fa) VN3 fa b pp
     I g h   X fa X fc K K VAL(g,fa) VAL(h,fc) VI4 fa fc b pp
     A x g   A fd Q E fd b K E fd pp A x X fa K VAL(g,fa) E fd fa
     P a     vz P b pp a   (a predicate symbol P: the symbol vz P of its value; used for the placeholders)
   Symbol numbers: 0 VE4, 1 VQ4, 2 VN3, 3 VI4, 4 Rg2 (the order of the symbol table). *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
From Cohen Require Import Syn Prov.
Import ListNotations.

Definition sVE := 0. Definition sVQ := 1. Definition sVN := 2. Definition sVI := 3. Definition sRg := 4.

(* the renamings placing a part's value inside its parent's body *)
Definition rN (n : nat) : nat := match n with 0 => 0 | 1 => 2 | S (S i) => 3 + i end.
Definition rI1 (n : nat) : nat := match n with 0 => 1 | 1 => 3 | S (S i) => 4 + i end.
Definition rI0 (n : nat) : nat := match n with 0 => 0 | 1 => 3 | S (S i) => 4 + i end.
Definition rA (n : nat) : nat := match n with 0 => 0 | 1 => 4 | 2 => 1 | S (S (S i)) => 5 + i end.

Definition valN (v : form) : form := Xf (Kf (ren rN v) (Pr sVN [0; 1; 2])).
Definition valI (v w : form) : form := Xf (Xf (Kf (Kf (ren rI1 v) (ren rI0 w)) (Pr sVI [1; 0; 2; 3]))).
Definition valA (v : form) : form := All (Qf (Mem 0 1) (Kf (Mem 0 2) (All (Xf (Kf (ren rA v) (Mem 2 0)))))).

Section V.
Variable vz : nat -> nat.

Fixpoint val (f : form) : form :=
  match f with
  | Mem x y => Pr sVE [0; 1; 2 + x; 2 + y]
  | Eqv x y => Pr sVQ [0; 1; 2 + x; 2 + y]
  | Pr p a => Pr (vz p) (0 :: 1 :: map (fun x => 2 + x) a)
  | Neg g => valN (val g)
  | Imp g h => valI (val g) (val h)
  | All g => valA (val g)
  end.

(* ---- values commute with renaming: the names move with the variables *)
Lemma rN_up s n : rN (up (up s) n) = up (up (up s)) (rN n).
Proof. destruct n as [|[|n]]; reflexivity. Qed.
Lemma rI1_up s n : rI1 (up (up s) n) = up (up (up (up s))) (rI1 n).
Proof. destruct n as [|[|n]]; reflexivity. Qed.
Lemma rI0_up s n : rI0 (up (up s) n) = up (up (up (up s))) (rI0 n).
Proof. destruct n as [|[|n]]; reflexivity. Qed.
Lemma rA_up s n : rA (up (up (up s)) n) = up (up (up (up (up s)))) (rA n).
Proof. destruct n as [|[|[|n]]]; reflexivity. Qed.

Lemma val_ren (f : form) : forall s, val (ren s f) = ren (up (up s)) (val f).
Proof.
  induction f; intros s; simpl.
  - reflexivity.
  - reflexivity.
  - f_equal. simpl. rewrite !map_map. reflexivity.
  - unfold valN. rewrite IHf.
    assert (E : ren rN (ren (up (up s)) (val f)) = ren (up (up (up s))) (ren rN (val f)))
      by (rewrite !ren_comp; apply ren_ext; intros n; apply rN_up).
    unfold Xf, Kf. simpl. rewrite E. reflexivity.
  - unfold valI. rewrite IHf1, IHf2.
    assert (E1 : ren rI1 (ren (up (up s)) (val f1)) = ren (up (up (up (up s)))) (ren rI1 (val f1)))
      by (rewrite !ren_comp; apply ren_ext; intros n; apply rI1_up).
    assert (E0 : ren rI0 (ren (up (up s)) (val f2)) = ren (up (up (up (up s)))) (ren rI0 (val f2)))
      by (rewrite !ren_comp; apply ren_ext; intros n; apply rI0_up).
    unfold Xf, Kf. simpl. rewrite E1, E0. reflexivity.
  - unfold valA. rewrite IHf.
    assert (E : ren rA (ren (up (up (up s))) (val f)) = ren (up (up (up (up (up s))))) (ren rA (val f)))
      by (rewrite !ren_comp; apply ren_ext; intros n; apply rA_up).
    unfold Qf, Xf, Kf. simpl. rewrite E. reflexivity.
Qed.
End V.
