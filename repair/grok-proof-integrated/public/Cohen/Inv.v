(* Inv.v - the value invariants of the transformer's lemmas, in the kernel's shapes, over a statement context
   (0 = pp, 1 + i = the name of object variable i):
     EX   X b VAL(n,b)                          UQ   A b A c I K VAL(n,b) VAL(n,c) = b c
     RG   A b I VAL(n,b) Rg2 b pp                TOP  VAL(n,pp)  (the value is pp)
     SUB  A e A b A c I K K VQ4 e pp s t VAL(n[s/h],b) VAL(n[t/h],c) A d I K E d e E d b E d c
   and their behaviour under renaming and under the substitution of formulas for placeholder symbols. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
From Cohen Require Import Syn Prov Val.
Import ListNotations.

Definition u1 (n : nat) : nat := match n with 0 => 1 | S m => S (S m) end.
Definition EXf (v : form) : form := Xf v.
Definition UQf (v : form) : form := All (All (Imp (Kf (ren u1 v) (ren (up S) v)) (Eqv 1 0))).
Definition RGf (v : form) : form := All (Imp v (Pr sRg [0; 1])).
Definition TOPf (v : form) : form := ren Nat.pred v.

Definition sv (h s : nat) : nat -> nat := fun i => if i =? h then s else i.
Definition w1 (n : nat) : nat := match n with 0 => 1 | 1 => 3 | S (S i) => 4 + i end.
Definition w0 (n : nat) : nat := match n with 0 => 0 | 1 => 3 | S (S i) => 4 + i end.

Section I.
Variable vz : nat -> nat.

Definition SUBf (f : form) (h s t : nat) : form :=
  All (All (All (Imp (Kf (Kf (Pr sVQ [2; 3; 4 + s; 4 + t]) (ren w1 (val vz (ren (sv h s) f))))
                        (ren w0 (val vz (ren (sv h t) f))))
                   (All (Imp (Kf (Mem 0 3) (Mem 0 2)) (Mem 0 1)))))).

(* ---- renaming the object variables *)
Lemma EX_ren f s : EXf (val vz (ren s f)) = ren (up s) (EXf (val vz f)).
Proof. unfold EXf, Xf. simpl. rewrite val_ren. reflexivity. Qed.

Lemma UQ_ren f s : UQf (val vz (ren s f)) = ren (up s) (UQf (val vz f)).
Proof.
  unfold UQf, Kf. simpl. rewrite val_ren. rewrite !ren_comp. f_equal. f_equal. f_equal. f_equal. f_equal.
  - apply ren_ext. intros [|[|n]]; reflexivity.
  - f_equal. apply ren_ext. intros [|[|n]]; reflexivity.
Qed.

Lemma RG_ren f s : RGf (val vz (ren s f)) = ren (up s) (RGf (val vz f)).
Proof. unfold RGf. simpl. rewrite val_ren. reflexivity. Qed.

Lemma TOP_ren f s : TOPf (val vz (ren s f)) = ren (up s) (TOPf (val vz f)).
Proof. unfold TOPf. rewrite val_ren, !ren_comp. apply ren_ext. intros [|[|n]]; reflexivity. Qed.

(* ---- substitution: formulas for placeholder symbols at the object level, their values at the value level *)
Variable tau tau' : nat -> option form.
Hypothesis Hsym : forall p, tau' (vz p) = option_map (val vz) (tau p).
Hypothesis Hbase : tau' sVE = None /\ tau' sVQ = None /\ tau' sVN = None /\ tau' sVI = None /\ tau' sRg = None.

Lemma val_psub (f : form) : forall rho, val vz (psub tau rho f) = psub tau' (fun j => 2 + rho j) (val vz f).
Proof.
  destruct Hbase as (HE & HQ & HN & HI & HR).
  induction f; intros rho; simpl.
  - rewrite HE. reflexivity.
  - rewrite HQ. reflexivity.
  - rewrite Hsym. destruct (tau n) as [th|]; simpl.
    + rewrite val_ren. apply ren_ext. intros [|[|i]]; try reflexivity. simpl.
      unfold inst_args. simpl. rewrite length_map.
      destruct (i <? length l) eqn:E.
      * apply Nat.ltb_lt in E. replace (S (S i) <? S (S (length l))) with true by (symmetry; apply Nat.ltb_lt; lia).
        pose proof (map_nth (fun x : nat => S (S x)) l 0 i) as M. simpl in M.
        rewrite (nth_indep (map (fun x : nat => S (S x)) l) 0 2) by (rewrite length_map; exact E). rewrite M. reflexivity.
      * replace (S (S i) <? S (S (length l))) with false by (symmetry; apply Nat.ltb_ge; apply Nat.ltb_ge in E; lia).
        replace (S (S i) - S (S (length l))) with (i - length l) by lia. reflexivity.
    + reflexivity.
  - unfold valN, Xf, Kf. simpl. rewrite HN. rewrite IHf, ren_psub. reflexivity.
  - unfold valI, Xf, Kf. simpl. rewrite HI. rewrite IHf1, IHf2, !ren_psub. reflexivity.
  - unfold valA, Qf, Xf, Kf. simpl. rewrite IHf, ren_psub.
    reflexivity.
Qed.

Lemma EX_psub f rho : EXf (val vz (psub tau rho f)) = psub tau' (fun j => 1 + rho j) (EXf (val vz f)).
Proof. unfold EXf, Xf. simpl. rewrite val_psub. reflexivity. Qed.

Lemma UQ_psub f rho : UQf (val vz (psub tau rho f)) = psub tau' (fun j => 1 + rho j) (UQf (val vz f)).
Proof.
  unfold UQf, Kf. simpl. rewrite val_psub, !ren_psub. reflexivity.
Qed.

Lemma RG_psub f rho : RGf (val vz (psub tau rho f)) = psub tau' (fun j => 1 + rho j) (RGf (val vz f)).
Proof.
  destruct Hbase as (HE & HQ & HN & HI & HR).
  unfold RGf. simpl. rewrite val_psub, HR. reflexivity.
Qed.

Lemma TOP_psub f rho : TOPf (val vz (psub tau rho f)) = psub tau' (fun j => 1 + rho j) (TOPf (val vz f)).
Proof. unfold TOPf. rewrite val_psub, ren_psub. apply psub_ext. intros j. reflexivity. Qed.
End I.
