(* Sub3.v - SUB for every pure formula, every hole and every pair of variables. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Use Sub Inv2 Sub2.
Import ListNotations.
Open Scope nat_scope.

Lemma sub_back_gen F G H A B (sg : nat -> nat) h s t : (forall i, free i F = true -> i <> H -> sg i <> sg H) ->
  ren sg F = G -> sg H = h -> sg A = s -> sg B = t -> prov Gam (SUBf vz F H A B) -> prov Gam (SUBf vz G h s t).
Proof.
  intros Hi E EH EA EB D.
  assert (R : ren (up sg) (SUBf vz F H A B) = SUBf vz G h s t) by (rewrite (SUB_ren vz F H A B sg Hi), E, EH, EA, EB; reflexivity).
  rewrite <- R. apply prov_Gam_ren. exact D.
Qed.

Lemma back_other j : backs 0 0 0 (6 + j) = j.
Proof. unfold backs. replace (6 + j) with (S (S (S (3 + j)))) by lia. lia. Qed.

Lemma backs_ge s t h j : backs s t h (6 + j) = j.
Proof. unfold backs. replace (6 + j) with (S (S (S (3 + j)))) by lia. lia. Qed.

Section S.
Hypothesis K : KERNEL.

Ltac kt n := apply (useK K n); vm_compute; reflexivity.

(* the hole moved to argument 0: the template's result renamed back is the formula itself *)
Lemma hm_back h s t (f : form) : ren (backs s t h) (ren (inst_args [2] sh6) (ren (hm h) f)) = f.
Proof.
  rewrite !ren_comp. apply ren_id'. intros i. unfold hm, inst_args, sh6.
  destruct (i =? h) eqn:E; simpl.
  - apply Nat.eqb_eq in E. auto.
  - rewrite Nat.sub_0_r. exact (backs_ge s t h i).
Qed.

Lemma hm_free h s t (f : form) i : free i (ren (inst_args [2] sh6) (ren (hm h) f)) = true -> i <> 2 -> backs s t h i <> h.
Proof.
  intros Fi N2. rewrite ren_comp in Fi. apply free_ren in Fi as [j [Fj Ej]].
  unfold hm, inst_args in Ej. destruct (j =? h) eqn:Ejh; simpl in Ej; [congruence|].
  apply Nat.eqb_neq in Ejh. unfold sh6 in Ej. rewrite Nat.sub_0_r in Ej. subst i. intros C. apply Ejh. rewrite <- (backs_ge s t h j). exact C.
Qed.

Lemma hmA_back h s t (f : form) : ren (up (backs s t h)) (ren (inst_args [0; 3] (fun j => S (sh6 j))) (ren (hmA h) f)) = f.
Proof.
  rewrite !ren_comp. apply ren_id'. intros [|k]; unfold hmA, inst_args, sh6; simpl; [reflexivity|].
  destruct (k =? h) eqn:E; simpl.
  - apply Nat.eqb_eq in E. auto.
  - rewrite Nat.sub_0_r. f_equal. exact (backs_ge s t h k).
Qed.

Lemma hmA_free h s t (f : form) i : free (S i) (ren (inst_args [0; 3] (fun j => S (sh6 j))) (ren (hmA h) f)) = true ->
  i <> 2 -> backs s t h i <> h.
Proof.
  intros Fi N2. rewrite ren_comp in Fi. apply free_ren in Fi as [j [Fj Ej]].
  destruct j as [|k]; unfold hmA, inst_args in Ej; simpl in Ej; [congruence|].
  destruct (k =? h) eqn:Ekh; simpl in Ej; [congruence|]. apply Nat.eqb_neq in Ekh. unfold sh6 in Ej.
  rewrite Nat.sub_0_r in Ej. injection Ej as Ej. subst i. intros C. apply Ekh. rewrite <- (backs_ge s t h k). exact C.
Qed.

Theorem sub_all f : syms f = [] -> forall h s t, prov Gam (SUBf vz f h s t).
Proof.
  induction f; intros Hp h s t; simpl in Hp; try discriminate.
  - (* E n n0 *)
    destruct (free h (Mem n n0)) eqn:Fh; [|apply sub_nofree; [exact K|reflexivity|exact Fh]].
    simpl in Fh. destruct (n =? h) eqn:E1, (n0 =? h) eqn:E2; simpl in Fh; try discriminate.
    + apply Nat.eqb_eq in E1, E2. subst.
      apply (sub_back_gen (Mem 2 2) _ 2 0 1 (fun i => match i with 0 => s | 1 => t | _ => h end));
        [|reflexivity|reflexivity|reflexivity|reflexivity|apply prov_nohyp; kt "TplSe3"].
      intros i Fi N2; unfold free in Fi; apply orb_true_iff in Fi as [Fi|Fi]; apply Nat.eqb_eq in Fi; congruence.
    + apply Nat.eqb_eq in E1. apply Nat.eqb_neq in E2. subst.
      apply (sub_back_gen (Mem 3 2) _ 3 0 1 (fun i => match i with 0 => s | 1 => t | 2 => n0 | _ => h end));
        [|reflexivity|reflexivity|reflexivity|reflexivity|apply prov_nohyp; kt "TplSe1"].
      intros i Fi N3; unfold free in Fi; apply orb_true_iff in Fi as [Fi|Fi]; apply Nat.eqb_eq in Fi; subst; [congruence|simpl; auto].
    + apply Nat.eqb_neq in E1. apply Nat.eqb_eq in E2. subst.
      apply (sub_back_gen (Mem 2 3) _ 3 0 1 (fun i => match i with 0 => s | 1 => t | 2 => n | _ => h end));
        [|reflexivity|reflexivity|reflexivity|reflexivity|apply prov_nohyp; kt "TplSe2"].
      intros i Fi N3; unfold free in Fi; apply orb_true_iff in Fi as [Fi|Fi]; apply Nat.eqb_eq in Fi; subst; [simpl; auto|congruence].
  - (* = n n0 *)
    destruct (free h (Eqv n n0)) eqn:Fh; [|apply sub_nofree; [exact K|reflexivity|exact Fh]].
    simpl in Fh. destruct (n =? h) eqn:E1, (n0 =? h) eqn:E2; simpl in Fh; try discriminate.
    + apply Nat.eqb_eq in E1, E2. subst.
      apply (sub_back_gen (Eqv 2 2) _ 2 0 1 (fun i => match i with 0 => s | 1 => t | _ => h end));
        [|reflexivity|reflexivity|reflexivity|reflexivity|apply prov_nohyp; kt "TplSq3"].
      intros i Fi N2; unfold free in Fi; apply orb_true_iff in Fi as [Fi|Fi]; apply Nat.eqb_eq in Fi; congruence.
    + apply Nat.eqb_eq in E1. apply Nat.eqb_neq in E2. subst.
      apply (sub_back_gen (Eqv 3 2) _ 3 0 1 (fun i => match i with 0 => s | 1 => t | 2 => n0 | _ => h end));
        [|reflexivity|reflexivity|reflexivity|reflexivity|apply prov_nohyp; kt "TplSq1"].
      intros i Fi N3; unfold free in Fi; apply orb_true_iff in Fi as [Fi|Fi]; apply Nat.eqb_eq in Fi; subst; [congruence|simpl; auto].
    + apply Nat.eqb_neq in E1. apply Nat.eqb_eq in E2. subst.
      apply (sub_back_gen (Eqv 2 3) _ 3 0 1 (fun i => match i with 0 => s | 1 => t | 2 => n | _ => h end));
        [|reflexivity|reflexivity|reflexivity|reflexivity|apply prov_nohyp; kt "TplSq2"].
      intros i Fi N3; unfold free in Fi; apply orb_true_iff in Fi as [Fi|Fi]; apply Nat.eqb_eq in Fi; subst; [simpl; auto|congruence].
  - (* N f *)
    destruct (free h (Neg f)) eqn:Fh; [|apply sub_nofree; [exact K|exact Hp|exact Fh]].
    set (l := [(uc, ren (hm h) f)]). assert (O : otau l uc = Some (ren (hm h) f)) by reflexivity.
    assert (C : psub (otau l) sh6 (Neg (Pr uc [2])) = Neg (ren (inst_args [2] sh6) (ren (hm h) f))) by (simpl; try rewrite O; reflexivity).
    apply (sub_back (psub (otau l) sh6 (Neg (Pr uc [2])))).
    + rewrite C. intros i Fi N2. simpl in Fi. exact (hm_free h s t f i Fi N2).
    + rewrite C. simpl. f_equal. apply hm_back.
    + rewrite <- (SUB_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l) _ 2 0 1 sh6) by (intros j; unfold sh6; lia).
      apply (instT (SUBf vz (Neg (Pr uc [2])) 2 0 1) [SUBf vz (Pr uc [2]) 2 0 1] l P7); [kt "TplSn"|apply P7_S| |apply P7_sh6].
      intros rho g Pr0 [<-|[]]. apply (hyp_SUB1 l uc f h rho O Pr0 (IHf Hp)).
  - (* I f1 f2 *)
    apply app_eq_nil in Hp as [Hp1 Hp2].
    destruct (free h (Imp f1 f2)) eqn:Fh; [|apply sub_nofree; [exact K|simpl; rewrite Hp1, Hp2; reflexivity|exact Fh]].
    set (l := [(uc, ren (hm h) f1); (ud1, ren (hm h) f2)]).
    assert (O1 : otau l uc = Some (ren (hm h) f1)) by reflexivity. assert (O2 : otau l ud1 = Some (ren (hm h) f2)) by reflexivity.
    assert (C : psub (otau l) sh6 (Imp (Pr uc [2]) (Pr ud1 [2])) =
                Imp (ren (inst_args [2] sh6) (ren (hm h) f1)) (ren (inst_args [2] sh6) (ren (hm h) f2)))
      by (simpl; try rewrite O1; try rewrite O2; reflexivity).
    apply (sub_back (psub (otau l) sh6 (Imp (Pr uc [2]) (Pr ud1 [2])))).
    + rewrite C. intros i Fi N2. simpl in Fi. apply orb_true_iff in Fi as [Fi|Fi];
        [exact (hm_free h s t f1 i Fi N2)|exact (hm_free h s t f2 i Fi N2)].
    + rewrite C. simpl. f_equal; apply hm_back.
    + rewrite <- (SUB_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l) _ 2 0 1 sh6) by (intros j; unfold sh6; lia).
      apply (instT (SUBf vz (Imp (Pr uc [2]) (Pr ud1 [2])) 2 0 1) [SUBf vz (Pr uc [2]) 2 0 1; SUBf vz (Pr ud1 [2]) 2 0 1] l P7);
        [kt "TplSi"|apply P7_S| |apply P7_sh6].
      intros rho g Pr0 [<-|[<-|[]]].
      * apply (hyp_SUB1 l uc f1 h rho O1 Pr0 (IHf1 Hp1)).
      * apply (hyp_SUB1 l ud1 f2 h rho O2 Pr0 (IHf2 Hp2)).
  - (* A f *)
    destruct (free h (All f)) eqn:Fh; [|apply sub_nofree; [exact K|exact Hp|exact Fh]].
    set (l := [(uc2, ren (hmA h) f)]). assert (O : otau l uc2 = Some (ren (hmA h) f)) by reflexivity.
    destruct (inv_all K f Hp) as (Ex & _ & _).
    assert (C : psub (otau l) sh6 (All (Pr uc2 [0; 3])) = All (ren (inst_args [0; 3] (fun j => S (sh6 j))) (ren (hmA h) f)))
      by (simpl; try rewrite O; reflexivity).
    apply (sub_back (psub (otau l) sh6 (All (Pr uc2 [0; 3])))).
    + rewrite C. intros i Fi N2. simpl in Fi. exact (hmA_free h s t f i Fi N2).
    + rewrite C. simpl. f_equal. apply hmA_back.
    + rewrite <- (SUB_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l) _ 2 0 1 sh6) by (intros j; unfold sh6; lia).
      apply (instT (SUBf vz (All (Pr uc2 [0; 3])) 2 0 1) [EXf (V (Pr uc2 [0; 1])); SUBf vz (Pr uc2 [2; 3]) 3 0 1] l P7);
        [kt "TplSa"|apply P7_S| |apply P7_sh6].
      intros rho g Pr0 [<-|[<-|[]]].
      * apply (hyp_EX l uc2 (ren (hmA h) f) [0; 1] rho O Pr0). unfold V. rewrite EX_ren. apply prov_Gam_ren. exact Ex.
      * apply (hyp_SUB2 l uc2 f h rho O Pr0 (IHf Hp)).
Qed.
End S.
