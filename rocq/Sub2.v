(* Sub2.v - SUB for every pure formula, hole and pair of variables (from the kernel's SUB templates). *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Use Sub Inv2.
Import ListNotations.
Open Scope nat_scope.

(* the hole moved to a placeholder's argument 0 (one argument), or 1 (two arguments, after the bound variable) *)
Definition hm (h i : nat) : nat := if i =? h then 0 else S i.
Definition hmA (h i : nat) : nat := match i with 0 => 0 | S k => if k =? h then 1 else S (S k) end.
(* renaming a template's result back: s t h at 0 1 2, the parameters from 6 on *)
Definition backs (s t h i : nat) : nat := match i with 0 => s | 1 => t | 2 => h | _ => i - 6 end.

Lemma sub_back F G h s t : (forall i, free i F = true -> i <> 2 -> backs s t h i <> h) -> ren (backs s t h) F = G ->
  prov Gam (SUBf vz F 2 0 1) -> prov Gam (SUBf vz G h s t).
Proof.
  intros Hi E D.
  assert (R : ren (up (backs s t h)) (SUBf vz F 2 0 1) = SUBf vz G h s t)
    by (rewrite (SUB_ren vz F 2 0 1 (backs s t h) Hi), E; reflexivity).
  rewrite <- R. apply prov_Gam_ren. exact D.
Qed.

Section S.
Hypothesis K : KERNEL.

Ltac kt n := apply (useK K n); vm_compute; reflexivity.

(* ---- SUB from the induction hypothesis at a fresh pair, renamed into a template's hypothesis *)
Lemma sub_rename g h (IH : forall h' a b, prov Gam (SUBf vz g h' a b)) (tau : nat -> nat) H :
  tau h = H -> (forall i, free i g = true -> i <> h -> tau i <> H) ->
  prov Gam (SUBf vz (ren tau g) H 0 1).
Proof.
  intros Th Hi. set (N := S (Nat.max (fvb g) h)).
  set (s' := fun i => if i =? N then 0 else if i =? S N then 1 else tau i).
  assert (Fr : forall i, free i g = true -> i < N).
  { intros i Fi. pose proof (free_fvb g i Fi). unfold N. lia. }
  assert (Sh : s' h = H). { unfold s'. assert (h <> N) by (unfold N; lia). assert (h <> S N) by (unfold N; lia).
    rewrite (proj2 (Nat.eqb_neq h N) H0), (proj2 (Nat.eqb_neq h (S N)) H1). exact Th. }
  assert (Si : forall i, free i g = true -> i <> h -> s' i <> s' h).
  { intros i Fi Ni. rewrite Sh. specialize (Fr i Fi). unfold s'.
    rewrite (proj2 (Nat.eqb_neq i N)) by lia. rewrite (proj2 (Nat.eqb_neq i (S N))) by lia. apply Hi; auto. }
  pose proof (SUB_ren vz g h N (S N) s' Si) as R.
  assert (E1 : s' N = 0) by (unfold s'; rewrite Nat.eqb_refl; reflexivity).
  assert (E2 : s' (S N) = 1) by (unfold s'; rewrite (proj2 (Nat.eqb_neq (S N) N)) by lia; rewrite Nat.eqb_refl; reflexivity).
  rewrite Sh, E1, E2 in R.
  assert (E : ren s' g = ren tau g).
  { apply ren_free. intros i Fi. specialize (Fr i Fi). unfold s'.
    rewrite (proj2 (Nat.eqb_neq i N)) by lia. rewrite (proj2 (Nat.eqb_neq i (S N))) by lia. reflexivity. }
  rewrite E in R. rewrite <- R. apply prov_Gam_ren. apply IH.
Qed.

Lemma hyp_SUB1 l p g h rho : otau l p = Some (ren (hm h) g) -> P7 rho -> (forall h' a b, prov Gam (SUBf vz g h' a b)) ->
  prov Gam (psub (vtau l) rho (SUBf vz (Pr p [2]) 2 0 1)).
Proof.
  intros Ho Hr IH. rewrite (psub_ext _ (vtau l) rho (fun j => 1 + (rho j - 1))) by (apply shift_back; exact Hr).
  rewrite (SUB_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l) (Pr p [2]) 2 0 1 (fun j => rho j - 1))
    by (intros j; specialize (Hr j); lia).
  simpl. rewrite Ho. rewrite ren_comp.
  apply (sub_rename g h IH).
  - unfold hm, inst_args. rewrite Nat.eqb_refl. reflexivity.
  - intros i Fi Ni. unfold hm, inst_args. rewrite (proj2 (Nat.eqb_neq i h) Ni). simpl. rewrite ?Nat.sub_0_r.
    specialize (Hr i). lia.
Qed.

Lemma hyp_SUB2 l p g h rho : otau l p = Some (ren (hmA h) g) -> P7 rho -> (forall h' a b, prov Gam (SUBf vz g h' a b)) ->
  prov Gam (psub (vtau l) rho (SUBf vz (Pr p [2; 3]) 3 0 1)).
Proof.
  intros Ho Hr IH. rewrite (psub_ext _ (vtau l) rho (fun j => 1 + (rho j - 1))) by (apply shift_back; exact Hr).
  rewrite (SUB_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l) (Pr p [2; 3]) 3 0 1 (fun j => rho j - 1))
    by (intros j; specialize (Hr j); lia).
  simpl. rewrite Ho. rewrite ren_comp.
  apply (sub_rename g (S h) IH).
  - unfold hmA, inst_args. rewrite Nat.eqb_refl. reflexivity.
  - intros [|k] Fi Ni; unfold hmA, inst_args; simpl; [lia|].
    assert (k <> h) by lia. rewrite (proj2 (Nat.eqb_neq k h) H). simpl. rewrite ?Nat.sub_0_r. specialize (Hr k). lia.
Qed.

Lemma sub_nofree f h s t : syms f = [] -> free h f = false -> prov Gam (SUBf vz f h s t).
Proof.
  intros Hp Fh. destruct (inv_all K f Hp) as (_ & U & _). set (l := [(ua, f)]).
  assert (O : otau l ua = Some f) by reflexivity.
  apply (sub_back (psub (otau l) sh6 PA)).
  - intros i Fi N2. simpl in Fi. try rewrite O in Fi. apply free_ren in Fi as [j [Fj Ej]].
    unfold inst_args in Ej. simpl in Ej. rewrite Nat.sub_0_r in Ej. unfold sh6 in Ej. subst i.
    unfold backs. destruct (6 + j) as [|[|[|m]]] eqn:E; try lia. intros C. replace (S (S (S m)) - 6) with j in C by lia.
    subst j. congruence.
  - simpl. try rewrite O. rewrite ren_comp. apply ren_id'. intros i. unfold backs, inst_args, sh6. simpl.
    rewrite Nat.sub_0_r. destruct (6 + i) as [|[|[|m]]] eqn:E; lia.
  - rewrite <- (SUB_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l) PA 2 0 1 sh6) by (intros j; unfold sh6; lia).
    apply (instT (SUBf vz PA 2 0 1) [UQf (V PA)] l P7); [kt "TplSo"|apply P7_S| |apply P7_sh6].
    intros rho h' Pr0 [<-|[]]. apply (hyp_UQ l ua f [] rho O Pr0 U).
Qed.
End S.
