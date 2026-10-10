(* L2RDefR4.v - lane L2R recovery 4 (same text as L2RDef.v, whose .vo was cut by the 19:30 outage), 2026-10-09. DEFsep of L2RSepL.v from the closure of M under Delta_0 separation:
     DSEP0 psi n: for z and the parameters in M, {x in z : psi(x, z, p)} is an element of M, psi a Delta_0 formula
                  (Abs2.d0: membership, equality, not, implies, bounded universals).
   g relativized to a set u is Delta_0 for every pure g (relU_d0), and u, z are elements of M (SIN, SSUB), so
     defsep_from_dsep0 : SIN, SSUB, DSEP0 -> DEFsep g n for every pure g.
   With L2RRefl.v: Separation and Collection relativized to M follow from the single statements STR, SSUB, SIN, SCOV
   and the two schemas GREFL (reflection) and DSEP0 (Delta_0 separation). *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
From Cohen Require Import Syn Prov Kal Ax Checks Replay Expand Pure Elim.
From LCH Require Import Rel2 GoedelCH Abs2.
From L2R Require Import L2RLogicA L2RSepL L2RRefl.
Import ListNotations.
Open Scope nat_scope.

Lemma relU_d0 g : syms g = [] -> forall w, d0 (relU w g).
Proof.
  induction g; intros Hg w; simpl in *.
  - apply d0_mem.
  - apply d0_eq.
  - discriminate.
  - apply d0_neg. apply IHg. exact Hg.
  - apply app_eq_nil in Hg as [H1 H2]. apply d0_imp; [apply IHg1; exact H1|apply IHg2; exact H2].
  - apply d0_ball. apply IHg. exact Hg.
Qed.

Section D.
Variable M : form.
Hypothesis HM : closedk 1 M = true.
Variable Lev : form.
Hypothesis HL : closedk 1 Lev = true.
Notation ZF := ZFpure.

(* z = variable 0, the parameters 1 .. n; inside exists y forall x: x = 0, y = 1, z = 2, parameter i = i + 3 *)
Definition DSEP0 (psi : form) (n : nat) : Prop :=
  prov ZF (chain (G M (S n)) (Xf (Kf M (All (Qf (Mem 0 1) (Kf (Mem 0 2) (ren sigS psi))))))).

Definition swp (t : nat) : nat := match t with 0 => 1 | 1 => 0 | t => t end.
(* g's x = 0, z = 1 stay; its parameter i (= 2 + i) moves to 3 + i, past the variable 2 that holds u *)
Definition kap (t : nat) : nat := match t with 0 => 0 | 1 => 1 | S (S t') => S (S (S t')) end.

Lemma closedk_ren_le f : forall k k' s, closedk k f = true -> (forall i, i < k -> s i < k') -> closedk k' (ren s f) = true.
Proof.
  intros k k' s H Hs. apply free_closedk. intros i Fi.
  pose proof (free_ren f) as FR. apply Sub.free_ren in Fi. destruct Fi as [j [Fj <-]].
  apply Hs. exact (closedk_free _ _ _ H Fj).
Qed.

Lemma closedk_relU f : forall k w, closedk k f = true -> w < k -> closedk k (relU w f) = true.
Proof.
  induction f; intros k w H Hw; simpl in *; try exact H.
  - apply IHf; assumption.
  - apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split; [apply IHf1|apply IHf2]; assumption.
  - repeat (apply andb_true_iff; split); try (apply Nat.ltb_lt; lia). apply IHf; [exact H|lia].
Qed.

Theorem defsep_from_dsep0 : prov ZF (SIN M Lev) -> prov ZF (SSUB M Lev) ->
  (forall psi n, d0 psi -> closedk (S (S n)) psi = true -> DSEP0 psi n) ->
  forall g n, syms g = [] -> closedk (S (S n)) g = true -> DEFsep M Lev g n.
Proof.
  intros Hin Hsub Hds g n Hg Hc. unfold DEFsep. rewrite chain_chainA. apply A_chain. set (G1 := G M (S n)).
  apply A_all. apply A_intro. apply A_intro.
  (* u = 0, z = 1, parameter i = i + 2 *)
  set (psi := relU 2 (ren kap g)).
  assert (Hpsi : d0 psi) by (apply relU_d0; rewrite syms_ren; exact Hg).
  assert (Hcp : closedk (S (S (S n))) psi = true).
  { apply closedk_relU; [|lia]. apply (closedk_ren_le g (S (S n))); [exact Hc|].
    intros [|[|i]] Hi; cbn; lia. }
  pose proof (A_unchain _ _ _ ltac:(rewrite <- chain_chainA; exact (Hds psi (S n) Hpsi Hcp))) as D0.
  (* D0 holds with z = 0, u = 1: swap the two; its guards are M(z), M(u) and the parameters *)
  pose proof (A_ren _ _ _ swp D0) as D1.
  haveA D2 (ren swp (Xf (Kf M (All (Qf (Mem 0 1) (Kf (Mem 0 2) (ren sigS psi))))))).
  { apply (A_ctx _ (map (ren swp) (G M (S (S n))))); [|exact D1].
    intros h Hh. unfold G in Hh. rewrite map_map in Hh. apply in_map_iff in Hh as [i [<- Hi]]. apply in_seq in Hi.
    rewrite (Mv_ren M). destruct i as [|[|i]]; cbn [swp].
    - apply A_hyp. right. right. unfold G1, G. rewrite map_map. apply in_map_iff. exists 0.
      split; [rewrite (Mv_ren M); reflexivity|apply in_seq; lia].
    - apply (A_mp _ _ Lev); [|hypA].
      apply (A_conv _ _ _ (A_inst _ _ _ 0 (A_thm _ _ _ Hin))). unfold SIN. nrm M HM Lev HL. reflexivity.
    - apply A_hyp. right. right. unfold G1, G. rewrite map_map. apply in_map_iff. exists (S i).
      split; [rewrite (Mv_ren M); reflexivity|apply in_seq; lia]. }
  apply (A_conv _ _ _ D2). unfold psi. nrm M HM Lev HL. feq.
Qed.
End D.

(* Separation relativized to M from the single statements and the two schemas *)
Theorem lsep_from_grefl_dsep0 (M : form) (HM : closedk 1 M = true) (Lev : form) (HL : closedk 1 Lev = true) :
  prov ZFpure (STR Lev) -> prov ZFpure (SSUB M Lev) -> prov ZFpure (SIN M Lev) -> prov ZFpure (SCOV M Lev) ->
  GREFL M Lev -> (forall psi n, d0 psi -> closedk (S (S n)) psi = true -> DSEP0 M psi n) -> LSEP M.
Proof.
  intros Htr Hsub Hin Hcov Hgr Hds. apply (lsep_from_grefl M HM Lev HL Htr Hcov Hgr).
  exact (defsep_from_dsep0 M HM Lev HL Hin Hsub Hds).
Qed.
