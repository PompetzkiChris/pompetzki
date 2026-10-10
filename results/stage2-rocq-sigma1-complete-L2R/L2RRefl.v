(* L2RRefl.v - lane L2R round 2, 2026-10-09. The reflection hypotheses of L2RSepL.v (REFLsep, REFLcoll) derived from
   one schema in the standard form of the reflection principle for the hierarchy of levels:
     GREFL L n: for parameters p_0 .. p_(n-1) in M and every level u0 there is a level u containing u0 that reflects
                every formula of the finite list L, each (m, phi) uniformly in its first m variables:
                forall x_0 .. x_(m-1) in u (phi^M(x, p) <-> phi^u(x, p)).
   and one more single statement
     SCOV  every element of M lies in a level: forall z (M z -> exists u (Lev u & z in u)).
   lsep_from_grefl : STR, SCOV, GREFL, DEFsep -> LSEP M
   lcoll_from_grefl: STR, SSUB, SIN, SCOV, GREFL -> LCOLL M *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
From Cohen Require Import Syn Prov Kal Ax Checks Replay Expand Pure Elim.
From LCH Require Import Rel2 GoedelCH.
From L2R Require Import L2RLogicA L2RSepL.
Import ListNotations.
Open Scope nat_scope.

(* k quantifiers bounded by the set held by w (w as seen outside them) *)
Fixpoint wrapQ (w k : nat) (b : form) : form :=
  match k with 0 => b | S k' => All (Imp (Mem 0 (S w)) (wrapQ (S w) k' b)) end.

(* u0 subset of u: forall d (d in u0 -> d in u) *)
Definition Sub (a b : nat) : form := All (Imp (Mem 0 (S a)) (Mem 0 (S b))).

(* the source form of a formula: variables below m uniform, m .. the parameters; inside forall u0 exists u and the m
   bounded quantifiers the parameters move up by two *)
Definition shm (m : nat) (t : nat) : nat := if t <? m then t else S (S t).

Section R.
Variable M : form.
Hypothesis HM : closedk 1 M = true.
Variable Lev : form.
Hypothesis HL : closedk 1 Lev = true.
Notation ZF := ZFpure.

Definition RF1 (c : nat * form) : form :=
  match c with (m, phi) => wrapQ 0 m (Qf (rel M (ren (shm m) phi)) (relU m (ren (shm m) phi))) end.
Fixpoint RFs (L : list (nat * form)) : form :=
  match L with [] => Top | c :: r => Kf (RF1 c) (RFs r) end.

Definition GREFL : Prop := forall (L : list (nat * form)) (n : nat),
  (forall c, In c L -> syms (snd c) = [] /\ closedk (fst c + n) (snd c) = true) ->
  prov ZF (chain (G M n) (All (Imp Lev (Xf (Kf (Kf Lev (Sub 1 0)) (RFs L)))))).

Definition SCOV : form := All (Imp M (Xf (Kf Lev (Mem 1 0)))).

Lemma Sub_use G a b x : DA ZF G (Sub a b) -> DA ZF G (Mem x a) -> DA ZF G (Mem x b).
Proof.
  intros H1 H2. pose proof (A_inst _ _ _ x H1) as H. cbn [ren up scons sid] in H. unfold sid in H. exact (A_mp _ _ _ _ H H2).
Qed.

Lemma ren_Sub s a b : ren s (Sub a b) = Sub (s a) (s b). Proof. reflexivity. Qed.

Lemma reflsep_from_grefl g n : syms g = [] -> closedk (S (S n)) g = true -> prov ZF SCOV -> GREFL ->
  REFLsep M Lev g n.
Proof.
  intros Hg Hc Hcov Hgr. unfold REFLsep. rewrite chain_chainA. apply A_chain. set (G1 := G M (S n)).
  pose proof (A_unchain _ _ _ ltac:(rewrite <- chain_chainA; exact (Hgr [(1, g)] (S n)
    ltac:(intros c [<-|[]]; split; [exact Hg|exact Hc])))) as GR.
  haveA H0 (Xf (Kf Lev (Mem 1 0))).
  { pose proof (A_inst _ _ _ 0 (A_thm _ G1 _ Hcov)) as T. unfold SCOV in T.
    apply (A_mp _ _ M); [apply (A_conv _ _ _ T); nrm M HM Lev HL; reflexivity|].
    unfold G1. rewrite G_S, (Mv0 M HM). hypA. }
  apply (A_exE2 _ _ _ _ _ H0). nrmg M HM Lev HL.
  (* u0 = 0, z = 1 *)
  pose proof (A_sh2 _ Lev (Mem 1 0) _ GR) as GR1. apply (A_inst _ _ _ 0) in GR1.
  assert (GR2 : DA ZF (Lev :: Mem 1 0 :: map (ren S) G1)
    (Imp Lev (Xf (Kf (Kf Lev (Sub 1 0)) (Kf (All (Imp (Mem 0 1) (Qf (rel M (ren (fun t => match t with 0 => 0 | S t' => S (S (S t')) end) g))
       (relU 1 (ren (fun t => match t with 0 => 0 | S t' => S (S (S t')) end) g))))) Top))))).
  { apply (A_conv _ _ _ GR1). unfold RFs, RF1, wrapQ. nrm M HM Lev HL. feq. }
  pose proof (A_mp _ _ _ _ GR2 ltac:(hypA)) as GR3.
  apply (A_exE2 _ _ _ _ _ GR3). nrmg M HM Lev HL.
  (* u = 0, u0 = 1, z = 2 *)
  apply (A_exI _ _ _ 0). nrmg M HM Lev HL.
  haveA HU (Kf Lev (Sub 1 0)). { hypA. }
  apply A_and; [apply A_and|].
  - exact (A_andl _ _ _ _ HU).
  - apply (Sub_use _ 1 0 2 (A_andr _ _ _ _ HU)). hypA.
  - haveA HR (Kf (All (Imp (Mem 0 1) (Qf (rel M (ren (fun t => match t with 0 => 0 | S t' => S (S (S t')) end) g))
       (relU 1 (ren (fun t => match t with 0 => 0 | S t' => S (S (S t')) end) g))))) Top). { hypA. }
    apply (A_conv _ _ _ (A_andl _ _ _ _ HR)). nrm M HM Lev HL. feq.
Qed.

Definition kap2 (t : nat) : nat := match t with 0 => 0 | 1 => 1 | S (S t') => S (S (S (S t'))) end.

Lemma closedk_Xf k a : closedk k (Xf a) = closedk (S k) a. Proof. reflexivity. Qed.

Lemma reflcoll_from_grefl g n : syms g = [] -> closedk (S (S (S n))) g = true -> prov ZF SCOV -> GREFL ->
  REFLcoll M Lev g n.
Proof.
  intros Hg Hc Hcov Hgr. unfold REFLcoll. rewrite chain_chainA. apply A_chain. set (G1 := G M (S n)).
  pose proof (A_unchain _ _ _ ltac:(rewrite <- chain_chainA; exact (Hgr [(2, g); (1, Xf g)] (S n)
    ltac:(intros c [<-|[<-|[]]]; split; [exact Hg|exact Hc|unfold Xf; simpl; exact Hg|
      simpl; exact Hc])))) as GR.
  haveA H0 (Xf (Kf Lev (Mem 1 0))).
  { pose proof (A_inst _ _ _ 0 (A_thm _ G1 _ Hcov)) as T. unfold SCOV in T.
    apply (A_mp _ _ M); [apply (A_conv _ _ _ T); nrm M HM Lev HL; reflexivity|].
    unfold G1. rewrite G_S, (Mv0 M HM). hypA. }
  apply (A_exE2 _ _ _ _ _ H0). nrmg M HM Lev HL.
  (* u0 = 0, a = 1 *)
  pose proof (A_sh2 _ Lev (Mem 1 0) _ GR) as GR1. apply (A_inst _ _ _ 0) in GR1.
  set (R2u := All (Imp (Mem 0 1) (All (Imp (Mem 0 2) (Qf (rel M (ren kap2 g)) (relU 2 (ren kap2 g))))))).
  set (R1u := All (Imp (Mem 0 1) (Qf (rel M (Xf (ren kap2 g))) (relU 1 (Xf (ren kap2 g)))))).
  assert (GR2 : DA ZF (Lev :: Mem 1 0 :: map (ren S) G1)
    (Imp Lev (Xf (Kf (Kf Lev (Sub 1 0)) (Kf R2u (Kf R1u Top)))))).
  { apply (A_conv _ _ _ GR1). unfold RFs, RF1, wrapQ, R2u, R1u. nrm M HM Lev HL. feq. }
  pose proof (A_mp _ _ _ _ GR2 ltac:(hypA)) as GR3.
  apply (A_exE2 _ _ _ _ _ GR3). nrmg M HM Lev HL.
  (* u = 0, u0 = 1, a = 2 *)
  apply (A_exI _ _ _ 0). nrmg M HM Lev HL.
  haveA HU (Kf Lev (Sub 1 0)). { hypA. }
  haveA HR (Kf R2u (Kf R1u Top)). { hypA. }
  apply A_and; [apply A_and; [apply A_and|]|].
  - exact (A_andl _ _ _ _ HU).
  - apply (Sub_use _ 1 0 2 (A_andr _ _ _ _ HU)). hypA.
  - apply (A_conv _ _ _ (A_andl _ _ _ _ HR)). unfold R2u. nrm M HM Lev HL. feq.
  - apply (A_conv _ _ _ (A_andl _ _ _ _ (A_andr _ _ _ _ HR))). unfold R1u. nrm M HM Lev HL. feq.
Qed.

Theorem lsep_from_grefl : prov ZF (STR Lev) -> prov ZF SCOV -> GREFL ->
  (forall g n, syms g = [] -> closedk (S (S n)) g = true -> DEFsep M Lev g n) -> LSEP M.
Proof.
  intros Htr Hcov Hgr Hd. apply (lsep_from_levels M HM Lev HL Htr); [|exact Hd].
  intros g n Hg Hc. exact (reflsep_from_grefl g n Hg Hc Hcov Hgr).
Qed.

Theorem lcoll_from_grefl : prov ZF (STR Lev) -> prov ZF (SSUB M Lev) -> prov ZF (SIN M Lev) -> prov ZF SCOV -> GREFL ->
  LCOLL M.
Proof.
  intros Htr Hsub Hin Hcov Hgr. apply (lcoll_from_levels M HM Lev HL Htr Hsub Hin).
  intros g n Hg Hc. exact (reflcoll_from_grefl g n Hg Hc Hcov Hgr).
Qed.
End R.
