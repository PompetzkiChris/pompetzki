(* L2RSepL.v - lane L2R round 2, 2026-10-09. Separation and Collection relativized to a class M (LCH's obligations
   O8 = GoedelCH.LSEP and O9 = GoedelCH.LCOLL, as VLred.goedel_final_red consumes them), derived in Rocq for every pure
   formula from statements about a hierarchy of levels (for L: the L_alpha):
     single statements  STR  every level is transitive          forall u (Lev u -> forall z in u, forall x in z, x in u)
                        SSUB every level is contained in M       forall u (Lev u -> forall x in u, M x)
                        SIN  every level is an element of M      forall u (Lev u -> M u)
     per formula g      REFLsep g n  for z and the parameters in M: some level u contains z and reflects g in x:
                                     forall x in u (g^M(x,z,p) <-> g^u(x,z,p))
                        DEFsep g n   for every level u containing z: {x in z : g^u(x,z,p)} is an element of M
                        REFLcoll g n for a and the parameters in M: some level u contains a and reflects g in (x,y) and
                                     exists y g in x
   lsep_from_levels : STR, REFLsep, DEFsep -> LSEP M
   lcoll_from_levels: STR, SSUB, SIN, REFLcoll -> LCOLL M
   Here g^u is relU: every quantifier bounded by membership in the level u. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat.
From Cohen Require Import Syn Prov Kal Ax Checks Replay Expand Pure Elim.
From LCH Require Import Rel2 GoedelCH.
From L2R Require Import L2RLogicA.
Import ListNotations.
Open Scope nat_scope.

(* ---- relativization to the set held by the variable w *)
Fixpoint relU (w : nat) (f : form) : form :=
  match f with
  | Mem x y => Mem x y
  | Eqv x y => Eqv x y
  | Pr p a => Pr p a
  | Neg a => Neg (relU w a)
  | Imp a b => Imp (relU w a) (relU w b)
  | All a => All (Imp (Mem 0 (S w)) (relU (S w) a))
  end.

Lemma ren_relU f : forall s w, ren s (relU w f) = relU (s w) (ren s f).
Proof.
  induction f; intros s w; simpl; try reflexivity.
  - rewrite IHf. reflexivity.
  - rewrite IHf1, IHf2. reflexivity.
  - rewrite IHf. reflexivity.
Qed.

Lemma relU_Xf w a : relU w (Xf a) = Neg (All (Imp (Mem 0 (S w)) (Neg (relU (S w) a)))). Proof. reflexivity. Qed.
Lemma relU_Kf w a b : relU w (Kf a b) = Kf (relU w a) (relU w b). Proof. reflexivity. Qed.
Lemma relU_Qf w a b : relU w (Qf a b) = Qf (relU w a) (relU w b). Proof. reflexivity. Qed.

Lemma chain_chainA gs f : chain gs f = chainA gs f.
Proof. induction gs as [|g r IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* a formula with at most the variable 0 free *)
Lemma cl1_ren F (HF : closedk 1 F = true) t : ren t F = ren (fun _ => t 0) F.
Proof. apply ren_free. intros n Hn. pose proof (closedk_free F 1 n HF Hn). assert (n = 0) by lia. subst. reflexivity. Qed.
Lemma cl1_up F (HF : closedk 1 F = true) s : ren (up s) F = F.
Proof.
  rewrite (cl1_ren F HF). simpl. rewrite <- (ren_id F) at 2. apply ren_free. intros n Hn.
  pose proof (closedk_free F 1 n HF Hn). assert (n = 0) by lia. subst. reflexivity.
Qed.

Section L.
Variable M : form.
Hypothesis HM : closedk 1 M = true.
Variable Lev : form.
Hypothesis HL : closedk 1 Lev = true.

Notation ZF := ZFpure.

(* "exists x in M, a" as the relativization writes it *)
Definition XM (a : form) : form := Neg (All (Imp M (Neg a))).

Lemma rel_Kf a b : rel M (Kf a b) = Kf (rel M a) (rel M b). Proof. reflexivity. Qed.
Lemma rel_Qf a b : rel M (Qf a b) = Qf (rel M a) (rel M b). Proof. reflexivity. Qed.
Lemma rel_Xf a : rel M (Xf a) = XM (rel M a). Proof. reflexivity. Qed.
Lemma ren_XM s a : ren s (XM a) = XM (ren (up s) a).
Proof. unfold XM. simpl. rewrite (M_up M HM). reflexivity. Qed.

(* the witness of an M-bounded existential *)
Lemma A_XM G a y : DA ZF G (ren (fun _ => y) M) -> DA ZF G (ren (scons y sid) a) -> DA ZF G (XM a).
Proof.
  intros H1 H2. unfold XM.
  assert (I : prov ZF (Imp (All (Imp M (Neg a))) (ren (scons y sid) (Imp M (Neg a))))) by apply p_inst.
  simpl in I. rewrite (cl1_ren M HM) in I. simpl in I.
  apply (A_t3 _ _ (Imp (All (Imp M (Neg a))) (Imp (ren (fun _ => y) M) (Neg (ren (scons y sid) a))))
    (ren (fun _ => y) M) (ren (scons y sid) a)); [ptA|apply A_thm; exact I|exact H1|exact H2].
Qed.

(* ---- the hypotheses *)
Definition STR : form := All (Imp Lev (All (Imp (Mem 0 1) (All (Imp (Mem 0 1) (Mem 0 2)))))).
Definition SSUB : form := All (Imp Lev (All (Imp (Mem 0 1) M))).
Definition SIN : form := All (Imp Lev M).

Definition sigS (t : nat) : nat := match t with 0 => 0 | S t' => S (S t') end.
Definition sigD (t : nat) : nat := match t with 0 => 0 | S t' => S (S (S t')) end.

(* z = variable 0, the parameters 1 .. n *)
Definition REFLsep (g : form) (n : nat) : Prop :=
  prov ZF (chain (G M (S n))
    (Xf (Kf (Kf Lev (Mem 1 0)) (All (Imp (Mem 0 1) (Qf (rel M (ren sigS g)) (relU 1 (ren sigS g)))))))).
Definition DEFsep (g : form) (n : nat) : Prop :=
  prov ZF (chain (G M (S n))
    (All (Imp Lev (Imp (Mem 1 0)
      (Xf (Kf M (All (Qf (Mem 0 1) (Kf (Mem 0 3) (relU 2 (ren sigD g))))))))))).


Lemma free_closedk f : forall k, (forall i, free i f = true -> i < k) -> closedk k f = true.
Proof.
  induction f; intros k H; simpl in *.
  - apply andb_true_iff. split; apply Nat.ltb_lt; apply H; rewrite Nat.eqb_refl; [reflexivity|apply orb_true_r].
  - apply andb_true_iff. split; apply Nat.ltb_lt; apply H; rewrite Nat.eqb_refl; [reflexivity|apply orb_true_r].
  - apply forallb_forall. intros x Hx. apply Nat.ltb_lt. apply H. apply existsb_exists. exists x. split; [exact Hx|apply Nat.eqb_refl].
  - apply IHf. exact H.
  - apply andb_true_iff. split; [apply IHf1|apply IHf2]; intros i Hi; apply H; rewrite Hi; [reflexivity|apply orb_true_r].
  - apply IHf. intros [|i] Hi; [lia|]. specialize (H i Hi). lia.
Qed.

Lemma closed_SepF_g g n : closedk n (SepF g) = true -> closedk (S (S n)) g = true.
Proof.
  intros H. unfold SepF, Qf, Kf, Xf in H. simpl in H. repeat (apply andb_true_iff in H as [? H]).
  apply free_closedk. intros i Fi. pose proof (free_ren g i skip1 Fi) as F2.
  pose proof (closedk_free _ _ _ H0 F2) as L. destruct i as [|i]; simpl in L; lia.
Qed.

Definition Lv (i : nat) : form := ren (fun _ => i) Lev.
Lemma Lev_ren t : ren t Lev = Lv (t 0).
Proof. unfold Lv. apply ren_free. intros k Hk. pose proof (closedk_free Lev 1 k HL Hk). assert (k = 0) by lia. subst. reflexivity. Qed.
Lemma Lv0 : Lv 0 = Lev.
Proof. unfold Lv. rewrite <- (ren_id Lev) at 2. apply ren_free. intros k Hk. pose proof (closedk_free Lev 1 k HL Hk). lia. Qed.
Lemma ren_Lv s i : ren s (Lv i) = Lv (s i). Proof. unfold Lv. rewrite ren_comp. reflexivity. Qed.
Lemma rel_ren' f s : ren s (rel M f) = rel M (ren s f). Proof. symmetry. apply (rel_ren M HM). Qed.

Lemma A_sh1 G a f : DA ZF G f -> DA ZF (a :: map (ren S) G) (ren S f).
Proof. intros H. apply (A_weak _ (map (ren S) G)); [intros h Hh; right; exact Hh|]. apply A_ren. exact H. Qed.
Lemma A_sh2 G a b f : DA ZF G f -> DA ZF (a :: b :: map (ren S) G) (ren S f).
Proof. intros H. apply (A_weak _ (map (ren S) G)); [intros h Hh; right; right; exact Hh|]. apply A_ren. exact H. Qed.
Lemma A_conv G f f' : DA ZF G f -> f = f' -> DA ZF G f'.
Proof. intros H <-. exact H. Qed.
Lemma sid_red n : sid n = n. Proof. reflexivity. Qed.

(* the transitivity of the levels, used at variables u, z, x *)
Lemma STR_use G u z x : prov ZF STR -> DA ZF G (Lv u) -> DA ZF G (Mem z u) -> DA ZF G (Mem x z) ->
  DA ZF G (Mem x u).
Proof.
  intros H H1 H2 H3. pose proof (A_inst _ _ _ u (A_thm _ G _ H)) as T. unfold STR in T. cbn [ren up scons sid] in T.
  rewrite (Lev_ren) in T. cbn in T. pose proof (A_mp _ _ _ _ T H1) as T1.
  apply (A_inst _ _ _ z) in T1. cbn [ren up scons sid] in T1. pose proof (A_mp _ _ _ _ T1 H2) as T2.
  apply (A_inst _ _ _ x) in T2. cbn [ren up scons sid] in T2. exact (A_mp _ _ _ _ T2 H3).
Qed.

End L.

Arguments XM : simpl never.
Arguments G : simpl never.
Arguments Lv : simpl never.
Arguments Mv : simpl never.

Ltac nrm M HM Lev HL := repeat progress (rewrite ?renA_Kf, ?renA_Df, ?renA_Qf, ?renA_Xf, ?renA_Top, ?(ren_XM M HM),
  ?ren_relU, ?(rel_ren' M HM), ?(M_ren M HM), ?(Mv_ren M), ?(Mv0 M HM), ?(Lev_ren Lev HL), ?(ren_Lv Lev), ?(Lv0 Lev HL),
  ?(rel_Xf M), ?(rel_Kf M), ?(rel_Qf M), ?relU_Xf, ?relU_Kf, ?relU_Qf,
  ?ren_comp, ?sid_red; cbn [ren up scons sid map]).
Ltac nrmin M HM Lev HL H := repeat progress (rewrite ?renA_Kf, ?renA_Df, ?renA_Qf, ?renA_Xf, ?renA_Top, ?(ren_XM M HM),
  ?ren_relU, ?(rel_ren' M HM), ?(M_ren M HM), ?(Mv_ren M), ?(Mv0 M HM), ?(Lev_ren Lev HL), ?(ren_Lv Lev), ?(Lv0 Lev HL),
  ?(rel_Xf M), ?(rel_Kf M), ?(rel_Qf M), ?relU_Xf, ?relU_Kf, ?relU_Qf,
  ?ren_comp, ?sid_red in H; cbn [ren up scons sid map] in H).
Ltac nrm2 M HM Lev HL := repeat progress (rewrite ?sid_red; nrm M HM Lev HL).
Ltac nrmg M HM Lev HL := match goal with |- DA ?A ?G ?f => let Gc := fresh "Gc" in set (Gc := G); nrm M HM Lev HL; subst Gc end.
Ltac fixr := let i := fresh "i" in apply ren_ext; intros [|[|i]]; cbn; lia.
Ltac dt3A H1 H2 H3 := match type of H1 with DA _ _ ?a => match type of H2 with DA _ _ ?b => match type of H3 with DA _ _ ?c =>
  apply (A_t3 _ _ a b c); [ptA|exact H1|exact H2|exact H3] end end end.
Ltac dt2A H1 H2 := match type of H1 with DA _ _ ?a => match type of H2 with DA _ _ ?b =>
  apply (A_t2 _ _ a b); [ptA|exact H1|exact H2] end end.
Ltac dt1A H1 := match type of H1 with DA _ _ ?a => apply (A_t1 _ _ a); [ptA|exact H1] end.
Ltac feq := repeat (first [ apply ren_ext; let i := fresh "i" in intros [|[|i]]; unfold sid; cbn; lia | progress f_equal ]).

Section L2.
Variable M : form.
Hypothesis HM : closedk 1 M = true.
Variable Lev : form.
Hypothesis HL : closedk 1 Lev = true.
Notation ZF := ZFpure.

Definition tau4 (t : nat) : nat := match t with 0 => 0 | 1 => 3 | S (S i) => S (S (S (S i))) end.

Theorem lsep_from_levels : prov ZF (STR Lev) ->
  (forall g n, syms g = [] -> closedk (S (S n)) g = true -> REFLsep M Lev g n) ->
  (forall g n, syms g = [] -> closedk (S (S n)) g = true -> DEFsep M Lev g n) ->
  LSEP M.
Proof.
  intros Htr Hr Hd g Hg n Hn Hc. pose proof (closed_SepF_g g n Hc) as Hc2.
  rewrite chain_chainA. apply A_chain.
  change (rel M (SepF g)) with (All (Imp M (XM M (All (Imp M (Qf (Mem 0 1) (Kf (Mem 0 2) (rel M (ren skip1 g))))))))).
  apply A_all. apply A_intro.
  replace (M :: map (ren S) (G M n)) with (G M (S n)) by (rewrite G_S, (Mv0 M HM); reflexivity).
  pose proof (A_unchain _ _ _ ltac:(rewrite <- chain_chainA; exact (Hr g n Hg Hc2))) as R.
  pose proof (A_unchain _ _ _ ltac:(rewrite <- chain_chainA; exact (Hd g n Hg Hc2))) as Dd.
  set (G1 := G M (S n)) in *.
  set (a1 := Kf Lev (Mem 1 0)). set (b1 := All (Imp (Mem 0 1) (Qf (rel M (ren sigS g)) (relU 1 (ren sigS g))))).
  apply (A_exE2 _ _ a1 b1 _ R).
  (* u = 0, z = 1 *)
  nrm M HM Lev HL.
  (* the level u = 0 holds z = 1 *)
  pose proof (A_sh2 _ a1 b1 _ Dd) as Dd1. nrmin M HM Lev HL Dd1.
  apply (A_inst _ _ _ 0) in Dd1. nrmin M HM Lev HL Dd1.
  haveA HLu Lev. { apply (A_andl _ _ _ (Mem 1 0)). hypA. }
  haveA Hzu (Mem 1 0). { apply (A_andr _ _ Lev). hypA. }
  pose proof (A_mp _ _ _ _ (A_mp _ _ _ _ Dd1 HLu) Hzu) as Dd2.
  match type of Dd2 with DA _ _ (Xf (Kf ?a ?b)) => set (a2 := a); set (b2 := b); apply (A_exE2 _ _ a2 b2 _ Dd2) end.
  (* y = 0, u = 1, z = 2 *)
  nrm M HM Lev HL.
  apply (A_XM M HM _ _ 0).
  { change (ren (fun _ => 0) M) with (Mv M 0). rewrite (Mv0 M HM). hypA. }
  nrm M HM Lev HL. apply A_all. apply A_intro.
  (* x = 0, y = 1, u = 2, z = 3, parameter i = i + 4 *)
  haveA F1 (Qf (Mem 0 1) (Kf (Mem 0 3) (relU 2 (ren tau4 g)))).
  { haveA B (ren S b2). { hypA. } apply (A_inst _ _ _ 0) in B. unfold b2 in B.
    apply (A_conv _ _ _ B). nrm M HM Lev HL. feq. }
  haveA F2 (Imp (Mem 0 2) (Qf (rel M (ren tau4 g)) (relU 2 (ren tau4 g)))).
  { haveA B (ren S (ren S b1)). { hypA. } apply (A_inst _ _ _ 0) in B. unfold b1 in B.
    apply (A_conv _ _ _ B). nrm M HM Lev HL. feq. }
  haveA F3 (Imp (Mem 0 3) (Mem 0 2)).
  { apply A_intro. eapply STR_use with (u := 2) (z := 3) (x := 0); [exact HL|exact Htr| | |hypA].
    - haveA A1 (ren S (ren S a1)). { apply A_add. hypA. } unfold a1 in A1.
      apply (A_andl _ _ _ (Mem 3 2)). apply (A_conv _ _ _ A1). nrm M HM Lev HL. reflexivity.
    - haveA A1 (ren S (ren S a1)). { apply A_add. hypA. } unfold a1 in A1.
      apply (A_andr _ _ (Lv Lev 2)). apply (A_conv _ _ _ A1). nrm M HM Lev HL. reflexivity. }
  match goal with |- DA _ _ (Qf (Mem 0 1) (Kf (Mem 0 3) ?r)) => replace r with (rel M (ren tau4 g)) by (nrm M HM Lev HL; feq) end.
  dt3A F1 F2 F3.
Qed.

(* ---- Collection *)
Definition sig2 (t : nat) : nat := match t with 0 => 0 | 1 => 1 | S (S t') => S (S (S t')) end.

(* a = variable 0, the parameters 1 .. n; inside: y = 0, x = 1, u = 2, a = 3 *)
Definition REFLcoll (g : form) (n : nat) : Prop :=
  prov ZF (chain (G M (S n))
    (Xf (Kf (Kf (Kf Lev (Mem 1 0))
                (All (Imp (Mem 0 1) (All (Imp (Mem 0 2) (Qf (rel M (ren sig2 g)) (relU 2 (ren sig2 g))))))))
            (All (Imp (Mem 0 1) (Qf (rel M (Xf (ren sig2 g))) (relU 1 (Xf (ren sig2 g))))))))).

Lemma closed_CollF_g g n : closedk n (CollF g) = true -> closedk (S (S (S n))) g = true.
Proof.
  intros H. unfold CollF, Kf, Xf in H. simpl in H. repeat (apply andb_true_iff in H as [? H]).
  apply free_closedk. intros i Fi. pose proof (free_ren g i ins2 Fi) as F2.
  pose proof (closedk_free _ _ _ H F2) as L. destruct i as [|[|i]]; simpl in L; lia.
Qed.

Lemma xb_ex a b : prov ZF (Imp (Neg (All (Imp a (Neg b)))) (Xf (Kf a b))).
Proof.
  assert (H : prov ZF (Imp (All (Neg (Kf a b))) (All (Imp a (Neg b))))) by (apply all_imp; ptA).
  apply (qmp _ _ _ H). ptA.
Qed.
Lemma A_exEb G a b c : DA ZF G (Neg (All (Imp a (Neg b)))) -> DA ZF (a :: b :: map (ren S) G) (ren S c) -> DA ZF G c.
Proof. intros H1 H2. exact (A_exE2 _ _ _ _ _ (A_t1 _ _ _ _ (xb_ex a b) H1) H2). Qed.

Theorem lcoll_from_levels : prov ZF (STR Lev) -> prov ZF (SSUB M Lev) -> prov ZF (SIN M Lev) ->
  (forall g n, syms g = [] -> closedk (S (S (S n))) g = true -> REFLcoll g n) ->
  LCOLL M.
Proof.
  intros Htr Hsub Hin Hr g Hg n Hn Hc. pose proof (closed_CollF_g g n Hc) as Hc2.
  rewrite chain_chainA. apply A_chain.
  change (rel M (CollF g)) with (All (Imp M (Imp (All (Imp M (Imp (Mem 0 1) (XM M (rel M g)))))
    (XM M (All (Imp M (Imp (Mem 0 2) (XM M (Kf (Mem 0 2) (rel M (ren ins2 g))))))))))).
  apply A_all. apply A_intro.
  replace (M :: map (ren S) (G M n)) with (G M (S n)) by (rewrite G_S, (Mv0 M HM); reflexivity).
  pose proof (A_unchain _ _ _ ltac:(rewrite <- chain_chainA; exact (Hr g n Hg Hc2))) as R.
  set (G1 := G M (S n)) in *.
  set (H := All (Imp M (Imp (Mem 0 1) (XM M (rel M g))))).
  apply A_intro.
  match type of R with DA _ _ (Xf (Kf ?a ?b)) => set (a1 := a); set (b1 := b); apply (A_exE2 _ _ a1 b1 _ (A_add _ _ H _ R)) end.
  (* u = 0, a = 1 *)
  nrmg M HM Lev HL.
  set (R2 := All (Imp (Mem 0 1) (All (Imp (Mem 0 2) (Qf (rel M (ren sig2 g)) (relU 2 (ren sig2 g))))))).
  haveA HA (Kf (Kf Lev (Mem 1 0)) R2). { hypA. }
  pose proof (A_andl _ _ _ _ (A_andl _ _ _ _ HA)) as HLu. pose proof (A_andr _ _ _ _ (A_andl _ _ _ _ HA)) as Hau.
  pose proof (A_andr _ _ _ _ HA) as HR2.
  (* b := u *)
  apply (A_XM M HM _ _ 0).
  { change (ren (fun _ => 0) M) with (Mv M 0). rewrite (Mv0 M HM).
    apply (A_mp _ _ Lev); [|exact HLu]. apply (A_conv _ _ _ (A_inst _ _ _ 0 (A_thm _ _ _ Hin))). unfold SIN.
    nrm M HM Lev HL. reflexivity. }
  nrmg M HM Lev HL. apply A_all. apply A_intro. apply A_intro.
  (* x = 0, u = 1, a = 2, parameter i = i + 3 *)
  haveA Hxu (Mem 0 1).
  { eapply STR_use with (u := 1) (z := 2) (x := 0); [exact HL|exact Htr| | |hypA].
    - apply (A_conv _ _ _ (A_add _ _ _ _ (A_sh1 _ M _ HLu))). nrm M HM Lev HL. reflexivity.
    - apply (A_conv _ _ _ (A_add _ _ _ _ (A_sh1 _ M _ Hau))). nrm M HM Lev HL. reflexivity. }
  haveA E1 (XM M (rel M (ren sig2 g))).
  { haveA Hh (ren S (ren S H)). { hypA. } apply (A_inst _ _ _ 0) in Hh.
    assert (Hh2 : DA ZF (Mem 0 2 :: M :: map (ren S) (a1 :: b1 :: ren S H :: map (ren S) G1))
                    (Imp M (Imp (Mem 0 2) (XM M (rel M (ren sig2 g)))))).
    { apply (A_conv _ _ _ Hh). unfold H. nrm M HM Lev HL. feq. }
    apply (A_mp _ _ _ _ (A_mp _ _ _ _ Hh2 ltac:(hypA)) ltac:(hypA)). }
  haveA E2 (Neg (All (Imp (Mem 0 2) (Neg (relU 2 (ren sig2 g)))))).
  { haveA Hb (ren S b1). { hypA. } apply (A_inst _ _ _ 0) in Hb.
    assert (Hb2 : DA ZF (Mem 0 2 :: M :: map (ren S) (a1 :: b1 :: ren S H :: map (ren S) G1))
                    (Imp (Mem 0 1) (Qf (XM M (rel M (ren sig2 g))) (Neg (All (Imp (Mem 0 2) (Neg (relU 2 (ren sig2 g))))))))).
    { apply (A_conv _ _ _ Hb). unfold b1. nrm M HM Lev HL. feq. }
    exact (A_iffl _ _ _ _ (A_mp _ _ _ _ Hb2 Hxu) E1). }
  apply (A_exEb _ _ _ _ E2).
  (* y = 0, x = 1, u = 2, a = 3, parameter i = i + 4 *)
  nrmg M HM Lev HL.
  apply (A_XM M HM _ _ 0).
  { change (ren (fun _ => 0) M) with (Mv M 0).
    pose proof (A_inst _ _ _ 2 (A_thm _ (Mem 0 2 :: relU 2 (ren sig2 g) :: map (ren S) (Mem 0 2 :: M :: map (ren S)
      (a1 :: b1 :: ren S H :: map (ren S) G1))) _ Hsub)) as T. unfold SSUB in T.
    assert (T2 : DA ZF (Mem 0 2 :: relU 2 (ren sig2 g) :: map (ren S) (Mem 0 2 :: M :: map (ren S)
      (a1 :: b1 :: ren S H :: map (ren S) G1))) (Imp (Lv Lev 2) (All (Imp (Mem 0 3) (Mv M 0))))).
    { apply (A_conv _ _ _ T). nrm M HM Lev HL. reflexivity. }
    pose proof (A_mp _ _ _ _ T2 (A_conv _ _ _ (A_sh2 _ _ _ _ (A_add _ _ (Mem 0 2) _ (A_sh1 _ M _ HLu))) ltac:(nrm M HM Lev HL; reflexivity))) as T3.
    apply (A_inst _ _ _ 0) in T3. cbn [ren up scons sid] in T3. rewrite (Mv_ren M) in T3. cbn in T3.
    exact (A_mp _ _ _ _ T3 ltac:(hypA)). }
  nrmg M HM Lev HL.
  (* y = 0, x = 1, u = 2, a = 3 *)
  haveA Q (Imp (Mem 0 2) (Qf (rel M (ren sig2 g)) (relU 2 (ren sig2 g)))).
  { pose proof (A_sh2 _ (Mem 0 2) (relU 2 (ren sig2 g)) _ (A_add _ _ (Mem 0 2) _ (A_sh1 _ M _ HR2))) as R4.
    pose proof (A_sh2 _ (Mem 0 2) (relU 2 (ren sig2 g)) _ Hxu) as Hxu4. cbn in Hxu4.
    apply (A_inst _ _ _ 1) in R4.
    assert (R5 : DA ZF (Mem 0 2 :: relU 2 (ren sig2 g) :: map (ren S) (Mem 0 2 :: M :: map (ren S) (a1 :: b1 :: map (ren S) (H :: G1))))
      (Imp (Mem 1 2) (All (Imp (Mem 0 3) (Qf (rel M (ren (up (scons 1 sid)) (ren (up (up S)) (ren (up (up S)) (ren sig2 g)))))
        (relU 3 (ren (up (scons 1 sid)) (ren (up (up S)) (ren (up (up S)) (ren sig2 g)))))))))).
    { apply (A_conv _ _ _ R4). unfold R2. nrm M HM Lev HL. feq. }
    pose proof (A_mp _ _ _ _ R5 Hxu4) as R6. apply (A_inst _ _ _ 0) in R6.
    apply (A_conv _ _ _ R6). nrm M HM Lev HL. feq. }
  apply A_and; [hypA|].
  match goal with |- DA _ _ ?r => replace r with (rel M (ren sig2 g)) by (nrm M HM Lev HL; feq) end.
  exact (A_iffr _ _ _ _ (A_mp _ _ _ _ Q ltac:(hypA)) ltac:(hypA)).
Qed.
End L2.
