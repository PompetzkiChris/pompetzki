(* GoedelCH.v - Goedel's half of the independence of CH, reduced to its L obligations, in the form of Theorem 29.
   Input theory GamCH: the seven axioms, every Separation and Collection instance (any formula, any symbols), the 23
   ZB_BASE definitions (D0 of Pure.v, in every renaming) and the plain statement of CH, parsed from ch_text:
     A w A x A p I K K Om1 w A u Q E u p Sub2 u w Sub2 x p D Le2 x w Le2 p x
   i.e. for w = omega, p = P(omega) and x a subset of p: x injects into omega, or p injects into x.
   ZFpure: pure ZFC, as in Elim.v.
   goedel_relative_consistency: for every class formula M (closedk 1 M), if pure ZFC proves
     LEX   exists x M(x)
     LAX   the seven axioms relativized to M
     LSEP  every pure Separation instance relativized to M, its parameters guarded by M
     LCOLL every pure Collection instance relativized to M, its parameters guarded by M
     LCH   CH (purified by pi of Pure.v) relativized to M
   then GamCH |- Bot implies ZFpure |- Bot. For M the defining formula of the constructible universe L these five
   premises are Goedel's theorems (L is an inner model of ZF, of AC, and of V = L, which gives GCH); they are the
   remaining obligations of lane LCH (RESULTS.md).
   Proof: pi_prov purifies every derivation from GamCH into ZFpure + pi ch; Rel2.rel_con relativizes it to M.
   Lane LCH, 2026-10-09. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Expand Pure Elim Replay.
From LCH Require Import Rel2.
Import ListNotations.
Open Scope nat_scope.

Definition ch_text : string := "A w A x A p I K K Om1 w A u Q E u p Sub2 u w Sub2 x p D Le2 x w Le2 p x".
Definition ch : form := match pstmt symtab [] ch_text with Some f => f | None => Top end.
Lemma ch_parse : pstmt symtab [] ch_text <> None. Proof. vm_compute. discriminate. Qed.
Lemma ch_closed : closedk 0 ch = true. Proof. vm_compute. reflexivity. Qed.
Lemma ch_is : ch = All (All (All (Imp (Neg (Imp (Neg (Imp (Pr 20 [2])
  (Neg (All (Neg (Imp (Imp (Mem 0 1) (Pr 5 [0; 3])) (Neg (Imp (Pr 5 [0; 3]) (Mem 0 1))))))))) (Neg (Pr 5 [1; 0]))))
  (Imp (Neg (Pr 14 [1; 2])) (Pr 14 [0; 1]))))).
Proof. vm_compute. reflexivity. Qed.

Lemma pi_imp a b : pi (Imp a b) = Imp (pi a) (pi b). Proof. reflexivity. Qed.
Lemma pi_neg a : pi (Neg a) = Neg (pi a). Proof. reflexivity. Qed.
Lemma pi_all a : pi (All a) = All (pi a). Proof. reflexivity. Qed.
Lemma pi_eqv x y : pi (Eqv x y) = Eqv x y. Proof. reflexivity. Qed.

Lemma syms_SepF g : syms (SepF g) = [] -> syms g = [].
Proof. unfold SepF, Qf, Kf, Xf. simpl. rewrite syms_ren. intros H. repeat (apply app_eq_nil in H as [H ?]); auto. Qed.
Lemma syms_SepF2 g : syms g = [] -> syms (SepF g) = [].
Proof. unfold SepF, Qf, Kf, Xf. simpl. rewrite syms_ren. intros H. rewrite H. reflexivity. Qed.
Lemma syms_CollF g : syms (CollF g) = [] -> syms g = [].
Proof. unfold CollF, Kf, Xf. simpl. rewrite syms_ren. intros H. repeat (apply app_eq_nil in H as [H ?]); auto. Qed.
Lemma syms_CollF2 g : syms g = [] -> syms (CollF g) = [].
Proof. unfold CollF, Kf, Xf. simpl. rewrite syms_ren. intros H. rewrite H. reflexivity. Qed.

(* ---- the input theories with one extra axiom E, and pure ZFC with one extra axiom *)
Definition GamE (E : form) (f : form) : Prop := ZFC7 f \/ SepAx f \/ CollAx f \/ DefAx D0 f \/ f = E.
Definition ZFE (E : form) (f : form) : Prop := ZFpure f \/ f = E.

(* purification of every derivation: each rule goes to the same rule, each D0 definition to X <-> X *)
Theorem pi_prov E : forall f, prov (GamE E) f -> prov (ZFE (pi E)) (pi f).
Proof.
  intros f P. induction P.
  - destruct H as [[i [Hi ->]]|[[g ->]|[[g ->]|[[d [s [Hd ->]]]| ->]]]].
    + rewrite (pi_fix _ (axf_pure i Hi)). apply p_ax. left. split; [left; exists i; auto|exact (axf_pure i Hi)].
    + rewrite pi_Sep. apply p_ax. left. split; [right; left; eexists; reflexivity|apply syms_SepF2, pi_pure].
    + rewrite pi_Coll. apply p_ax. left. split; [right; right; eexists; reflexivity|apply syms_CollF2, pi_pure].
    + destruct (pi_defax d s Hd) as [X [EX _]]. rewrite EX. apply iff_refl.
    + apply p_ax. right. reflexivity.
  - rewrite !pi_imp. apply p_k.
  - rewrite !pi_imp. apply p_s.
  - rewrite !pi_imp, !pi_neg. apply p_c.
  - rewrite pi_imp in IHP2. exact (p_mp _ _ _ IHP1 IHP2).
  - rewrite pi_all. apply p_gen. exact IHP.
  - rewrite pi_imp, pi_all, pi_ren. apply p_inst.
  - rewrite pi_imp, pi_all, pi_ren. apply p_vac.
  - rewrite !pi_imp, !pi_all, pi_imp. apply p_dist.
  - rewrite pi_eqv. apply p_refl.
  - rewrite !pi_imp, pi_eqv, !pi_ren. apply p_leib.
Qed.

Definition GamCH : form -> Prop := GamE ch.

Lemma ZFE_ren E : closedk 0 E = true -> forall f s, ZFE E f -> ZFE E (ren s f).
Proof.
  intros HE f s [[[[i [Hi ->]]|[[g ->]|[g ->]]] Hp]| ->].
  - left. rewrite (ren_closed _ s (axf_closed i Hi)). split; [left; exists i; auto|exact Hp].
  - left. rewrite SepF_ren. split; [right; left; eexists; reflexivity|].
    apply syms_SepF2. rewrite syms_ren. exact (syms_SepF g Hp).
  - left. rewrite CollF_ren. split; [right; right; eexists; reflexivity|].
    apply syms_CollF2. rewrite syms_ren. exact (syms_CollF g Hp).
  - right. apply ren_closed. exact HE.
Qed.

Lemma pi_ch_closed : closedk 0 (pi ch) = true. Proof. vm_compute. reflexivity. Qed.

Section Goedel.
Variable M : form.
Hypothesis HM : closedk 1 M = true.

Definition LEX : Prop := prov ZFpure (Xf M).
Definition LAX : Prop := forall i, i < 7 -> prov ZFpure (rel M (axf i)).
Definition LSEP : Prop := forall g, syms g = [] -> forall n, 1 <= n -> closedk n (SepF g) = true ->
  prov ZFpure (chain (G M n) (rel M (SepF g))).
Definition LCOLL : Prop := forall g, syms g = [] -> forall n, 1 <= n -> closedk n (CollF g) = true ->
  prov ZFpure (chain (G M n) (rel M (CollF g))).
Definition LCH : Prop := prov ZFpure (rel M (pi ch)).

Theorem goedel_relative_consistency : LEX -> LAX -> LSEP -> LCOLL -> LCH -> prov GamCH Bot -> prov ZFpure Bot.
Proof.
  intros Hex Hax Hsep Hcoll Hch D.
  pose proof (pi_prov ch Bot D) as P. rewrite (pi_fix Bot eq_refl) in P.
  apply (rel_con M HM (ZFE (pi ch)) ZFpure (ZFE_ren (pi ch) pi_ch_closed)); [|exact Hex|exact P].
  intros f [[[[i [Hi ->]]|[[g ->]|[g ->]]] Hp]| ->] n Hn Hc.
  - apply chain_k. exact (Hax i Hi).
  - exact (Hsep g (syms_SepF g Hp) n Hn Hc).
  - exact (Hcoll g (syms_CollF g Hp) n Hn Hc).
  - apply chain_k. exact Hch.
Qed.

Corollary con_zfc_con_ch : LEX -> LAX -> LSEP -> LCOLL -> LCH -> ~ prov ZFpure Bot -> ~ prov GamCH Bot.
Proof. intros a b c d e C D. exact (C (goedel_relative_consistency a b c d e D)). Qed.
End Goedel.
