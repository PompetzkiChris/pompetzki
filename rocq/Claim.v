(* Claim.v - the transformation is correct for every input derivation. For every formula f that Gam0 derives, Gam
   derives Coh(pp) -> TOP(V(pi f)): at every coherent condition pp the value of the purified formula is pp. By induction
   on the derivation: each axiom and rule of the calculus is one interface template, instantiated at the purified
   formulas; the placeholder hypotheses are discharged by inv_all (EX UQ RG) and sub_all (SUB); modus ponens and
   generalization lift over Coh(pp). *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Use Sub Inv2 Sub2 Sub3 Expand Pure Notch.
Import ListNotations.
Open Scope nat_scope.

Definition Coh : form := Pr coh [0].

Lemma pi_Neg a : pi (Neg a) = Neg (pi a). Proof. reflexivity. Qed.
Lemma pi_Imp a b : pi (Imp a b) = Imp (pi a) (pi b). Proof. reflexivity. Qed.
Lemma pi_All a : pi (All a) = All (pi a). Proof. reflexivity. Qed.
Lemma pi_Eqv x y : pi (Eqv x y) = Eqv x y. Proof. reflexivity. Qed.

Lemma psub_Imp tau rho a b : psub tau rho (Imp a b) = Imp (psub tau rho a) (psub tau rho b). Proof. reflexivity. Qed.
Lemma psub_Kf tau rho a b : psub tau rho (Kf a b) = Kf (psub tau rho a) (psub tau rho b). Proof. reflexivity. Qed.
Lemma ren_Imp s a b : ren s (Imp a b) = Imp (ren s a) (ren s b). Proof. reflexivity. Qed.
Lemma ren_Kf s a b : ren s (Kf a b) = Kf (ren s a) (ren s b). Proof. reflexivity. Qed.

Lemma wkC X : prov Gam X -> prov Gam (Imp Coh X).
Proof. intros H. apply (p_mp _ _ _ H). apply p_k. Qed.

(* ---- computing a template's instance renamed back *)
Ltac ptw := let i := fresh "i" in
  intros [|[|[|[|[|i]]]]]; cbv [inst_args sh6 un6 swap01 scons sid up skip1 ins2]; simpl; try reflexivity; try lia.
Ltac strip := repeat match goal with
  | |- Neg _ = Neg _ => f_equal
  | |- Imp _ _ = Imp _ _ => f_equal
  | |- All _ = All _ => f_equal
  end.
Ltac leaf := first [ reflexivity | rewrite ?ren_comp; first [ apply ren_id'; ptw | apply ren_ext; ptw ] ].
Ltac back := simpl; unfold SepF, CollF, Qf, Kf, Xf; strip; leaf.

Section C.
Hypothesis K : KERNEL.

Ltac kt n := apply (useK K n); vm_compute; reflexivity.

Lemma invEX f : syms f = [] -> prov Gam (EXf (V f)). Proof. intros H. exact (proj1 (inv_all K f H)). Qed.
Lemma invUQ f : syms f = [] -> prov Gam (UQf (V f)). Proof. intros H. exact (proj1 (proj2 (inv_all K f H))). Qed.
Lemma invRG f : syms f = [] -> prov Gam (RGf (V f)). Proof. intros H. exact (proj2 (proj2 (inv_all K f H))). Qed.

(* a SUB hypothesis of a placeholder, instantiated at a pure formula: sub_all *)
Lemma hyp_SUBg l p th args h rho : otau l p = Some th -> syms th = [] -> P7 rho -> h < 6 ->
  prov Gam (psub (vtau l) rho (SUBf vz (Pr p args) h 0 1)).
Proof.
  intros Ho Hp Hr Hh. rewrite (psub_ext _ (vtau l) rho (fun j => 1 + (rho j - 1))) by (apply shift_back; exact Hr).
  rewrite (SUB_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l) (Pr p args) h 0 1 (fun j => rho j - 1))
    by (intros j; specialize (Hr j); lia).
  simpl. rewrite Ho. apply (sub_all K). rewrite syms_ren. exact Hp.
Qed.

Ltac pure := first [ apply pi_pure | rewrite syms_ren; apply pi_pure | assumption | rewrite syms_ren; assumption ].
Ltac disch1 := first
  [ eapply hyp_EX; [reflexivity|eassumption|apply invEX; pure]
  | eapply hyp_UQ; [reflexivity|eassumption|apply invUQ; pure]
  | eapply hyp_RG; [reflexivity|eassumption|apply invRG; pure]
  | eapply hyp_SUBg; [reflexivity|pure|eassumption|lia] ].
Ltac disch := let rho := fresh "rho" in let h := fresh "h" in let P := fresh "P" in let Hin := fresh "Hin" in
  intros rho h P Hin; repeat (destruct Hin as [<-|Hin]; [disch1|]); destruct Hin.

Lemma via_TOP F Hs l : prov (fun g => Gam g \/ In g Hs) (TOPf (V F)) ->
  (forall rho h, P7 rho -> In h Hs -> prov Gam (psub (vtau l) rho h)) -> prov Gam (TOPf (V (psub (otau l) sh6 F))).
Proof. intros D H. rewrite <- concl_TOP. exact (apply_T _ Hs l sh6 D P7_sh6 H). Qed.

Lemma tpl_TOP F Hs l G s : prov (fun g => Gam g \/ In g Hs) (TOPf (V F)) ->
  (forall rho h, P7 rho -> In h Hs -> prov Gam (psub (vtau l) rho h)) ->
  ren s (psub (otau l) sh6 F) = G -> prov Gam (TOPf (V G)).
Proof. intros D H E. apply (back_TOP _ _ s E). exact (via_TOP F Hs l D H). Qed.

Definition HsKC : list form := [EXf (V PA); EXf (V PB); RGf (V PA); RGf (V PB); UQf (V PA); UQf (V PB)].
Definition HsS : list form :=
  [EXf (V PA); EXf (V PB); EXf (V PD); RGf (V PA); RGf (V PB); RGf (V PD); UQf (V PA); UQf (V PB); UQf (V PD)].
Definition PC := Pr uc [0]. Definition PC1 := Pr ud1 [0].
Definition HsDist : list form := [EXf (V PC); EXf (V PC1); RGf (V PC); RGf (V PC1); UQf (V PC); UQf (V PC1)].
Definition PF := Pr uf [0; 1]. Definition PG := Pr ug [0; 1; 2].
Definition HsSep : list form := [EXf (V PF); RGf (V PF); SUBf vz (Pr uf [3; 2]) 3 0 1; SUBf vz (Pr uf [3; 2]) 3 0 1; UQf (V PF)].
Definition HsColl : list form := [EXf (V PG); RGf (V PG); SUBf vz (Pr ug [4; 2; 3]) 4 0 1; UQf (V PG)].

(* ---- the cases *)
Lemma case_K a b : prov Gam (Imp Coh (TOPf (V (pi (Imp a (Imp b a)))))).
Proof.
  apply wkC. rewrite !pi_Imp.
  apply (tpl_TOP (Imp PA (Imp PB PA)) HsKC [(ua, pi a); (ub, pi b)] _ un6); [kt "TplK"|unfold HsKC; disch|back].
Qed.

Lemma case_S a b c : prov Gam (Imp Coh (TOPf (V (pi (Imp (Imp a (Imp b c)) (Imp (Imp a b) (Imp a c))))))).
Proof.
  apply wkC. rewrite !pi_Imp.
  apply (tpl_TOP (Imp (Imp PA (Imp PB PD)) (Imp (Imp PA PB) (Imp PA PD))) HsS [(ua, pi a); (ub, pi b); (ud, pi c)] _ un6);
    [kt "TplS"|unfold HsS; disch|back].
Qed.

Lemma case_C a b : prov Gam (Imp Coh (TOPf (V (pi (Imp (Imp (Neg a) (Neg b)) (Imp b a)))))).
Proof.
  apply wkC. rewrite !pi_Imp, !pi_Neg.
  apply (tpl_TOP (Imp (Imp (Neg PA) (Neg PB)) (Imp PB PA)) HsKC [(ua, pi a); (ub, pi b)] _ un6);
    [kt "TplC"|unfold HsKC; disch|back].
Qed.

Lemma case_Inst a y : prov Gam (Imp Coh (TOPf (V (pi (Imp (All a) (ren (scons y sid) a)))))).
Proof.
  apply wkC. rewrite pi_Imp, pi_All, pi_ren.
  apply (tpl_TOP (Imp (All PC) PC) [EXf (V PC); UQf (V PC)] [(uc, pi a)] _
    (fun i => match i with 0 => y | _ => i - 6 end)); [kt "TplInst"|disch|back].
Qed.

Lemma case_Vac a : prov Gam (Imp Coh (TOPf (V (pi (Imp a (All (ren S a))))))).
Proof.
  apply wkC. rewrite pi_Imp, pi_All, pi_ren.
  apply (tpl_TOP (Imp PA (All PA)) [EXf (V PA); RGf (V PA)] [(ua, pi a)] _ un6); [kt "TplVac"|disch|back].
Qed.

Lemma case_Dist a b : prov Gam (Imp Coh (TOPf (V (pi (Imp (All (Imp a b)) (Imp (All a) (All b))))))).
Proof.
  apply wkC. rewrite !pi_Imp, !pi_All, !pi_Imp.
  apply (tpl_TOP (Imp (All (Imp PC PC1)) (Imp (All PC) (All PC1))) HsDist [(uc, pi a); (ud1, pi b)] _ un6);
    [kt "TplDist"|unfold HsDist; disch|back].
Qed.

Lemma case_Refl x : prov Gam (Imp Coh (TOPf (V (pi (Eqv x x))))).
Proof.
  apply wkC. rewrite pi_Eqv.
  apply (tpl_TOP (Eqv 0 0) [] [] _ (fun _ => x)); [kt "TplRefl"|disch|reflexivity].
Qed.

Lemma case_Leib a x y :
  prov Gam (Imp Coh (TOPf (V (pi (Imp (Eqv x y) (Imp (ren (scons x sid) a) (ren (scons y sid) a))))))).
Proof.
  apply wkC. rewrite !pi_Imp, pi_Eqv, !pi_ren.
  apply (tpl_TOP (Imp (Eqv 0 1) (Imp PC (Pr uc [1]))) [EXf (V PC); SUBf vz (Pr uc [2]) 2 0 1] [(uc, pi a)] _
    (fun i => match i with 0 => x | 1 => y | _ => i - 6 end)); [kt "TplLeib"|disch|back].
Qed.

Lemma case_ZFC i : i < 7 -> prov Gam (Imp Coh (TOPf (V (pi (axf i))))).
Proof.
  intros Hi. rewrite (pi_fix _ (axf_pure i Hi)). apply wkC. apply prov_nohyp.
  destruct i as [|[|[|[|[|[|[|i]]]]]]]; [kt "TplExt"|kt "TplPair"|kt "TplUnion"|kt "TplPower"|kt "TplInf"|kt "TplFound"
    |kt "TplChoice"|lia].
Qed.

Lemma case_Sep g : prov Gam (Imp Coh (TOPf (V (pi (SepF g))))).
Proof.
  apply wkC. rewrite pi_Sep.
  apply (tpl_TOP (SepF PF) HsSep [(uf, pi g)] _ un6); [kt "TplSep"|unfold HsSep; disch|back].
Qed.

Lemma case_Coll g : prov Gam (Imp Coh (TOPf (V (pi (CollF g))))).
Proof.
  apply wkC. rewrite pi_Coll.
  apply (tpl_TOP (CollF (Pr ug [1; 0; 2])) HsColl [(ug, ren swap01 (pi g))] _ un6); [kt "TplColl"|unfold HsColl; disch|back].
Qed.

Lemma case_Def d s : In d D0 -> prov Gam (Imp Coh (TOPf (V (pi (ren s (defax d)))))).
Proof.
  intros Hd. destruct (pi_defax d s Hd) as [X [E P]]. rewrite E. apply wkC.
  apply (tpl_TOP (Qf PA PA) [EXf (V PA); RGf (V PA); UQf (V PA)] [(ua, X)] _ un6); [kt "TplIff"|disch|back].
Qed.

(* modus ponens: TplMp, lifted over Coh(pp) *)
Lemma case_MP a b : prov Gam (Imp Coh (TOPf (V (pi a)))) -> prov Gam (Imp Coh (TOPf (V (pi (Imp a b))))) ->
  prov Gam (Imp Coh (TOPf (V (pi b)))).
Proof.
  intros H1 H2. rewrite pi_Imp in H2. set (l := [(ua, pi a); (ub, pi b)]).
  assert (D : prov (fun g => Gam g \/ In g [RGf (V PB); UQf (V PA)])
    (Imp (Kf (TOPf (V PA)) (TOPf (V (Imp PA PB)))) (TOPf (V PB)))) by kt "TplMp".
  assert (D1 : prov Gam (psub (vtau l) (fun j => 1 + sh6 j) (Imp (Kf (TOPf (V PA)) (TOPf (V (Imp PA PB)))) (TOPf (V PB)))))
    by (apply (apply_T _ _ l sh6 D P7_sh6); disch).
  rewrite psub_Imp, psub_Kf, !concl_TOP in D1.
  pose proof (prov_Gam_ren _ D1 (up un6)) as D2. rewrite ren_Imp, ren_Kf in D2. unfold V in D2.
  rewrite <- !(TOP_ren vz) in D2.
  assert (E1 : ren un6 (psub (otau l) sh6 PA) = pi a) by back.
  assert (E2 : ren un6 (psub (otau l) sh6 (Imp PA PB)) = Imp (pi a) (pi b)) by back.
  assert (E3 : ren un6 (psub (otau l) sh6 PB) = pi b) by back.
  rewrite E1, E2, E3 in D2.
  apply (mp2 _ _ _ _ H1 H2). apply (p_mp _ _ _ D2).
  pose proof (ptaut_prov Gam
    (PI (PI (PN (PI (PV 1) (PN (PV 2)))) (PV 3)) (PI (PI (PV 0) (PV 1)) (PI (PI (PV 0) (PV 2)) (PI (PV 0) (PV 3)))))
    (lv [Coh; TOPf (V (pi a)); TOPf (V (Imp (pi a) (pi b))); TOPf (V (pi b))]) ltac:(vm_compute; reflexivity)) as T.
  exact T.
Qed.

(* generalization: TplGen; Coh(pp) does not mention the generalized variable *)
Lemma psub_swap tau rho X : (forall j, 2 <= rho j) -> psub tau rho (ren swap01 X) = ren swap01 (psub tau rho X).
Proof.
  intros H. rewrite ren_psub. apply psub_ext. intros j. specialize (H j). unfold swap01.
  destruct (rho j) as [|[|m]]; [lia|lia|reflexivity].
Qed.

Lemma case_Gen a : prov Gam (Imp Coh (TOPf (V (pi a)))) -> prov Gam (Imp Coh (TOPf (V (pi (All a))))).
Proof.
  intros H. rewrite pi_All. set (l := [(uc, pi a)]).
  assert (D : prov (fun g => Gam g \/ In g []) (Imp (All (ren swap01 (TOPf (V PC)))) (TOPf (V (All PC))))) by kt "TplGen".
  assert (D1 : prov Gam (psub (vtau l) (fun j => 1 + sh6 j) (Imp (All (ren swap01 (TOPf (V PC)))) (TOPf (V (All PC))))))
    by (apply (apply_T _ _ l sh6 D P7_sh6); disch).
  change (prov Gam (Imp (All (psub (vtau l) (fun j => S (1 + sh6 j)) (ren swap01 (TOPf (V PC)))))
    (psub (vtau l) (fun j => 1 + sh6 j) (TOPf (V (All PC)))))) in D1.
  rewrite psub_swap in D1 by (intros j; unfold sh6; lia).
  rewrite (psub_ext _ (vtau l) (fun j => S (1 + sh6 j)) (fun j => 1 + S (sh6 j))) in D1 by reflexivity.
  rewrite !concl_TOP in D1.
  pose proof (prov_Gam_ren _ D1 (up un6)) as D2. rewrite ren_Imp in D2.
  change (ren (up un6) (All (ren swap01 (TOPf (V (psub (otau l) (fun j => S (sh6 j)) PC))))))
    with (All (ren (up (up un6)) (ren swap01 (TOPf (V (psub (otau l) (fun j => S (sh6 j)) PC)))))) in D2.
  assert (Sw : forall Y, ren (up (up un6)) (ren swap01 Y) = ren swap01 (ren (up (up un6)) Y))
    by (intros Y; rewrite !ren_comp; apply ren_ext; intros [|[|n]]; reflexivity).
  rewrite Sw in D2. unfold V in D2. rewrite <- !(TOP_ren vz) in D2.
  assert (E1 : ren (up un6) (psub (otau l) (fun j => S (sh6 j)) PC) = pi a) by back.
  assert (E2 : ren un6 (psub (otau l) sh6 (All PC)) = All (pi a)) by back.
  rewrite E1, E2 in D2.
  (* D2 : A x (swap TOP(V(pi a))) -> TOP(V(A x pi a)); from H by generalization and vacuous quantification over Coh *)
  pose proof (prov_Gam_ren _ H swap01) as H1. rewrite ren_Imp in H1.
  change (ren swap01 Coh) with (Pr coh [1]) in H1.
  pose proof (all_imp _ _ _ H1) as H2.
  pose proof (p_vac Gam Coh) as H3. change (ren S Coh) with (Pr coh [1]) in H3.
  apply (mp2 _ _ _ _ H3 H2). apply (p_mp _ _ _ D2).
  pose proof (ptaut_prov Gam
    (PI (PI (PV 2) (PV 3)) (PI (PI (PV 0) (PV 1)) (PI (PI (PV 1) (PV 2)) (PI (PV 0) (PV 3)))))
    (lv [Coh; All (Pr coh [1]); All (ren swap01 (TOPf (val vz (pi a)))); TOPf (val vz (All (pi a)))])
    ltac:(vm_compute; reflexivity)) as T.
  exact T.
Qed.

(* ---- the induction *)
Theorem claim : TNOTCH -> forall f, prov Gam0 f -> prov Gam (Imp Coh (TOPf (V (pi f)))).
Proof.
  intros TN f D. induction D as [f Hf|a b|a b c|a b|a b D1 IH1 D2 IH2|a D IH|a y|a|a b|x|a x y].
  - destruct Hf as [[i [Hi ->]]|[[g ->]|[[g ->]|[[d [s [Hd ->]]]| ->]]]].
    + apply case_ZFC. exact Hi.
    + apply case_Sep.
    + apply case_Coll.
    + apply case_Def. exact Hd.
    + exact (notch_value TN).
  - apply case_K.
  - apply case_S.
  - apply case_C.
  - exact (case_MP a b IH1 IH2).
  - exact (case_Gen a IH).
  - apply case_Inst.
  - apply case_Vac.
  - apply case_Dist.
  - apply case_Refl.
  - apply case_Leib.
Qed.
End C.
