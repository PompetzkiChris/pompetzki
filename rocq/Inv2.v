(* Inv2.v - from the kernel's interface theorems to every formula: the value invariants EX UQ RG hold for the value of
   every pure formula (no predicate symbols), and SUB for every pure formula, hole and pair of variables.
   KERNEL is the bridge: each interface theorem, as the kernel's text parses, is derivable from Gam and the placeholder
   hypotheses its kernel record names (runs/r_tpl1-01). *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Use Sub.
Import ListNotations.
Open Scope nat_scope.

Definition iface_names : list string := map (fun e => match e with (n, _, _, _) => n end) iface.
Definition iface_hyps (n : string) : list string :=
  match find (fun e => match e with (m, _, _, _) => String.eqb m n end) iface with Some (_, _, _, hs) => hs | None => [] end.
Definition hyps_named (hs : list string) : list form := somes (map phy hs).
Definition KERNEL : Prop := forall n f, existsb (String.eqb n) iface_names = true -> pif n = Some f ->
  prov (fun g => Gam g \/ In g (hyps_named (iface_hyps n))) f.

Lemma Gam_psub l rho f : Gam f -> Gam (psub (vtau l) rho f).
Proof.
  intros [[i [Hi ->]]|[[g ->]|[[g ->]|[d [s [Hd ->]]]]]].
  - left. exists i. split; auto. apply psub_none. rewrite (axf_pure i Hi). simpl. tauto.
  - right; left. rewrite SepF_psub. eexists; reflexivity.
  - right; right; left. rewrite CollF_psub. eexists; reflexivity.
  - right; right; right. exists d, s. split; auto. apply psub_none. intros p Hp. rewrite syms_ren in Hp.
    apply vtau_none_notv. exact (defs_avoid_in d p Hd Hp).
Qed.

Lemma instT (T : form) (Hs : list form) (l : list (nat * form)) (P : (nat -> nat) -> Prop) :
  prov (fun g => Gam g \/ In g Hs) T ->
  (forall rho, P rho -> P (fun j => S (rho j))) ->
  (forall rho h, P rho -> In h Hs -> prov Gam (psub (vtau l) rho h)) ->
  forall rho, P rho -> prov Gam (psub (vtau l) rho T).
Proof.
  intros D HP HH. apply (prov_psub_to (fun g => Gam g \/ In g Hs) Gam (vtau l) P HP); [|exact D].
  intros rho f Pr0 [G|I]; [apply p_ax; apply Gam_psub; exact G|apply HH; assumption].
Qed.

Definition P7 (rho : nat -> nat) : Prop := forall j, 7 <= rho j.
Lemma P7_S rho : P7 rho -> P7 (fun j => S (rho j)).
Proof. intros H j. specialize (H j). lia. Qed.

Lemma shift_back rho : P7 rho -> forall j, rho j = 1 + (rho j - 1).
Proof. intros H j. specialize (H j). lia. Qed.

(* ---- the placeholder hypotheses EX UQ RG, instantiated *)
Lemma hyp_EX l p th args rho : otau l p = Some th -> P7 rho -> prov Gam (EXf (V th)) ->
  prov Gam (psub (vtau l) rho (EXf (V (Pr p args)))).
Proof.
  intros Ho Hr D. rewrite (psub_ext _ (vtau l) rho (fun j => 1 + (rho j - 1))) by (apply shift_back; exact Hr).
  unfold V. rewrite <- (EX_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l)). simpl. rewrite Ho.
  rewrite EX_ren. apply prov_Gam_ren. exact D.
Qed.

Lemma hyp_UQ l p th args rho : otau l p = Some th -> P7 rho -> prov Gam (UQf (V th)) ->
  prov Gam (psub (vtau l) rho (UQf (V (Pr p args)))).
Proof.
  intros Ho Hr D. rewrite (psub_ext _ (vtau l) rho (fun j => 1 + (rho j - 1))) by (apply shift_back; exact Hr).
  unfold V. rewrite <- (UQ_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l)). simpl. rewrite Ho.
  rewrite UQ_ren. apply prov_Gam_ren. exact D.
Qed.

Lemma hyp_RG l p th args rho : otau l p = Some th -> P7 rho -> prov Gam (RGf (V th)) ->
  prov Gam (psub (vtau l) rho (RGf (V (Pr p args)))).
Proof.
  intros Ho Hr D. rewrite (psub_ext _ (vtau l) rho (fun j => 1 + (rho j - 1))) by (apply shift_back; exact Hr).
  unfold V. rewrite <- (RG_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l)). simpl. rewrite Ho.
  rewrite RG_ren. apply prov_Gam_ren. exact D.
Qed.

(* the conclusion of a template at rho = 1 + rho0 *)
Lemma concl_EX l F rho0 : psub (vtau l) (fun j => 1 + rho0 j) (EXf (V F)) = EXf (V (psub (otau l) rho0 F)).
Proof. unfold V. rewrite (EX_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l)). reflexivity. Qed.
Lemma concl_UQ l F rho0 : psub (vtau l) (fun j => 1 + rho0 j) (UQf (V F)) = UQf (V (psub (otau l) rho0 F)).
Proof. unfold V. rewrite (UQ_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l)). reflexivity. Qed.
Lemma concl_RG l F rho0 : psub (vtau l) (fun j => 1 + rho0 j) (RGf (V F)) = RGf (V (psub (otau l) rho0 F)).
Proof. unfold V. rewrite (RG_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l)). reflexivity. Qed.
Lemma concl_TOP l F rho0 : psub (vtau l) (fun j => 1 + rho0 j) (TOPf (V F)) = TOPf (V (psub (otau l) rho0 F)).
Proof. unfold V. rewrite (TOP_psub vz (otau l) (vtau l) (vtau_sym l) (vtau_base l)). reflexivity. Qed.

Lemma prov_nohyp T : prov (fun g => Gam g \/ In g []) T -> prov Gam T.
Proof. apply prov_cut. intros f [G|[]]. apply p_ax. exact G. Qed.

Lemma ren_inst0 (f : form) (rho : nat -> nat) : (forall i, rho i = i) -> ren (inst_args [] rho) f = f.
Proof. intros H. apply ren_id'. intros i. unfold inst_args. simpl. rewrite Nat.sub_0_r. apply H. Qed.

Lemma ren_inst1 (f : form) : ren (inst_args [0] S) f = f.
Proof. apply ren_id'. intros [|i]; unfold inst_args; simpl; [reflexivity|rewrite Nat.sub_0_r; reflexivity]. Qed.

Section K.
Hypothesis K : KERNEL.

Lemma useK n T Hs : existsb (String.eqb n) iface_names = true -> pif n = Some T -> hyps_named (iface_hyps n) = Hs ->
  prov (fun g => Gam g \/ In g Hs) T.
Proof. intros E P H. rewrite <- H. apply K; assumption. Qed.

Ltac kt := apply useK; vm_compute; reflexivity.

(* a template at rho = 1 + rho0, with every placeholder hypothesis discharged *)
Lemma apply_T T Hs l rho0 : prov (fun g => Gam g \/ In g Hs) T -> P7 (fun j => 1 + rho0 j) ->
  (forall rho h, P7 rho -> In h Hs -> prov Gam (psub (vtau l) rho h)) ->
  prov Gam (psub (vtau l) (fun j => 1 + rho0 j) T).
Proof. intros D P H. apply (instT T Hs l P7 D P7_S H). exact P. Qed.

End K.

(* ---- renaming a result back *)
Lemma back_EX F G s : ren s F = G -> prov Gam (EXf (V F)) -> prov Gam (EXf (V G)).
Proof. intros <- D. unfold V. rewrite EX_ren. apply prov_Gam_ren. exact D. Qed.
Lemma back_UQ F G s : ren s F = G -> prov Gam (UQf (V F)) -> prov Gam (UQf (V G)).
Proof. intros <- D. unfold V. rewrite UQ_ren. apply prov_Gam_ren. exact D. Qed.
Lemma back_RG F G s : ren s F = G -> prov Gam (RGf (V F)) -> prov Gam (RGf (V G)).
Proof. intros <- D. unfold V. rewrite RG_ren. apply prov_Gam_ren. exact D. Qed.
Lemma back_TOP F G s : ren s F = G -> prov Gam (TOPf (V F)) -> prov Gam (TOPf (V G)).
Proof. intros <- D. unfold V. rewrite TOP_ren. apply prov_Gam_ren. exact D. Qed.

Definition sh6 (j : nat) : nat := 6 + j.
Definition un6 (i : nat) : nat := i - 6.
Lemma P7_sh6 : P7 (fun j => 1 + sh6 j). Proof. intros j. unfold sh6. lia. Qed.

Lemma un6_0 (f : form) : ren un6 (ren (inst_args [] sh6) f) = f.
Proof. rewrite ren_comp. apply ren_id'. intros i. unfold un6, inst_args, sh6. simpl. lia. Qed.
Lemma un6_1 (f : form) : ren (up un6) (ren (inst_args [0] (fun j => S (sh6 j))) f) = f.
Proof. rewrite ren_comp. apply ren_id'. intros [|i]; unfold un6, inst_args, sh6; simpl; [reflexivity|]. f_equal. lia. Qed.

Section Inv.
Hypothesis K : KERNEL.

Ltac kt n := apply (useK K n); vm_compute; reflexivity.

(* instantiate a template T (hypotheses Hs) for the list l at parameters 6 + j, then conclude with the concl_ lemma *)
Lemma via_EX F Hs l : prov (fun g => Gam g \/ In g Hs) (EXf (V F)) ->
  (forall rho h, P7 rho -> In h Hs -> prov Gam (psub (vtau l) rho h)) -> prov Gam (EXf (V (psub (otau l) sh6 F))).
Proof. intros D H. rewrite <- concl_EX. apply (apply_T _ Hs l sh6 D P7_sh6 H). Qed.
Lemma via_UQ F Hs l : prov (fun g => Gam g \/ In g Hs) (UQf (V F)) ->
  (forall rho h, P7 rho -> In h Hs -> prov Gam (psub (vtau l) rho h)) -> prov Gam (UQf (V (psub (otau l) sh6 F))).
Proof. intros D H. rewrite <- concl_UQ. apply (apply_T _ Hs l sh6 D P7_sh6 H). Qed.
Lemma via_RG F Hs l : prov (fun g => Gam g \/ In g Hs) (RGf (V F)) ->
  (forall rho h, P7 rho -> In h Hs -> prov Gam (psub (vtau l) rho h)) -> prov Gam (RGf (V (psub (otau l) sh6 F))).
Proof. intros D H. rewrite <- concl_RG. apply (apply_T _ Hs l sh6 D P7_sh6 H). Qed.

Theorem inv_all f : syms f = [] -> prov Gam (EXf (V f)) /\ prov Gam (UQf (V f)) /\ prov Gam (RGf (V f)).
Proof.
  induction f; intros Hp; simpl in Hp; try discriminate.
  - assert (E : Mem n n0 = ren (fun i => match i with 0 => n | 1 => n0 | _ => i end) (Mem 0 1)) by reflexivity.
    rewrite E. unfold V. rewrite EX_ren, UQ_ren, RG_ren. repeat split; apply prov_Gam_ren; apply prov_nohyp.
    + kt "TplEex". + kt "TplEuq". + kt "TplErg".
  - assert (E : Eqv n n0 = ren (fun i => match i with 0 => n | 1 => n0 | _ => i end) (Eqv 0 1)) by reflexivity.
    rewrite E. unfold V. rewrite EX_ren, UQ_ren, RG_ren. repeat split; apply prov_Gam_ren; apply prov_nohyp.
    + kt "TplQex". + kt "TplQuq". + kt "TplQrg".
  - destruct (IHf Hp) as (E1 & U1 & R1). set (l := [(ua, f)]).
    assert (O : otau l ua = Some f) by reflexivity.
    assert (B : ren un6 (psub (otau l) sh6 (Neg PA)) = Neg f).
    { simpl. try rewrite O. f_equal. apply un6_0. }
    repeat split.
    + apply (back_EX _ _ un6 B). apply (via_EX _ [EXf (V PA)] l); [kt "TplNex"|].
      intros rho h Pr0 [<-|[]]. apply (hyp_EX l ua f [] rho O Pr0 E1).
    + apply (back_UQ _ _ un6 B). apply (via_UQ _ [UQf (V PA)] l); [kt "TplNuq"|].
      intros rho h Pr0 [<-|[]]. apply (hyp_UQ l ua f [] rho O Pr0 U1).
    + apply (back_RG _ _ un6 B). apply (via_RG _ [RGf (V PA)] l); [kt "TplNrg"|].
      intros rho h Pr0 [<-|[]]. apply (hyp_RG l ua f [] rho O Pr0 R1).
  - apply app_eq_nil in Hp as [Hp1 Hp2].
    destruct (IHf1 Hp1) as (E1 & U1 & R1). destruct (IHf2 Hp2) as (E2 & U2 & R2). set (l := [(ua, f1); (ub, f2)]).
    assert (O1 : otau l ua = Some f1) by reflexivity. assert (O2 : otau l ub = Some f2) by reflexivity.
    assert (B : ren un6 (psub (otau l) sh6 (Imp PA PB)) = Imp f1 f2).
    { simpl. try rewrite O1. try rewrite O2. f_equal; apply un6_0. }
    repeat split.
    + apply (back_EX _ _ un6 B). apply (via_EX _ [EXf (V PA); EXf (V PB)] l); [kt "TplIex"|].
      intros rho h Pr0 [<-|[<-|[]]]; [apply (hyp_EX l ua f1 [] rho O1 Pr0 E1)|apply (hyp_EX l ub f2 [] rho O2 Pr0 E2)].
    + apply (back_UQ _ _ un6 B). apply (via_UQ _ [UQf (V PA); UQf (V PB)] l); [kt "TplIuq"|].
      intros rho h Pr0 [<-|[<-|[]]]; [apply (hyp_UQ l ua f1 [] rho O1 Pr0 U1)|apply (hyp_UQ l ub f2 [] rho O2 Pr0 U2)].
    + apply (back_RG _ _ un6 B). apply (via_RG _ [RGf (V PA)] l); [kt "TplIrg"|].
      intros rho h Pr0 [<-|[]]. apply (hyp_RG l ua f1 [] rho O1 Pr0 R1).
  - destruct (IHf Hp) as (E1 & U1 & R1). set (l := [(uc, f)]).
    assert (O : otau l uc = Some f) by reflexivity.
    assert (B : ren un6 (psub (otau l) sh6 (All (Pr uc [0]))) = All f).
    { simpl. try rewrite O. f_equal. apply un6_1. }
    repeat split.
    + apply (back_EX _ _ un6 B). apply (via_EX _ [] l); [kt "TplAex"|]. intros rho h _ [].
    + apply (back_UQ _ _ un6 B). apply (via_UQ _ [] l); [kt "TplAuq"|]. intros rho h _ [].
    + apply (back_RG _ _ un6 B).
      apply (via_RG _ [EXf (V (Pr uc [0])); RGf (V (Pr uc [0])); UQf (V (Pr uc [0]))] l); [kt "TplArg"|].
      intros rho h Pr0 [<-|[<-|[<-|[]]]].
      * apply (hyp_EX l uc f [0] rho O Pr0 E1).
      * apply (hyp_RG l uc f [0] rho O Pr0 R1).
      * apply (hyp_UQ l uc f [0] rho O Pr0 U1).
Qed.
End Inv.
