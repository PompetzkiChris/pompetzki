(* CX3: faithful expansion of the dependency-closed Stage 2 vocabulary,
   and composition with the existing abstract replay soundness theorem. *)
From Stdlib Require Import List Bool Arith NArith.
From Cohen Require Import Syn Prov Ax Expand Pure Elim Replay2 Replay3 RpInit RpInitOk.
From JudgeLink Require Import JudgeBatch.
From CX3 Require Import Conservativity2.
Import ListNotations.

Definition stage2_symbols : list nat := [5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 72].
Definition stage2_definitions : list (nat * nat * form) :=
  filter (fun d => match d with (p, _, _) => existsb (Nat.eqb p) stage2_symbols end) Dall.
Definition stage2_table : list (nat * nat * form) :=
  Eval vm_compute in buildT Pr [] stage2_definitions.
Definition stage2_expand (f : form) : form := expD Pr stage2_table f.

Lemma stage2_definitions_count : length stage2_definitions = 11.
Proof. vm_compute. reflexivity. Qed.

Lemma stage2_definitions_in d : In d stage2_definitions -> In d Dall.
Proof. unfold stage2_definitions. intros H. apply filter_In in H. exact (proj1 H). Qed.

Lemma stage2_table_good : Good stage2_table.
Proof. apply buildT_good; [exact stage2_definitions_in|exact good_nil]. Qed.

Lemma stage2_table_pure_check :
  forallb (fun d => match d with (_, _, B) =>
    match syms B with [] => true | _ => false end end) stage2_table = true.
Proof. vm_compute. reflexivity. Qed.

Lemma stage2_table_entry_pure p k B :
  tlook stage2_table p = Some (k, B) -> syms B = [].
Proof.
  intros E. apply tlook_in in E.
  pose proof stage2_table_pure_check as C. rewrite forallb_forall in C.
  specialize (C _ E). simpl in C.
  destruct (syms B); [reflexivity|discriminate].
Qed.

Fixpoint covered (T : list (nat * nat * form)) (f : form) : bool :=
  match f with
  | Mem _ _ | Eqv _ _ => true
  | Pr p args => match tlook T p with
                | Some (k, _) => Nat.eqb (length args) k
                | None => false
                end
  | Neg g | All g => covered T g
  | Imp g h => covered T g && covered T h
  end.

Theorem covered_expansion_pure T
    (Hp : forall p k B, tlook T p = Some (k, B) -> syms B = []) f :
  covered T f = true -> syms (expD Pr T f) = [].
Proof.
  induction f; simpl; intros C; try reflexivity.
  - destruct (tlook T n) as [[k B]|] eqn:E; [|discriminate].
    rewrite C. rewrite syms_ren. exact (Hp n k B E).
  - exact (IHf C).
  - apply andb_true_iff in C as [C1 C2]. rewrite (IHf1 C1), (IHf2 C2). reflexivity.
  - exact (IHf C).
Qed.

Theorem stage2_expand_pure f :
  covered stage2_table f = true -> syms (stage2_expand f) = [].
Proof. apply covered_expansion_pure. exact stage2_table_entry_pure. Qed.

Theorem stage2_expansion_equivalent f : prov Gam (Qf f (stage2_expand f)).
Proof. apply repl. exact stage2_table_good. Qed.

Theorem stage2_theorem_pure f :
  covered stage2_table f = true -> prov Gam f -> prov ZFpure (stage2_expand f).
Proof.
  intros C D. apply expanded_theorem_pure;
    [exact stage2_table_good|apply stage2_expand_pure; exact C|exact D].
Qed.

Lemma AH_nil_to_Gam (hypothesis : N -> form) f :
  prov (AH hypothesis []) f -> prov Gam f.
Proof.
  apply prov_mono. intros g [G|[h [Hh E]]]; [exact G|contradiction].
Qed.

Theorem accepted_member_Gam (hypothesis : N -> form) reg ts t :
  reg_ok hypothesis reg -> check_batch reg ts = true ->
  In t ts -> t_hyps t = [] -> prov Gam (tof (t_stmt t)).
Proof.
  intros R C H NoHyp.
  pose proof (accepted_member_sound hypothesis reg ts t R C H) as D.
  rewrite NoHyp in D. exact (AH_nil_to_Gam hypothesis _ D).
Qed.

Theorem accepted_expanded_member_pure (hypothesis : N -> form) reg ts t T :
  reg_ok hypothesis reg -> check_batch reg ts = true -> In t ts ->
  t_hyps t = [] -> Good T -> syms (expD Pr T (tof (t_stmt t))) = [] ->
  prov ZFpure (expD Pr T (tof (t_stmt t))).
Proof.
  intros R C H NoHyp G Hp. apply expanded_theorem_pure; [exact G|exact Hp|].
  exact (accepted_member_Gam hypothesis reg ts t R C H NoHyp).
Qed.

Lemma reg_ok_left (hypothesis : N -> form) reg tail :
  reg_ok hypothesis (reg ++ tail) -> reg_ok hypothesis reg.
Proof.
  intros R i d h E. apply (R i d h).
  rewrite nth_error_app1; [exact E|].
  apply nth_error_Some. rewrite E. discriminate.
Qed.

Definition stage2_registry : list entry :=
  map (fun d => (d, [])) AX0 ++ map (fun d => (d, [])) DEF0.

Lemma stage2_registry_count : length stage2_registry = 677.
Proof. vm_compute. reflexivity. Qed.

Lemma stage2_registry_ok : reg_ok RpInitOk.hypf stage2_registry.
Proof.
  apply (reg_ok_left RpInitOk.hypf stage2_registry
    (mapi (fun i d => (d, [N.of_nat i])) 0 HYPD)).
  unfold stage2_registry. rewrite <- app_assoc. exact REG0_ok.
Qed.

Theorem stage2_accepted_member_pure ts t :
  check_batch stage2_registry ts = true -> In t ts -> t_hyps t = [] ->
  covered stage2_table (tof (t_stmt t)) = true ->
  prov ZFpure (stage2_expand (tof (t_stmt t))).
Proof.
  intros C H NoHyp Cov. apply stage2_theorem_pure; [exact Cov|].
  exact (accepted_member_Gam RpInitOk.hypf stage2_registry ts t
    stage2_registry_ok C H NoHyp).
Qed.

Print Assumptions stage2_definitions_count.
Print Assumptions stage2_table_good.
Print Assumptions stage2_table_pure_check.
Print Assumptions covered_expansion_pure.
Print Assumptions stage2_expand_pure.
Print Assumptions stage2_expansion_equivalent.
Print Assumptions stage2_theorem_pure.
Print Assumptions accepted_member_Gam.
Print Assumptions accepted_expanded_member_pure.
Print Assumptions stage2_registry_count.
Print Assumptions stage2_registry_ok.
Print Assumptions stage2_accepted_member_pure.
