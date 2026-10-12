(* Replay3.v - soundness of the checker: a step, a run of lines, a theorem, a batch. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Sub Expand Replay ReplayT Replay2.
Import ListNotations.
Open Scope nat_scope.

Section S.
Variable hypf : N -> form.
Notation AH := (AH hypf).
Notation reg_ok := (reg_ok hypf).

Lemma nthN_In {A : Type} (l : list A) i x : nthN l i = Some x -> In x l.
Proof. unfold nthN. apply nth_error_In. Qed.

Lemma specn_ok hs F ts G : prov (AH hs) F -> specn F ts = Some G -> prov (AH hs) G.
Proof.
  revert F. induction ts as [|t r IH]; intros F D E; simpl in E.
  - injection E as <-. exact D.
  - destruct F; try discriminate. apply (IH _ (p_mp _ _ _ D (p_inst _ F (N.to_nat t))) E).
Qed.

Lemma prems_ok lines ls ps hs : (forall l, In l lines -> prov (AH hs) l) -> prems lines ls = Some ps ->
  forall p, In p ps -> prov (AH hs) p.
Proof.
  revert ps. induction ls as [|l r IH]; intros ps Hl E; simpl in E.
  - injection E as <-. intros p [].
  - destruct (nthN lines l) as [f|] eqn:F; [|discriminate]. destruct (prems lines r) as [fs|] eqn:R; [|discriminate].
    injection E as <-. intros p [<-|Hp]; [apply Hl; exact (nthN_In _ _ _ F)|exact (IH fs Hl eq_refl p Hp)].
Qed.

Lemma fold_mp hs G ps : (forall p, In p ps -> prov (AH hs) p) -> prov (AH hs) (fold_right Imp G ps) -> prov (AH hs) G.
Proof.
  induction ps as [|p r IH]; intros Hp D; simpl in D; [exact D|].
  apply IH; [intros q Hq; apply Hp; right; exact Hq|]. exact (p_mp _ _ _ (Hp p (or_introl eq_refl)) D).
Qed.

Lemma sstep_ok reg lines hs st fo ho : reg_ok reg -> (forall l, In l lines -> prov (AH hs) l) ->
  sstep reg lines st = Some (fo, ho) -> prov (AH (hs ++ ho)) fo.
Proof.
  intros R L E. destruct st as [r sig|l ts|l k|i j|ls g|t g|l k g|k l g|t g|a g|g]; simpl in E.
  - destruct (nthN reg r) as [[d h0]|] eqn:N0; [|discriminate]. injection E as <- <-.
    apply (AH_mono hypf h0). { intros x Hx. apply in_or_app. right. exact Hx. }
    apply ren_adm. exact (R _ _ _ N0).
  - destruct (nthN lines l) as [F|] eqn:N0; [|discriminate]. destruct (specn F ts) as [G|] eqn:S0; [|discriminate].
    simpl in E. injection E as <- <-. rewrite app_nil_r. exact (specn_ok _ _ _ _ (L _ (nthN_In _ _ _ N0)) S0).
  - destruct (nthN lines l) as [F|] eqn:N0; [|discriminate]. injection E as <- <-. rewrite app_nil_r.
    apply gen_k. exact (L _ (nthN_In _ _ _ N0)).
  - destruct (nthN lines i) as [a|] eqn:N1; [|discriminate]. destruct (nthN lines j) as [[| | | |a' b|]|] eqn:N2; try discriminate.
    destruct (form_eqb a a') eqn:Q; [|discriminate]. injection E as <- <-. rewrite app_nil_r.
    apply form_eqb_true in Q. subst a'. exact (p_mp _ _ _ (L _ (nthN_In _ _ _ N1)) (L _ (nthN_In _ _ _ N2))).
  - destruct (prems lines ls) as [ps|] eqn:P; [|discriminate]. destruct (tautchk2 _) eqn:T; [|discriminate].
    injection E as <- <-. rewrite app_nil_r. apply (fold_mp _ _ ps); [exact (prems_ok _ _ _ _ L P)|].
    apply tautchk2_prov. exact T.
  - destruct (tof g) as [| | | |F [| | |[| | | | |[| | |f| |]]| |]|] eqn:G; try discriminate.
    destruct (form_eqb F _) eqn:Q; [|discriminate]. injection E as <- <-. rewrite app_nil_r.
    apply form_eqb_true in Q. subst F. apply rule_exi.
  - destruct (tof g) as [| | | |[| | |[| | | | |[| | |P'| |]]| |] G2|] eqn:G; try discriminate;
      destruct (nthN lines l) as [[| | | |P G3|]|] eqn:N0; try discriminate.
    destruct (form_eqb G2 G3 && form_eqb P' _ && negb _) eqn:Q; [|discriminate]. injection E as <- <-. rewrite app_nil_r.
    apply andb_true_iff in Q as [Q Q3]. apply andb_true_iff in Q as [Q1 Q2]. apply form_eqb_true in Q1, Q2.
    apply negb_true_iff in Q3. subst. apply rule_exel; [exact Q3|exact (L _ (nthN_In _ _ _ N0))].
  - destruct (tof g) as [| | | |H [| | | | |f']|] eqn:G; try discriminate;
      destruct (nthN lines l) as [[| | | |H2 f|]|] eqn:N0; try discriminate.
    destruct (form_eqb H H2 && form_eqb f' _ && negb _) eqn:Q; [|discriminate]. injection E as <- <-. rewrite app_nil_r.
    apply andb_true_iff in Q as [Q Q3]. apply andb_true_iff in Q as [Q1 Q2]. apply form_eqb_true in Q1, Q2.
    apply negb_true_iff in Q3. subst. apply rule_alli; [exact Q3|exact (L _ (nthN_In _ _ _ N0))].
  - destruct (tof g) as [| | | |[| | | | |f] G2|] eqn:G; try discriminate.
    destruct (form_eqb G2 _) eqn:Q; [|discriminate]. injection E as <- <-. rewrite app_nil_r.
    apply form_eqb_true in Q. subst. apply p_inst.
  - destruct (tof g) as [| | | |[|s t| | | |] [| | | |X Y|]|] eqn:G; try discriminate.
    destruct (form_eqb X _ && form_eqb Y _) eqn:Q; [|discriminate]. injection E as <- <-. rewrite app_nil_r.
    apply andb_true_iff in Q as [Q1 Q2]. apply form_eqb_true in Q1, Q2. subst. apply p_leib.
  - destruct (axshape (tof g)) eqn:A0; [|discriminate]. injection E as <- <-. rewrite app_nil_r.
    apply axshape_ok. exact A0.
Qed.

Lemma run_ok reg sts : reg_ok reg -> forall lines hs lines' hs', (forall l, In l lines -> prov (AH hs) l) ->
  run reg lines hs sts = Some (lines', hs') -> forall l, In l lines' -> prov (AH hs') l.
Proof.
  intros R. induction sts as [|st r IH]; intros lines hs lines' hs' L E; simpl in E.
  - injection E as <- <-. exact L.
  - destruct (sstep reg lines st) as [[f h]|] eqn:S0; [|discriminate]. apply (IH (lines ++ [f]) (hs ++ h) lines' hs'); [|exact E].
    intros l Hl. apply in_app_or in Hl as [Hl|[<-|[]]].
    + apply (AH_mono hypf hs); [intros x Hx; apply in_or_app; left; exact Hx|]. exact (L _ Hl).
    + exact (sstep_ok _ _ _ _ _ _ R L S0).
Qed.

Lemma idxn_nth l i : nodupb l = true -> i < length l -> idxn (nth i l 0) l = i.
Proof.
  revert i. induction l as [|x r IH]; intros i N Li; simpl in *; [lia|].
  apply andb_true_iff in N as [N1 N2]. destruct i as [|i]; simpl; [rewrite Nat.eqb_refl; reflexivity|].
  destruct (Nat.eqb (nth i r 0) x) eqn:E.
  - exfalso. apply Nat.eqb_eq in E. apply negb_true_iff in N1.
    assert (existsb (Nat.eqb x) r = true) by (apply existsb_exists; exists (nth i r 0); split; [apply nth_In; lia|rewrite E; apply Nat.eqb_refl]).
    congruence.
  - f_equal. apply IH; [exact N2|lia].
Qed.

Lemma subsetb_incl a b : subsetb a b = true -> incl a b.
Proof.
  unfold subsetb. intros H x Hx. rewrite forallb_forall in H. specialize (H x Hx).
  apply existsb_exists in H as [y [Hy E]]. apply N.eqb_eq in E. subst. exact Hy.
Qed.

Lemma last_mem (l : list form) d : l <> [] -> In (last l d) l.
Proof.
  induction l as [|x r IH]; intros H; [congruence|]. destruct r as [|y r]; [left; reflexivity|].
  right. apply IH. discriminate.
Qed.

Theorem check_thm_ok reg t : reg_ok reg -> check_thm reg t = true -> prov (AH (t_hyps t)) (tof (t_stmt t)).
Proof.
  intros R C. unfold check_thm in C. destruct (run reg [] [] (t_steps t)) as [[lines hs]|] eqn:E; [|discriminate].
  repeat (apply andb_true_iff in C as [C ?]).
  match goal with H : negb (Nat.eqb (length lines) 0) = true |- _ => rename H into Hn end.
  match goal with H : subsetb hs (t_hyps t) = true |- _ => rename H into Hs end.
  match goal with H : closedk _ _ = true |- _ => rename H into Hc end.
  match goal with H : nodupb _ = true |- _ => rename H into Hd end.
  apply form_eqb_true in C.
  assert (IL : In (last lines Bot) lines).
  { destruct lines as [|x r]; [simpl in Hn; discriminate|]. apply last_mem. discriminate. }
  pose proof (run_ok reg (t_steps t) R [] [] lines hs (fun l H => match H with end) E _ IL) as D.
  rewrite C in D. apply (AH_mono hypf hs); [apply subsetb_incl; exact Hs|].
  pose proof (ren_adm _ _ (fun j => idxn j (map N.to_nat (t_sig t))) D) as D2. rewrite ren_comp in D2.
  rewrite (ren_free _ _ (fun n => n)) in D2; [rewrite ren_id in D2; exact D2|].
  intros i Fi. pose proof (closedk_free _ _ _ Hc Fi) as Li. unfold sigf.
  apply idxn_nth; [exact Hd|rewrite length_map; exact Li].
Qed.

Theorem check_batch_ok reg ts : reg_ok reg -> check_batch reg ts = true -> reg_ok (reg ++ map ent ts).
Proof.
  revert reg. induction ts as [|t r IH]; intros reg R C; simpl in *.
  - rewrite app_nil_r. exact R.
  - apply andb_true_iff in C as [C1 C2].
    assert (R1 : reg_ok (reg ++ [ent t])).
    { intros i d h E. destruct (Nat.lt_ge_cases i (length reg)) as [Li|Li].
      - rewrite nth_error_app1 in E by exact Li. exact (R _ _ _ E).
      - rewrite nth_error_app2 in E by exact Li. destruct (i - length reg) as [|m]; simpl in E.
        + injection E as <- <-. exact (check_thm_ok reg t R C1).
        + destruct m; discriminate. }
    pose proof (IH _ R1 C2) as R2. rewrite <- app_assoc in R2. exact R2.
Qed.
End S.
