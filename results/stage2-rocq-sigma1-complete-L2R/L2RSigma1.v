(* L2RSigma1.v - lane L2R, 2026-10-09. Unbounded existentials in positive places. pos A: some occurs only under
   and, or, the conclusion of imp, the bounded quantifiers and some itself; every other part is bounded.
   Theorem sigma1_complete: a closed pos sentence true in N has prov Gam [s]. Numerals are in omega (NatNum), so a
   witness k of some x A gives exists x (Nat(x) & [A]). Then the 5 Sigma-1 theorems of sigma1's 07-sigma1.jdg too. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Ax RpFinal.
From L2R Require Import L2RLogic L2RArith L2RFin L2RSent L2RCases L2RAgree.
Import ListNotations.
Open Scope nat_scope.

Arguments Emp : simpl never.
Arguments Suc : simpl never.
Arguments NatP : simpl never.

Definition Om (w : nat) : form := Pr 20 [w].
Arguments Om : simpl never.
Lemma ren_Om s w : ren s (Om w) = Om (s w). Proof. reflexivity. Qed.

Lemma F_OmEx : Pv (Xf (Om 0)).
Proof. apply (entry_is_prov 1108). vm_compute. reflexivity. Qed.

Lemma F_ZeroW a b : Pv (Imp (Kf (Om a) (Emp b)) (Mem b a)).
Proof.
  assert (H : Pv (All (All (Imp (Kf (Pr 20 [1]) (Pr 17 [0])) (Mem 0 1))))) by (apply (entry_is_prov 740); vm_compute; reflexivity).
  inst_all H [a; b]. exact H.
Qed.

Lemma F_SucW a b c : Pv (Imp (Kf (Kf (Om a) (Mem b a)) (Suc c b)) (Mem c a)).
Proof.
  assert (H : Pv (All (All (All (Imp (Kf (Kf (Pr 20 [2]) (Mem 1 2)) (Pr 18 [0; 1])) (Mem 0 2))))))
    by (apply (entry_is_prov 741); vm_compute; reflexivity).
  inst_all H [a; b; c]. exact H.
Qed.

Lemma U_Nat x : Pv (Qf (NatP x) (Xf (Kf (Om 0) (Mem (S x) 0)))).
Proof. exact (def_pv 72 1 _ (fun _ => x) ltac:(vm_compute; reflexivity)). Qed.

Lemma NumOm n : forall G w x, D G (Om w) -> D G (Num n x) -> D G (Mem x w).
Proof.
  induction n as [|n IH]; intros G w x Hw Hx.
  - rewrite Num_0 in Hx. exact (D_t1 _ _ _ (F_ZeroW w x) (D_and _ _ _ Hw Hx)).
  - rewrite Num_S in Hx. apply (D_exE2 _ _ _ _ Hx). rs3. rewrite ?ren_Om.
    pose proof (D_sh2 _ (Num n 0) (Suc (S x) 0) _ Hw) as Hw'. rewrite ren_Om in Hw'. cbn in Hw'.
    have M (Mem 0 (S w)). { apply IH; [exact Hw'|hyp]. }
    apply (D_t1 _ (Kf (Kf (Om (S w)) (Mem 0 (S w))) (Suc (S x) 0))); [exact (F_SucW (S w) 0 (S x))|].
    apply D_and; [apply D_and; [exact Hw'|exact M]|hyp].
Qed.

Lemma NatNum n G x : D G (Num n x) -> D G (NatP x).
Proof.
  intros Hx. apply (D_cut _ _ _ Hx). apply (D_exE _ (Om 0)); [apply D_thm; exact F_OmEx|]. rs3. rewrite ?ren_NatP. cbn.
  apply (D_iffr _ _ _ (D_thm _ _ (U_Nat (S x)))). apply (D_exI _ _ 0). rs3. rewrite ?ren_Om. cbn.
  apply D_and; [hyp|]. apply (NumOm n); hyp.
Qed.

(* ---- the positive fragment *)
Fixpoint pos (A : fm) : Prop :=
  match A with
  | feq _ _ | flt _ _ | fle _ _ => True
  | fnot A => bounded A
  | fand A B | fdis A B => pos A /\ pos B
  | fimp A B => bounded A /\ pos B
  | fiff A B => bounded A /\ bounded B
  | fall _ A | fex _ A | falle _ A | fexe _ A => pos A
  | fsome A => pos A
  end.

Lemma Env_bind1 k e rho G : Env e rho G -> forall G', (forall g, In g (map (ren S) G) -> In g G') ->
  In (Num k 0) G' -> Env (k :: e) (scons 0 (shS rho)) G'.
Proof.
  intros H G' I Ik [|i] Hi; [apply D_hyp; exact Ik|]. cbn [nth List.length] in *.
  apply (D_weak _ _ _ I). pose proof (D_ren _ _ S (H i ltac:(lia))) as H'. rewrite ren_Num in H'. exact H'.
Qed.

Ltac ihq IH Hb Hw He k e rho G := match goal with |- D ?G1 _ =>
  apply (IH Hb (k :: e) (rho2 rho) G1 Hw (Env_G2 k e rho G G1 He ltac:(inmap) ltac:(repeat (first [left; reflexivity | right])))) end.

Lemma posmain A : pos A -> forall e rho G, wf (List.length e) A -> Env e rho G -> sat e A -> D G (tr A rho).
Proof.
  induction A as [t u|t u|t u|A IH|A IHA B IHB|A IHA B IHB|A IHA B IHB|A IHA B IHB|t A IH|t A IH|t A IH|t A IH|A IH];
    intros Hp e rho G Hw He Hs.
  - exact (proj1 (main (feq t u) I e rho G Hw He) Hs).
  - exact (proj1 (main (flt t u) I e rho G Hw He) Hs).
  - exact (proj1 (main (fle t u) I e rho G Hw He) Hs).
  - exact (proj1 (main (fnot A) Hp e rho G Hw He) Hs).
  - cbn in *. destruct Hp as [Ha Hb], Hw as [Hwa Hwb], Hs as [S1 S2].
    apply D_and; [exact (IHA Ha e rho G Hwa He S1)|exact (IHB Hb e rho G Hwb He S2)].
  - cbn in *. destruct Hp as [Ha Hb], Hw as [Hwa Hwb].
    destruct Hs as [S1|S2]; [apply D_orl; exact (IHA Ha e rho G Hwa He S1)|apply D_orr; exact (IHB Hb e rho G Hwb He S2)].
  - cbn in *. destruct Hp as [Ha Hb], Hw as [Hwa Hwb].
    destruct (sat_dec A Ha e) as [S1|S1].
    + pose proof (IHB Hb e rho G Hwb He (Hs S1)) as H. dt1 H.
    + pose proof (proj2 (main A Ha e rho G Hwa He) S1) as H. dt1 H.
  - exact (proj1 (main (fiff A B) Hp e rho G Hw He) Hs).
  - cbn in *. destruct Hw as [Ht Hw].
    apply (WrapPos t e rho G _ Ht He). apply D_all. apply D_intro. rs3.
    addh (Disj (ev e t) 0). { apply (D_iffl _ (Mem 0 1)); [apply MemChar; hyp|hyp]. }
    apply DisjE. intros k Hk. ihq IH Hp Hw He k e rho G. exact (Hs k Hk).
  - cbn in *. destruct Hw as [Ht Hw]. destruct Hs as [k [Hk Hs]].
    apply (WrapPos t e rho G _ Ht He). apply (num_exI k). rs3. apply D_and.
    + apply (NumIn k (ev e t)); [exact Hk|hyp|hyp].
    + ihq IH Hp Hw He k e rho G. exact Hs.
  - cbn in *. destruct Hw as [Ht Hw].
    apply (WrapPos t e rho G _ Ht He). apply D_all. apply D_intro. rs3.
    addh (Disj (S (ev e t)) 0). { apply (D_iffl _ (Df (Mem 0 1) (Eqv 0 1))); [apply MemCharLe; hyp|hyp]. }
    apply DisjE. intros k Hk. ihq IH Hp Hw He k e rho G. apply Hs. lia.
  - cbn in *. destruct Hw as [Ht Hw]. destruct Hs as [k [Hk Hs]].
    apply (WrapPos t e rho G _ Ht He). apply (num_exI k). rs3. apply D_and.
    + apply (D_iffr _ _ (Disj (S (ev e t)) 0)); [apply MemCharLe; hyp|].
      apply (D_t1 _ (Num k 0)); [apply DisjI; lia|hyp].
    + ihq IH Hp Hw He k e rho G. exact Hs.
  - cbn in *. destruct Hs as [k Hs]. apply (num_exI k). rs3. apply D_and.
    + apply (NatNum k). hyp.
    + match goal with |- D ?G1 _ =>
        apply (IH Hp (k :: e) (scons 0 (shS rho)) G1 Hw
          (Env_bind1 k e rho G He G1 ltac:(intros ? ?; repeat right; assumption) ltac:(left; reflexivity))) end.
      exact Hs.
Qed.

Theorem sigma1_complete (A : fm) : pos A -> wf 0 A -> sat [] A -> prov Gam (tr A sid).
Proof.
  intros Hp Hw Hs. apply D_nil.
  exact (posmain A Hp [] sid [] Hw (fun i Hi => ltac:(cbn in Hi; lia)) Hs).
Qed.

(* ---- the five Sigma-1 sentences of 07-sigma1.jdg, with their witnesses *)
Definition sigma1_cases : list (string * fm * bool * form) := filter (fun c => match c with (_, A, _, _) => negb (boundedb A) end) cases.
Lemma sigma1_cases_length : List.length sigma1_cases = 5. Proof. vm_compute. reflexivity. Qed.

Fixpoint posb (A : fm) : bool :=
  match A with
  | feq _ _ | flt _ _ | fle _ _ => true
  | fnot A => boundedb A
  | fand A B | fdis A B => posb A && posb B
  | fimp A B => boundedb A && posb B
  | fiff A B => boundedb A && boundedb B
  | fall _ A | fex _ A | falle _ A | fexe _ A => posb A
  | fsome A => posb A
  end.

Lemma posb_ok A : posb A = true -> pos A.
Proof.
  induction A; cbn; intros H; rewrite ?andb_true_iff in H;
    repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
    repeat split; auto using boundedb_ok.
Qed.

(* truth with explicit witnesses for some, searched below a bound; sound for sat *)
Fixpoint evw (n : nat) (e : list nat) (A : fm) : bool :=
  match A with
  | fand A B => evw n e A && evw n e B
  | fdis A B => evw n e A || evw n e B
  | fimp A B => implb (evb e A) (evw n e B)
  | fall t A => forallb (fun k => evw n (k :: e) A) (seq 0 (ev e t))
  | fex t A => existsb (fun k => evw n (k :: e) A) (seq 0 (ev e t))
  | falle t A => forallb (fun k => evw n (k :: e) A) (seq 0 (S (ev e t)))
  | fexe t A => existsb (fun k => evw n (k :: e) A) (seq 0 (S (ev e t)))
  | fsome A => existsb (fun k => evw n (k :: e) A) (seq 0 n)
  | _ => evb e A
  end.

Lemma evw_ok n A : pos A -> forall e, evw n e A = true -> sat e A.
Proof.
  induction A; intros Hp e H; cbn [pos evw] in Hp, H.
  - apply (evb_ok (feq t u) I e). exact H.
  - apply (evb_ok (flt t u) I e). exact H.
  - apply (evb_ok (fle t u) I e). exact H.
  - apply (evb_ok (fnot A) Hp e). exact H.
  - cbn [sat]. destruct Hp as [H1 H2]. apply andb_true_iff in H as [Ha Hb]. split; [apply IHA1|apply IHA2]; assumption.
  - cbn [sat]. destruct Hp as [H1 H2]. apply orb_true_iff in H as [Ha|Hb]; [left; apply IHA1|right; apply IHA2]; assumption.
  - cbn [sat]. destruct Hp as [H1 H2]. intros Sa. apply (IHA2 H2). apply (evb_ok _ H1 e) in Sa. rewrite Sa in H. exact H.
  - apply (evb_ok (fiff A1 A2) Hp e). exact H.
  - cbn [sat]. rewrite forallb_forall in H. intros k Hk. apply IHA; [exact Hp|]. apply H. apply in_seq. lia.
  - cbn [sat]. apply existsb_exists in H as [k [Hk H]]. apply in_seq in Hk. exists k. split; [lia|]. apply IHA; assumption.
  - cbn [sat]. rewrite forallb_forall in H. intros k Hk. apply IHA; [exact Hp|]. apply H. apply in_seq. lia.
  - cbn [sat]. apply existsb_exists in H as [k [Hk H]]. apply in_seq in Hk. exists k. split; [lia|]. apply IHA; assumption.
  - cbn [sat]. apply existsb_exists in H as [k [Hk H]]. exists k. apply IHA; assumption.
Qed.

Definition sigma1_case (c : string * fm * bool * form) : bool :=
  match c with (_, A, tv, f) => posb A && wfb 0 A && tv && evw 20 [] A && form_eqb (tr A sid) f end.

Lemma sigma1_cases_ok : forallb sigma1_case sigma1_cases = true. Proof. vm_compute. reflexivity. Qed.

Corollary sigma1_sigma1_statements : forall c, In c sigma1_cases -> match c with (_, _, _, f) => prov Gam f end.
Proof.
  intros c Hc. pose proof sigma1_cases_ok as H. rewrite forallb_forall in H. specialize (H c Hc).
  destruct c as [[[n A] tv] f]. unfold sigma1_case in H.
  repeat (apply andb_true_iff in H as [H ?]).
  match goal with H1 : form_eqb _ _ = true |- _ => apply form_eqb_true in H1; subst f end.
  apply sigma1_complete; [apply posb_ok; assumption|apply wfb_ok; assumption|].
  apply (evw_ok 20); [apply posb_ok; assumption|assumption].
Qed.

(* all 78 sentence theorems of sigma1's files 04, 06, 07 *)
Corollary sigma1_all_statements : forall c, In c cases -> match c with (_, _, _, f) => prov Gam f end.
Proof.
  intros c Hc. destruct (boundedb (match c with (_, A, _, _) => A end)) eqn:B.
  - apply sigma1_bounded_statements. unfold bounded_cases. apply filter_In. split; [exact Hc|].
    destruct c as [[[n A] tv] f]. exact B.
  - apply sigma1_sigma1_statements. unfold sigma1_cases. apply filter_In. split; [exact Hc|].
    destruct c as [[[n A] tv] f]. cbn in B |- *. rewrite B. reflexivity.
Qed.
