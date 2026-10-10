(* L2RAgree.v - lane L2R, 2026-10-09. The translation tr of L2RSent.v against the statements sigma1.rkt wrote and both
   judges accepted (L2RCases.v, written by agree.rkt): for each of the 78 sentence theorems of 04-bounded, 06-sentences,
   07-sigma1, tr of the sentence (its negation for a false one) is the theorem's statement, form for form. The truth
   values agree with a boolean evaluator, proved equal to sat for bounded sentences. Then bounded_complete gives, for the
   73 bounded ones, prov Gam of the statement directly. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Ax.
From L2R Require Import L2RLogic L2RArith L2RFin L2RSent L2RCases.
Import ListNotations.
Open Scope nat_scope.

Fixpoint evb (e : list nat) (A : fm) : bool :=
  match A with
  | feq t u => Nat.eqb (ev e t) (ev e u)
  | flt t u => Nat.ltb (ev e t) (ev e u)
  | fle t u => Nat.leb (ev e t) (ev e u)
  | fnot A => negb (evb e A)
  | fand A B => evb e A && evb e B
  | fdis A B => evb e A || evb e B
  | fimp A B => implb (evb e A) (evb e B)
  | fiff A B => Bool.eqb (evb e A) (evb e B)
  | fall t A => forallb (fun k => evb (k :: e) A) (seq 0 (ev e t))
  | fex t A => existsb (fun k => evb (k :: e) A) (seq 0 (ev e t))
  | falle t A => forallb (fun k => evb (k :: e) A) (seq 0 (S (ev e t)))
  | fexe t A => existsb (fun k => evb (k :: e) A) (seq 0 (S (ev e t)))
  | fsome A => false
  end.

Fixpoint boundedb (A : fm) : bool :=
  match A with
  | feq _ _ | flt _ _ | fle _ _ => true
  | fnot A => boundedb A
  | fand A B | fdis A B | fimp A B | fiff A B => boundedb A && boundedb B
  | fall _ A | fex _ A | falle _ A | fexe _ A => boundedb A
  | fsome _ => false
  end.

Fixpoint wftb (m : nat) (t : tm) : bool :=
  match t with
  | tnum _ => true | tvar i => i <? m | tS t => wftb m t
  | tadd t u | tmul t u => wftb m t && wftb m u
  end.

Fixpoint wfb (m : nat) (A : fm) : bool :=
  match A with
  | feq t u | flt t u | fle t u => wftb m t && wftb m u
  | fnot A => wfb m A
  | fand A B | fdis A B | fimp A B | fiff A B => wfb m A && wfb m B
  | fall t A | fex t A | falle t A | fexe t A => wftb m t && wfb (S m) A
  | fsome A => wfb (S m) A
  end.

Lemma boundedb_ok A : boundedb A = true -> bounded A.
Proof. induction A; cbn; intros H; rewrite ?andb_true_iff in H; try discriminate; tauto. Qed.

Lemma wftb_ok t m : wftb m t = true -> wft m t.
Proof. induction t; cbn; intros H; rewrite ?andb_true_iff in H; try tauto. apply Nat.ltb_lt. exact H. Qed.

Lemma wfb_ok A : forall m, wfb m A = true -> wf m A.
Proof.
  induction A; intros m; cbn; intros H; rewrite ?andb_true_iff in H; try tauto;
    try (destruct H as [H1 H2]; split; [apply wftb_ok; exact H1|apply wftb_ok; exact H2]);
    try (destruct H as [H1 H2]; split; [apply wftb_ok; exact H1|apply IHA; exact H2]);
    try (destruct H as [H1 H2]; split; [apply IHA1; exact H1|apply IHA2; exact H2]).
  - apply IHA. exact H.
  - apply IHA. exact H.
Qed.

Lemma evb_ok A : bounded A -> forall e, evb e A = true <-> sat e A.
Proof.
  induction A; cbn [bounded evb sat]; intros Hb e.
  - apply Nat.eqb_eq.
  - apply Nat.ltb_lt.
  - apply Nat.leb_le.
  - rewrite negb_true_iff, <- IHA by exact Hb. destruct (evb e A); split; congruence.
  - destruct Hb as [H1 H2]. rewrite andb_true_iff, IHA1, IHA2 by assumption. tauto.
  - destruct Hb as [H1 H2]. rewrite orb_true_iff, IHA1, IHA2 by assumption. tauto.
  - destruct Hb as [H1 H2]. rewrite <- IHA1, <- IHA2 by assumption.
    destruct (evb e A1), (evb e A2); cbn; intuition congruence.
  - destruct Hb as [H1 H2]. rewrite <- IHA1, <- IHA2 by assumption.
    destruct (evb e A1), (evb e A2); cbn; intuition congruence.
  - rewrite forallb_forall. split.
    + intros H k Hk. apply IHA; [exact Hb|]. apply H. apply in_seq. lia.
    + intros H k Hk. apply in_seq in Hk. apply IHA; [exact Hb|]. apply H. lia.
  - rewrite existsb_exists. split.
    + intros [k [Hk H]]. apply in_seq in Hk. exists k. split; [lia|]. apply IHA; assumption.
    + intros [k [Hk H]]. exists k. split; [apply in_seq; lia|]. apply IHA; assumption.
  - rewrite forallb_forall. split.
    + intros H k Hk. apply IHA; [exact Hb|]. apply H. apply in_seq. lia.
    + intros H k Hk. apply in_seq in Hk. apply IHA; [exact Hb|]. apply H. lia.
  - rewrite existsb_exists. split.
    + intros [k [Hk H]]. apply in_seq in Hk. exists k. split; [lia|]. apply IHA; assumption.
    + intros [k [Hk H]]. exists k. split; [apply in_seq; lia|]. apply IHA; assumption.
  - destruct Hb.
Qed.

(* ---- the 78 cases *)
Definition stmt_of (A : fm) (tv : bool) : form := if tv then tr A sid else Neg (tr A sid).

(* every case: the statement sigma1 wrote is tr of its sentence (negated when false) *)
Definition agrees (c : string * fm * bool * form) : bool :=
  match c with (_, A, tv, f) => wfb 0 A && form_eqb (stmt_of A tv) f end.

(* the bounded cases: also bounded, and the truth value is the evaluator's *)
Definition proved_case (c : string * fm * bool * form) : bool :=
  match c with (_, A, tv, f) => boundedb A && wfb 0 A && Bool.eqb (evb [] A) tv && form_eqb (stmt_of A tv) f end.

Lemma cases_length : List.length cases = 78. Proof. vm_compute. reflexivity. Qed.
Lemma all_agree : forallb agrees cases = true. Proof. vm_compute. reflexivity. Qed.
Definition bounded_cases : list (string * fm * bool * form) := filter (fun c => match c with (_, A, _, _) => boundedb A end) cases.
Lemma bounded_cases_length : List.length bounded_cases = 73. Proof. vm_compute. reflexivity. Qed.
Lemma bounded_cases_ok : forallb proved_case bounded_cases = true. Proof. vm_compute. reflexivity. Qed.

Lemma proved_case_prov c : proved_case c = true -> match c with (_, _, _, f) => prov Gam f end.
Proof.
  destruct c as [[[n A] tv] f]. unfold proved_case. intros H.
  repeat (apply andb_true_iff in H as [H ?]).
  match goal with H1 : form_eqb _ _ = true |- _ => apply form_eqb_true in H1; subst f end.
  match goal with H1 : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in H1 end.
  pose proof (boundedb_ok A H) as Hb.
  match goal with H1 : wfb 0 A = true |- _ => pose proof (wfb_ok A 0 H1) as Hw end.
  destruct (bounded_complete A Hb Hw) as [P N]. unfold stmt_of. destruct tv.
  - apply P. apply (evb_ok A Hb []). assumption.
  - apply N. intros S0. apply (evb_ok A Hb []) in S0. congruence.
Qed.

(* the statements of the 73 bounded sentence theorems of sigma1's files 04 and 06, derivable in Gam by the theorem *)
Corollary sigma1_bounded_statements : forall c, In c bounded_cases -> match c with (_, _, _, f) => prov Gam f end.
Proof.
  intros c Hc. apply proved_case_prov. pose proof bounded_cases_ok as H. rewrite forallb_forall in H. exact (H c Hc).
Qed.
