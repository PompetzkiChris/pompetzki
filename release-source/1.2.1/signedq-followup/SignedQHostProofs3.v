From Stdlib Require Import String ZArith QArith NArith Lia.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra ssrZ.
From Groebner Require Import QPoly CertExtCheck CertDecode2.
From CX1.signedq Require Import SignedQForms1 SignedQTargets1 SignedQHostProofs1.
Local Close Scope Q_scope.

Lemma q2r_eqv_iff (a b : Q) :
  qeqv a b = true <-> q2r a = q2r b.
Proof.
  rewrite <- q2r_eqv. split; intro H.
  - exact (elimT eqP H).
  - exact (introT eqP H).
Qed.

Theorem q_balance_q2r : Target_QBalanceQ2r.
Proof.
  unfold Target_QBalanceQ2r. intros z d u v h.
  rewrite <- q2r_eqv_iff.
  unfold QBalancedb, DifferenceQ, qeqv. cbn [Qnum Qden].
  rewrite !Z.eqb_eq.
  pose proof (signed_parts z) as H. nia.
Qed.

Theorem q_equivalence_q2r : Target_QEquivalenceQ2r.
Proof.
  unfold Target_QEquivalenceQ2r. intros u v h U V H.
  rewrite <- q2r_eqv_iff.
  unfold QEQuivb, DifferenceQ, qeqv. cbn [Qnum Qden].
  rewrite !Z.eqb_eq. nia.
Qed.

Theorem original_wire_decode : Target_OriginalWireDecode.
Proof.
  unfold Target_OriginalWireDecode. intros a b z d [Ha Hb].
  split; [exact (zdecS_complete Ha)|].
  split; [exact (zdecS_complete Hb)|].
  unfold DecRatG. exists z, (Zpos d).
  split; [exact Ha|exact Hb|reflexivity|reflexivity].
Qed.

Print Assumptions q_balance_q2r.
Print Assumptions q_equivalence_q2r.
Print Assumptions original_wire_decode.
