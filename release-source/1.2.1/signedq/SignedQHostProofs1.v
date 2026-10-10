From Stdlib Require Import ZArith NArith Lia.
From CX1.signedq Require Import SignedQForms1 SignedQTargets1.

Theorem signed_parts : Target_SignedParts.
Proof.
  unfold Target_SignedParts. intros z. destruct z; reflexivity.
Qed.

Theorem z_balance : Target_ZBalance.
Proof.
  unfold Target_ZBalance. intros z u v.
  unfold ZBalancedb. rewrite Z.eqb_eq.
  pose proof (signed_parts z) as H. lia.
Qed.

Print Assumptions signed_parts.
Print Assumptions z_balance.
