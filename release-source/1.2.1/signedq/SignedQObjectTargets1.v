(* Source-selection target types for the explicit scalar-object hook.
   Definitions of propositions only; no target is supplied as an axiom. *)
From Stdlib Require Import List ZArith QArith PArith.
From Cohen Require Import Syn Prov Ax Elim.
From Groebner Require Import QPoly.
From CX1.signedq Require Import SignedQForms1 SignedQTargets1 SignedQObjectForms1.
Import ListNotations.

Definition Target_OriginalWireObjectExists : Prop :=
  forall (z : Z) (d : positive),
    prov Gam (QWireObjectExistenceStatement z d).
Definition Target_OriginalWireObjectDomain : Prop :=
  forall (z : Z) (d : positive),
    prov Gam (QWireObjectDomainStatement z d).
Definition Target_OriginalWireObjectsEquivalent : Prop :=
  forall (z : Z) (d : positive) (Zz : Z) (Dd : positive),
    q2r (Qmake z d) = q2r (Qmake Zz Dd) ->
    prov Gam (QWireObjectEquivalenceStatement z d Zz Dd).
Definition Target_RationalElementBodyClosure : Prop :=
  closedk 5 RationalElementBody = true /\
  forall (z : Z) (d : positive), closedk 5 (QWireElementBody z d) = true.
Definition Target_OriginalWireObjectPureZF : Prop :=
  forall (z : Z) (d : positive),
    prov ZFpure (SignedQExpand (CloseFrame (QWireObjectExistenceStatement z d))) /\
    prov ZFpure (SignedQExpand (CloseFrame (QWireObjectDomainStatement z d))).
