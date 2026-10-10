(* Explicit element body for Main's PolynomialSequenceBindingsV2 hook.
   A representation object is the existing ordered pair ((u,v),h).
   Different representation objects can have the same rational value.
   This new source adds no registered symbol or assumption. *)
From Stdlib Require Import List Arith ZArith NArith PArith.
From Cohen Require Import Syn Prov Ax.
From L2R Require Import L2RLogic.
From L2R.b0033 Require Import Bridge_0033.
From CX1.signedq Require Import SignedQForms1.
Import ListNotations.
Local Open Scope nat_scope.

(* Object arity 2: w,q. Four binders outer-to-inner n,h,u,v.
   At their body n=3,h=2,u=1,v=0; ambient indices shift by 4.
   Opr has argument order result,first,second, using original symbol 8. *)
Definition RationalObjectF (w q : nat) : form :=
  Xf (Xf (Xf (Xf
    (Kf
      (Kf (Opr (4+q) 3 2) (Opr 3 1 0))
      (RatTripleF (4+w) 1 0 2))))).

(* Host z:Z,d:positive; object arity 4: w,g,o,q.
   The same ordered-pair layout is specialized to the original wire value. *)
Definition QWireObjectF (z : Z) (d : positive) (w g o q : nat) : form :=
  Xf (Xf (Xf (Xf
    (Kf
      (Kf (Opr (4+q) 3 2) (Opr 3 1 0))
      (QRepF z d (4+w) (4+g) (4+o) 1 0 2))))).

(* Element body contract: variable 0 is the element object; variable S j
   is ambient variable j. For original ambient frame w0,p1,g2,o3,
   this body sees q0,w1,p2,g3,o4 before its own four binders. *)
Definition RationalElementBody : form := RationalObjectF 1 0.
Definition QWireElementBody (z : Z) (d : positive) : form :=
  QWireObjectF z d 1 3 4 0.

(* Object arity 5: w,g,o,q,r. Value equality of two encoded objects.
   Eight component binders n,h,u,v,N,H,U,V have indices7,6,5,4,3,2,1,0.
   QEQuivF adds its own six arithmetic witness binders. *)
Definition RationalObjectEquivF (w g o q r : nat) : form :=
  Xf (Xf (Xf (Xf (Xf (Xf (Xf (Xf
    (Kf
      (Kf
        (Kf
          (Kf (Opr (8+q) 7 6) (Opr 7 5 4))
          (Opr (8+r) 3 2))
        (Opr 3 1 0))
      (QEQuivF (8+w) (8+g) (8+o) 5 4 6 1 0 2))))))))).

Definition QWireObjectExistenceStatement (z : Z) (d : positive) : form :=
  Imp CtxF (Xf (QWireObjectF z d 1 3 4 0)).
Definition QWireObjectDomainStatement (z : Z) (d : positive) : form :=
  Imp CtxF (All (Imp (QWireObjectF z d 1 3 4 0) (RationalObjectF 1 0))).
Definition QWireObjectEquivalenceStatement
  (z : Z) (d : positive) (Zz : Z) (Dd : positive) : form :=
  Imp CtxF (AllN 2
    (Imp (Kf (QWireObjectF z d 2 4 5 1) (QWireObjectF Zz Dd 2 4 5 0))
         (RationalObjectEquivF 2 4 5 1 0))).

(* RationalObjectEquivF is the selected scalar value relation.
   Eqv q r means equality of the encoded set objects and is a different
   relation: ((1,0),2) and ((2,0),4) represent the same rational value. *)
