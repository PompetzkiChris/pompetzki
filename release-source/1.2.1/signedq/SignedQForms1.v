(* Scalar formula interface selected for the original signed-Q wire.
   New source only. These definitions add no predicate or axiom to Gam.
   Object arguments are de Bruijn variable indices; z and d are host values.
   This source has not been submitted to Rocq at this source-selection stage. *)
From Stdlib Require Import List Arith ZArith NArith PArith.
From Cohen Require Import Syn Ax.
From L2R Require Import L2RLogic L2RArith.
From L2R.b0033 Require Import Bridge_0033 L2RBin7_0033.
Import ListNotations.
Open Scope nat_scope.

Definition PosPart (z : Z) : N :=
  match z with Zpos p => Npos p | _ => N0 end.
Definition NegPart (z : Z) : N :=
  match z with Zneg p => Npos p | _ => N0 end.

(* Original frame: w=0, p=1, g=2, o=3. CtxF is imported unchanged.
   AdF(w,g,x,y,z) and MuF(w,g,o,x,y,z) are the original Bridge_0033
   bodies; BinN(n,w,g,o,x) is the original binary numeral body. *)
Definition Nat2F (w u v : nat) : form := Kf (Mem u w) (Mem v w).
Definition Nat3F (w u v h : nat) : form := Kf (Nat2F w u v) (Mem h w).
Definition RatTripleF (w u v h : nat) : form :=
  Kf (Nat3F w u v h) (Neg (Emp h)).

(* Arity 6: w,g,a,b,c,d. Binds t; t=0 and ambient indices shift by 1.
   Formula: exists t (a+b=t and c+d=t). *)
Definition SumEqF (w g a b c d : nat) : form :=
  Xf (Kf (AdF (S w) (S g) (S a) (S b) 0)
          (AdF (S w) (S g) (S c) (S d) 0)).

(* Arity 11: w,g,o,a,b,c,d,e,f,h,i.
   Binds t1,t2,t3,t4,L,R in that outer-to-inner order.
   At depth 6: t1=5,t2=4,t3=3,t4=2,L=1,R=0; ambient indices shift by 6.
   Formula: a*b+c*d=e*f+h*i, with actual natural products and sums. *)
Definition CrossF (w g o a b c d e f h i : nat) : form :=
  Xf (Xf (Xf (Xf (Xf (Xf
    (Kf
      (Kf
        (Kf
          (Kf
            (Kf
              (Kf (MuF (6+w) (6+g) (6+o) (6+a) (6+b) 5)
                  (MuF (6+w) (6+g) (6+o) (6+c) (6+d) 4))
              (MuF (6+w) (6+g) (6+o) (6+e) (6+f) 3))
            (MuF (6+w) (6+g) (6+o) (6+h) (6+i) 2))
          (AdF (6+w) (6+g) 5 4 1))
        (AdF (6+w) (6+g) 3 2 0))
      (Eqv 1 0))))))).

(* Host parameter z:Z; object arity 5: w,g,o,u,v.
   Represents u-v=z, allowing every natural decomposition.
   Outer binders np,nn have indices 1,0. SumEqF then binds t;
   inside the sum body np=2,nn=1,t=0 and ambient indices shift by 3. *)
Definition ZRepF (z : Z) (w g o u v : nat) : form :=
  Kf (Nat2F w u v)
    (Xf (Xf
      (Kf
        (Kf (BinN (PosPart z) (2+w) (2+g) (2+o) 1)
            (BinN (NegPart z) (2+w) (2+g) (2+o) 0))
        (SumEqF (2+w) (2+g) (2+u) 0 (2+v) 1)))).

(* Host parameters z:Z,d:positive; object arity 6: w,g,o,u,v,h.
   Represents (u-v)/h=z/d without requiring a reduced fraction.
   np,nn,dd at depth 3 are 2,1,0. CrossF adds six binders, so its
   body has np=8,nn=7,dd=6,t1=5,t2=4,t3=3,t4=2,L=1,R=0.
   Equation: dd*u+nn*h=dd*v+np*h. *)
Definition QRepF (z : Z) (d : positive) (w g o u v h : nat) : form :=
  Kf (RatTripleF w u v h)
    (Xf (Xf (Xf
      (Kf
        (Kf
          (Kf (BinN (PosPart z) (3+w) (3+g) (3+o) 2)
              (BinN (NegPart z) (3+w) (3+g) (3+o) 1))
          (BinN (Npos d) (3+w) (3+g) (3+o) 0))
        (CrossF (3+w) (3+g) (3+o)
          0 (3+u) 1 (3+h) 0 (3+v) 2 (3+h)))))).

(* Object arity 9: w,g,o,u,v,h,U,V,H. The two triples can have
   different denominators and arbitrary natural decompositions.
   Equation: u*H+V*h=v*H+U*h. CrossF contributes six binders. *)
Definition QEQuivF (w g o u v h U V H : nat) : form :=
  Kf (Kf (RatTripleF w u v h) (RatTripleF w U V H))
      (CrossF w g o u H V h v H U h).

(* Canonical representatives; these are input numeral formulas. *)
Definition CanonZF (z : Z) (w g o u v : nat) : form :=
  Kf (BinN (PosPart z) w g o u) (BinN (NegPart z) w g o v).
Definition CanonQF (z : Z) (d : positive) (w g o u v h : nat) : form :=
  Kf (CanonZF z w g o u v) (BinN (Npos d) w g o h).

Definition Numeral2F (u v : N) (w g o x y : nat) : form :=
  Kf (BinN u w g o x) (BinN v w g o y).
Definition Numeral3F (u v : N) (h : positive) (w g o x y t : nat) : form :=
  Kf (Numeral2F u v w g o x y) (BinN (Npos h) w g o t).

Fixpoint AllN (n : nat) (f : form) : form :=
  match n with 0 => f | S k => All (AllN k f) end.
(* AllN does not rename f. Supply f with its final binder indices.
   AllN 4 f closes the frame in outer-to-inner order o,g,p,w,
   leaving the original frame at indices w0,p1,g2,o3 in f. *)
Definition CloseFrame (f : form) : form := AllN 4 f.

Definition ZCanonicalStatement (z : Z) : form :=
  Imp CtxF (AllN 2
    (Imp (CanonZF z 2 4 5 1 0) (ZRepF z 2 4 5 1 0))).
Definition QCanonicalStatement (z : Z) (d : positive) : form :=
  Imp CtxF (AllN 3
    (Imp (CanonQF z d 3 5 6 2 1 0) (QRepF z d 3 5 6 2 1 0))).
Definition ZExistenceStatement (z : Z) : form :=
  Imp CtxF (Xf (Xf (ZRepF z 2 4 5 1 0))).
Definition QExistenceStatement (z : Z) (d : positive) : form :=
  Imp CtxF (Xf (Xf (Xf (QRepF z d 3 5 6 2 1 0)))).

Definition ZBalancedb (z : Z) (u v : N) : bool :=
  Z.eqb (Z.add (Z.of_N u) (Z.of_N (NegPart z)))
        (Z.add (Z.of_N v) (Z.of_N (PosPart z))).
Definition QBalancedb (z : Z) (d : positive) (u v : N) (h : positive) : bool :=
  Z.eqb
    (Z.add (Z.mul (Zpos d) (Z.of_N u))
           (Z.mul (Z.of_N (NegPart z)) (Zpos h)))
    (Z.add (Z.mul (Zpos d) (Z.of_N v))
           (Z.mul (Z.of_N (PosPart z)) (Zpos h))).
Definition QEQuivb (u v : N) (h : positive) (U V : N) (H : positive) : bool :=
  Z.eqb
    (Z.add (Z.mul (Z.of_N u) (Zpos H)) (Z.mul (Z.of_N V) (Zpos h)))
    (Z.add (Z.mul (Z.of_N v) (Zpos H)) (Z.mul (Z.of_N U) (Zpos h))).

Definition ZNumeralStatement (z : Z) (u v : N) : form :=
  Imp CtxF (AllN 2 (Imp (Numeral2F u v 2 4 5 1 0)
    (if ZBalancedb z u v then ZRepF z 2 4 5 1 0
     else Neg (ZRepF z 2 4 5 1 0)))).
Definition QNumeralStatement (z : Z) (d : positive) (u v : N) (h : positive) : form :=
  Imp CtxF (AllN 3 (Imp (Numeral3F u v h 3 5 6 2 1 0)
    (if QBalancedb z d u v h then QRepF z d 3 5 6 2 1 0
     else Neg (QRepF z d 3 5 6 2 1 0)))).
(* Six binders outer-to-inner x,y,t,X,Y,T. At the body:
   x5,y4,t3,X2,Y1,T0; frame w6,p7,g8,o9. *)
Definition QEQuivNumeralStatement
  (u v : N) (h : positive) (U V : N) (H : positive) : form :=
  Imp CtxF (AllN 6
    (Imp (Kf (Numeral3F u v h 6 8 9 5 4 3)
             (Numeral3F U V H 6 8 9 2 1 0))
      (if QEQuivb u v h U V H then QEQuivF 6 8 9 5 4 3 2 1 0
       else Neg (QEQuivF 6 8 9 5 4 3 2 1 0)))).

(* Six freely quantified representation variables. This statement asserts
   rational-value preservation even when the wire pairs are unreduced. *)
Definition QWireEquivalentStatement (z : Z) (d : positive) (Zz : Z) (Dd : positive) : form :=
  Imp CtxF (AllN 6
    (Imp (Kf (QRepF z d 6 8 9 5 4 3) (QRepF Zz Dd 6 8 9 2 1 0))
         (QEQuivF 6 8 9 5 4 3 2 1 0))).

(* Frozen arities and binder positions for source integration. *)
Definition SignedQObjectArities : list (nat * nat) :=
  [(0,6); (1,11); (2,5); (3,6); (4,9); (5,5); (6,6)].
(* The first components above are metadata keys, not Syn.Pr predicate IDs:
   0 SumEqF,1 CrossF,2 ZRepF,3 QRepF,4 QEQuivF,5 CanonZF,6 CanonQF. *)
