(* Intended theorem types for the selected original scalar interface.
   Every Target_* below is a definition of a proposition, not a theorem,
   assumption, Parameter, Axiom, or new registered predicate. No target
   is claimed proved or kernel checked by this source-selection packet. *)
From Stdlib Require Import List String ZArith QArith NArith PArith.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra ssrZ.
From Cohen Require Import Syn Prov Ax Expand Elim.
From Groebner Require Import QPoly CertExtCheck CertDecode2.
From CX1.signedq Require Import SignedQForms1.
Import ListNotations.
Local Close Scope Q_scope.

Definition DifferenceQ (u v : N) (h : positive) : Q :=
  Qmake (Z.sub (Z.of_N u) (Z.of_N v)) h.
Definition OriginalWireCoefficient (a b : string) (z : Z) (d : positive) : Prop :=
  DecIntS a z /\ DecIntS b (Zpos d).

(* Host arithmetic and the original QPoly interpretation. These types
   quantify arbitrary values, with no normalization or size bound. *)
Definition Target_SignedParts : Prop :=
  forall z : Z, Z.sub (Z.of_N (PosPart z)) (Z.of_N (NegPart z)) = z.
Definition Target_ZBalance : Prop :=
  forall (z : Z) (u v : N),
    ZBalancedb z u v = true <-> Z.sub (Z.of_N u) (Z.of_N v) = z.
Definition Target_QBalanceQ2r : Prop :=
  forall (z : Z) (d : positive) (u v : N) (h : positive),
    QBalancedb z d u v h = true <->
    q2r (DifferenceQ u v h) = q2r (Qmake z d).
Definition Target_QEquivalenceQ2r : Prop :=
  forall (u v : N) (h : positive) (U V : N) (H : positive),
    QEQuivb u v h U V H = true <->
    q2r (DifferenceQ u v h) = q2r (DifferenceQ U V H).

(* Original strict wire input entails the original decoders and scalar
   relation. No desired output or judge verdict is a public premise. *)
Definition Target_OriginalWireDecode : Prop :=
  forall (a b : string) (z : Z) (d : positive),
    OriginalWireCoefficient a b z d ->
    zdecS a = Some z /\ zdecS b = Some (Zpos d) /\
    @DecRatG DecIntS a b (q2r (Qmake z d)).

(* These are object-language derivability targets over the unchanged Gam
   and literal CtxF. True and false arithmetic cases are both required.
   The operand values are supplied by the original BinN numeral formulas,
   rather than by an assumed interpretation of a new predicate. *)
Definition Target_ZNumeralCharacterization : Prop :=
  forall (z : Z) (u v : N), prov Gam (ZNumeralStatement z u v).
Definition Target_QNumeralCharacterization : Prop :=
  forall (z : Z) (d : positive) (u v : N) (h : positive),
    prov Gam (QNumeralStatement z d u v h).
Definition Target_QEquivNumeralCharacterization : Prop :=
  forall (u v : N) (h : positive) (U V : N) (H : positive),
    prov Gam (QEQuivNumeralStatement u v h U V H).

Definition Target_ZCanonical : Prop :=
  forall z : Z, prov Gam (ZCanonicalStatement z).
Definition Target_QCanonical : Prop :=
  forall (z : Z) (d : positive), prov Gam (QCanonicalStatement z d).
Definition Target_ZExists : Prop :=
  forall z : Z, prov Gam (ZExistenceStatement z).
Definition Target_QExists : Prop :=
  forall (z : Z) (d : positive), prov Gam (QExistenceStatement z d).

(* Universal object representatives, not only canonical numeral triples.
   The scalar-equality premise relates the two original wire coefficients.
   The conclusion is a Gam derivation quantified over every pair of natural
   triples meeting QRepF, including unreduced and noncanonical triples. *)
Definition Target_UnreducedWireEquivalence : Prop :=
  forall (z : Z) (d : positive) (Zz : Z) (Dd : positive),
    q2r (Qmake z d) = q2r (Qmake Zz Dd) ->
    prov Gam (QWireEquivalentStatement z d Zz Dd).

(* Four additional binders close the original frame. Their literal order
   is o,g,p,w. The arithmetic statements retain CtxF as their antecedent. *)
Definition Target_ClosedCanonical : Prop :=
  forall (z : Z) (d : positive),
    closedk 0 (CloseFrame (QCanonicalStatement z d)) = true /\
    prov Gam (CloseFrame (QCanonicalStatement z d)).

(* Preserve defined-symbol meaning by full registered expansion with Pr
   fallback. Pure.pi's first-23 table is not substituted for this table. *)
Definition SignedQFullTable : list (nat * nat * form) := buildT Pr [] Dall.
Definition SignedQExpand (f : form) : form := expD Pr SignedQFullTable f.
Definition SignedQScalarStatements (z : Z) (d : positive) : list form :=
  [ZCanonicalStatement z; QCanonicalStatement z d;
   ZExistenceStatement z; QExistenceStatement z d].
Definition Target_FullExpansionPurity : Prop :=
  forall (z : Z) (d : positive) (f : form),
    In f (SignedQScalarStatements z d) -> syms (SignedQExpand f) = [].
Definition Target_OriginalPureZFScalar : Prop :=
  forall (z : Z) (d : positive) (f : form),
    In f (SignedQScalarStatements z d) ->
    prov ZFpure (SignedQExpand (CloseFrame f)).

(* Existing proof route, read-only source references:
   - L2RBin7_0033.binN_num, L2RBinOps_0033.bin_ad_D/bin_mu_D;
   - L2RArith.NumEx/NumUq/NumNe and original Bridge_0033 arithmetic;
   - CertDecode2.zdecS_complete and dtermG_sound;
   - CertExtCheck.q2r_eqv, QPoly.zr_pos/q2r_*;
   - Expand.buildT_good/repl and CX3.Conservativity2's proved
     all_registered_expansion_pure, after actual expanded purity is proved.
   Main owns integration and polynomial/order/evaluation selection. *)
