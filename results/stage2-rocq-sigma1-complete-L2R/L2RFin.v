(* L2RFin.v - lane L2R, 2026-10-09. Addition and multiplication as sigma1.rkt writes them (fin-parts):
   Add(x,y,z) = exists f [Fnc(f) & forall o (Emp(o) -> App(f,o,x)) & forall i (i in y -> exists a App(f,i,a))
                 & forall i j a b (i in y & Suc(j,i) & App(f,i,a) & App(f,j,b) -> Suc(b,a)) & App(f,y,z)],
   Mul(x,y,z) the same with App(f,o,o) and Add(a,x,b) for the step.
   For N_a(x), N_b(y): Add(x,y,z) <-> N_(a+b)(z) and Mul(x,y,z) <-> N_(b*a)(z). One proof for both (kind true = Add,
   false = Mul): the value at every i <= y (FinVal), and the finite function {(0,v0), .., (b,vb)} built by adjoining one
   pair at a time (FinExt). *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith.
From Cohen Require Import Syn Prov Kal Ax Checks Replay Replay2 Expand Pure RpInitOk RpFinal.
From L2R Require Import L2RLogic L2RArith.
Import ListNotations.
Open Scope nat_scope.

Arguments Emp : simpl never.
Arguments Suc : simpl never.
Arguments Opr : simpl never.
Arguments App : simpl never.
Arguments Fnc : simpl never.
Arguments NatP : simpl never.

(* ---- the formulas; f is the variable of the function, the others as seen where the part stands *)
Definition P2a (f x : nat) : form := All (Imp (Emp 0) (App (S f) 0 (S x))).
Definition P2m (f : nat) : form := All (Imp (Emp 0) (App (S f) 0 0)).
Definition P3 (f y : nat) : form := All (Imp (Mem 0 (S y)) (Xf (App (S (S f)) 1 0))).
Definition P4 (f y : nat) (c : form) : form :=
  All (All (All (All (Imp (Kf (Kf (Kf (Mem 3 (4 + y)) (Suc 2 3)) (App (4 + f) 3 1)) (App (4 + f) 2 0)) c)))).
Definition FinBody (p2 : form) (f y z : nat) (c : form) : form :=
  Kf (Kf (Kf (Kf (Fnc f) p2) (P3 f y)) (P4 f y c)) (App f y z).
Definition AddF (x y z : nat) : form := Xf (FinBody (P2a 0 (S x)) 0 (S y) (S z) (Suc 0 1)).
Definition MulF (x y z : nat) : form := Xf (FinBody (P2m 0) 0 (S y) (S z) (AddF 1 (5 + x) 0)).
(* every i with i in y or i = y is in the domain *)
Definition Dom (f y : nat) : form := All (All (Imp (App (S (S f)) 1 0) (Df (Mem 1 (S (S y))) (Eqv 1 (S (S y)))))).

Arguments P2a : simpl never. Arguments P2m : simpl never. Arguments P3 : simpl never. Arguments P4 : simpl never.
Arguments AddF : simpl never. Arguments MulF : simpl never. Arguments Dom : simpl never.

Lemma ren_P2a s f x : ren s (P2a f x) = P2a (s f) (s x). Proof. reflexivity. Qed.
Lemma ren_P2m s f : ren s (P2m f) = P2m (s f). Proof. reflexivity. Qed.
Lemma ren_P3 s f y : ren s (P3 f y) = P3 (s f) (s y). Proof. reflexivity. Qed.
Lemma ren_P4 s f y c : ren s (P4 f y c) = P4 (s f) (s y) (ren (up (up (up (up s)))) c). Proof. reflexivity. Qed.
Lemma ren_AddF s x y z : ren s (AddF x y z) = AddF (s x) (s y) (s z). Proof. reflexivity. Qed.
Lemma ren_MulF s x y z : ren s (MulF x y z) = MulF (s x) (s y) (s z). Proof. reflexivity. Qed.
Lemma ren_Dom s f y : ren s (Dom f y) = Dom (s f) (s y). Proof. reflexivity. Qed.

(* the two kinds *)
Definition P2k (k : bool) (f x : nat) : form := if k then P2a f x else P2m f.
Definition C4k (k : bool) (x : nat) : form := if k then Suc 0 1 else AddF 1 (4 + x) 0.
Definition CCk (k : bool) (x A W : nat) : form := if k then Suc W A else AddF A x W.
Definition Vk (k : bool) (a n : nat) : nat := if k then a + n else n * a.
Definition FinK (k : bool) (x y z : nat) : form := Xf (FinBody (P2k k 0 (S x)) 0 (S y) (S z) (C4k k (S x))).
Lemma FinK_add x y z : FinK true x y z = AddF x y z. Proof. reflexivity. Qed.
Lemma FinK_mul x y z : FinK false x y z = MulF x y z. Proof. reflexivity. Qed.

Lemma ren_P2k s k f x : ren s (P2k k f x) = P2k k (s f) (s x). Proof. destruct k; reflexivity. Qed.
Lemma ren_C4k s k x : ren (up (up (up (up s)))) (C4k k x) = C4k k (s x). Proof. destruct k; reflexivity. Qed.
Lemma ren_CCk s k x A W : ren s (CCk k x A W) = CCk k (s x) (s A) (s W). Proof. destruct k; reflexivity. Qed.
Lemma ren_FinK s k x y z : ren s (FinK k x y z) = FinK k (s x) (s y) (s z). Proof. destruct k; reflexivity. Qed.
Arguments P2k : simpl never. Arguments C4k : simpl never. Arguments CCk : simpl never. Arguments FinK : simpl never.

Lemma sid_red n : sid n = n. Proof. reflexivity. Qed.
Ltac rs3 := repeat progress (rewrite ?ren_Kf, ?ren_Df, ?ren_Qf, ?ren_Xf, ?ren_Top, ?ren_Emp, ?ren_Suc, ?ren_Opr,
  ?ren_App, ?ren_Fnc, ?ren_NatP, ?ren_Num, ?ren_Disj, ?ren_P2a, ?ren_P2m, ?ren_P3, ?ren_P4, ?ren_AddF, ?ren_MulF,
  ?ren_Dom, ?ren_P2k, ?ren_C4k, ?ren_CCk, ?ren_FinK, ?cj_ren, ?sid_red; cbn).
Ltac rs3in H := repeat progress (rewrite ?ren_Kf, ?ren_Df, ?ren_Qf, ?ren_Xf, ?ren_Top, ?ren_Emp, ?ren_Suc, ?ren_Opr,
  ?ren_App, ?ren_Fnc, ?ren_NatP, ?ren_Num, ?ren_Disj, ?ren_P2a, ?ren_P2m, ?ren_P3, ?ren_P4, ?ren_AddF, ?ren_MulF,
  ?ren_Dom, ?ren_P2k, ?ren_C4k, ?ren_CCk, ?ren_FinK, ?cj_ren, ?sid_red in H; cbn in H).

(* ---- contexts given by lists *)
Lemma D_ctx G G' f : (forall g, In g G -> D G' g) -> D G f -> D G' f.
Proof.
  intros H D1. apply (D_mp _ _ _ (D_thm _ _ D1)). clear D1.
  induction G as [|h r IH]; cbn [cj].
  - apply D_thm. exact Top_pv.
  - apply D_and; [apply H; left; reflexivity|]. apply IH. intros g Hg. apply H. right. exact Hg.
Qed.

Lemma D_cjI G L : (forall g, In g L -> D G g) -> D G (cj L).
Proof.
  induction L as [|h r IH]; intros H; cbn [cj]; [apply D_thm; exact Top_pv|].
  apply D_and; [apply H; left; reflexivity|]. apply IH. intros g Hg. apply H. right. exact Hg.
Qed.

Lemma D_cjE G L a : In a L -> D G (cj L) -> D G a.
Proof.
  revert G. induction L as [|h r IH]; intros G I H; [destruct I|]. cbn [cj] in H. destruct I as [<-|I].
  - exact (D_andl _ _ _ H).
  - exact (IH G I (D_andr _ _ _ H)).
Qed.

Lemma D_exE_cj2 G L g : D G (Xf (Xf (cj L))) -> D (L ++ map (ren S) (map (ren S) G)) (ren S (ren S g)) -> D G g.
Proof.
  intros H1 H2. apply (D_exE _ _ _ H1). apply (D_exE _ (cj L)); [hyp|].
  apply (D_ctx (L ++ map (ren S) (map (ren S) G))); [|exact H2]. intros h Hh. apply in_app_or in Hh as [Hh|Hh].
  - apply (D_cjE _ L h Hh). hyp.
  - apply D_hyp. right. cbn [map]. right. exact Hh.
Qed.

Ltac cjE L H := apply (D_cjE _ L); [simpl; tauto|exact H].

(* ---- uses and introductions of the parts *)
Lemma P2a_use G f x o : D G (P2a f x) -> D G (Emp o) -> D G (App f o x).
Proof. intros H1 H2. pose proof (D_inst _ _ o H1) as H. rs3in H. exact (D_mp _ _ _ H H2). Qed.
Lemma P2m_use G f o : D G (P2m f) -> D G (Emp o) -> D G (App f o o).
Proof. intros H1 H2. pose proof (D_inst _ _ o H1) as H. rs3in H. exact (D_mp _ _ _ H H2). Qed.
Lemma P2a_intro G f x : D (Emp 0 :: map (ren S) G) (App (S f) 0 (S x)) -> D G (P2a f x).
Proof. intros H. apply D_all. apply D_intro. exact H. Qed.
Lemma P2m_intro G f : D (Emp 0 :: map (ren S) G) (App (S f) 0 0) -> D G (P2m f).
Proof. intros H. apply D_all. apply D_intro. exact H. Qed.
Lemma P3_use G f y i : D G (P3 f y) -> D G (Mem i y) -> D G (Xf (App (S f) (S i) 0)).
Proof. intros H1 H2. pose proof (D_inst _ _ i H1) as H. rs3in H. exact (D_mp _ _ _ H H2). Qed.
Lemma P3_intro G f y : D (Mem 0 (S y) :: map (ren S) G) (Xf (App (S (S f)) 1 0)) -> D G (P3 f y).
Proof. intros H. apply D_all. apply D_intro. exact H. Qed.
Lemma Dom_use G f y i w : D G (Dom f y) -> D G (App f i w) -> D G (Df (Mem i y) (Eqv i y)).
Proof.
  intros H1 H2. pose proof (D_inst _ _ i H1) as H. rs3in H. pose proof (D_inst _ _ w H) as H'. rs3in H'.
  exact (D_mp _ _ _ H' H2).
Qed.
Lemma Dom_intro G f y : D (App (S (S f)) 1 0 :: map (ren S) (map (ren S) G)) (Df (Mem 1 (S (S y))) (Eqv 1 (S (S y)))) ->
  D G (Dom f y).
Proof. intros H. apply D_all. apply D_all. apply D_intro. exact H. Qed.

Definition inst4 (I J A W : nat) : nat -> nat :=
  fun n => match n with 0 => W | 1 => A | 2 => J | 3 => I | S (S (S (S m))) => m end.

Lemma P4_use G k f y x I J A W : D G (P4 f y (C4k k x)) -> D G (Mem I y) -> D G (Suc J I) -> D G (App f I A) ->
  D G (App f J W) -> D G (CCk k x A W).
Proof.
  intros H H1 H2 H3 H4. apply (D_inst _ _ I) in H. rs3in H. apply (D_inst _ _ J) in H. rs3in H.
  apply (D_inst _ _ A) in H. rs3in H. apply (D_inst _ _ W) in H. rs3in H.
  rewrite !ren_comp in H.
  assert (E : ren (fun n => scons W sid (up (scons A sid) (up (up (scons J sid)) (up (up (up (scons I sid))) n)))) (C4k k x)
              = CCk k x A W) by (destruct k; reflexivity).
  rewrite E in H. apply (D_mp _ _ _ H). apply D_and; [apply D_and; [apply D_and|]|]; assumption.
Qed.

Lemma P4_intro G f y c :
  D (Kf (Kf (Kf (Mem 3 (4 + y)) (Suc 2 3)) (App (4 + f) 3 1)) (App (4 + f) 2 0) ::
     map (ren S) (map (ren S) (map (ren S) (map (ren S) G)))) c -> D G (P4 f y c).
Proof. intros H. apply D_all. apply D_all. apply D_all. apply D_all. apply D_intro. exact H. Qed.

Lemma Fnc_intro G f : D (Kf (App (S (S (S f))) 2 1) (App (S (S (S f))) 2 0) :: map (ren S) (map (ren S) (map (ren S) G)))
  (Eqv 1 0) -> D G (Fnc f).
Proof.
  intros H. apply (D_iffr _ _ _ (D_thm _ _ (U_Fnc f))). apply D_all. apply D_all. apply D_all. apply D_intro. exact H.
Qed.

(* App of f' = r u {p}, p = (Y, Z) *)
Lemma AppU G f' r p i w Y Z :
  D G (All (Qf (Mem 0 (S f')) (Df (Mem 0 (S r)) (Eqv 0 (S p))))) -> D G (Opr p Y Z) ->
  D G (App f' i w) -> D G (Df (App r i w) (Kf (Eqv i Y) (Eqv w Z))).
Proof.
  intros HU HP HA. apply D_App_E in HA. apply (D_exE2 _ _ _ _ HA). rs3.
  pose proof (D_sh2 _ (Mem 0 (S f')) (Opr 0 (S i) (S w)) _ HU) as HU'. rs3in HU'.
  apply (D_inst _ _ 0) in HU'. rs3in HU'.
  pose proof (D_sh2 _ (Mem 0 (S f')) (Opr 0 (S i) (S w)) _ HP) as HP'. rs3in HP'.
  have M (Df (Mem 0 (S r)) (Eqv 0 (S p))). { apply (D_iffl _ _ _ HU'). hyp. }
  apply (D_orE _ _ _ _ M).
  - apply D_orl. apply (D_MemApp _ _ _ _ 0); hyp.
  - apply D_orr. have HO (Opr (S p) (S i) (S w)).
    { apply (D_leib _ (Opr 0 (S (S i)) (S (S w))) 0 (S p)); [hyp|]. rs3. hyp. }
    apply D_and; apply D_sym; [apply (D_Kur1 _ (S p) (S Y) (S Z) (S i) (S w))|apply (D_Kur2 _ (S p) (S Y) (S Z) (S i) (S w))];
      try exact HO; apply D_add; exact HP'.
Qed.

Lemma AppU_old G f' r p i w :
  D G (All (Qf (Mem 0 (S f')) (Df (Mem 0 (S r)) (Eqv 0 (S p))))) -> D G (App r i w) -> D G (App f' i w).
Proof.
  intros HU HA. apply D_App_E in HA. apply (D_exE2 _ _ _ _ HA). rs3.
  pose proof (D_sh2 _ (Mem 0 (S r)) (Opr 0 (S i) (S w)) _ HU) as HU'. rs3in HU'.
  apply (D_inst _ _ 0) in HU'. rs3in HU'.
  apply (D_MemApp _ _ _ _ 0); [|hyp]. apply (D_iffr _ _ _ HU'). apply D_orl. hyp.
Qed.

Lemma AppU_new G f' r p i w Y Z :
  D G (All (Qf (Mem 0 (S f')) (Df (Mem 0 (S r)) (Eqv 0 (S p))))) -> D G (Opr p Y Z) ->
  D G (Eqv Y i) -> D G (Eqv Z w) -> D G (App f' i w).
Proof.
  intros HU HP E1 E2. apply (D_inst _ _ p) in HU. rs3in HU.
  apply (D_MemApp _ _ _ _ p); [apply (D_iffr _ _ _ HU); apply D_orr; apply D_refl|].
  have HO1 (Opr p i Z). { apply (D_leib _ (Opr (S p) 0 (S Z)) Y i E1). rs3. exact HP. }
  apply (D_leib _ (Opr (S p) (S i) 0) Z w E2). rs3. exact HO1.
Qed.

(* ---- small lemmas for the construction *)
Lemma App_emp G r i w c : D G (Emp r) -> D G (App r i w) -> D G c.
Proof.
  intros He HA. apply D_App_E in HA. apply (D_exE2 _ _ _ _ HA).
  pose proof (D_sh2 _ (Mem 0 (S r)) (Opr 0 (S i) (S w)) _ He) as He'. rs3in He'.
  apply (D_absurd _ (Mem 0 (S r))); [hyp|]. exact (D_Emp_nomem _ _ _ He').
Qed.

Lemma AppU_single G f' r p i w Y Z :
  D G (All (Qf (Mem 0 (S f')) (Df (Mem 0 (S r)) (Eqv 0 (S p))))) -> D G (Opr p Y Z) -> D G (Emp r) ->
  D G (App f' i w) -> D G (Kf (Eqv i Y) (Eqv w Z)).
Proof.
  intros HU HP He HA. pose proof (AppU _ _ _ _ _ _ _ _ HU HP HA) as H. apply (D_orE _ _ _ _ H); [|hyp].
  apply (App_emp _ r i w); [apply D_add; exact He|hyp].
Qed.

Lemma CC_eq k G x A W A' W' : D G (Eqv A A') -> D G (Eqv W W') -> D G (CCk k x A W) -> D G (CCk k x A' W').
Proof.
  intros E1 E2 H.
  pose proof (D_leib _ (CCk k (S x) 0 (S W)) A A' E1) as L1. rs3in L1.
  pose proof (D_leib _ (CCk k (S x) (S A') 0) W W' E2) as L2. rs3in L2.
  exact (L2 (L1 H)).
Qed.

Lemma C4k_CC k x : C4k k x = CCk k (4 + x) 1 0. Proof. destruct k; reflexivity. Qed.

Definition w0 (k : bool) (x y : nat) : nat := if k then x else y.
Lemma w0_S k x y : S (w0 k x y) = w0 k (S x) (S y). Proof. destruct k; reflexivity. Qed.

Lemma Base_V k a G x y : D G (Num a x) -> D G (Emp y) -> D G (Num (Vk k a 0) (w0 k x y)).
Proof.
  intros Hx Hy. destruct k; cbn [Vk w0].
  - rewrite Nat.add_0_r. exact Hx.
  - rewrite Num_0. exact Hy.
Qed.

Lemma Base_P2 k G f' r p x y : D G (All (Qf (Mem 0 (S f')) (Df (Mem 0 (S r)) (Eqv 0 (S p))))) ->
  D G (Opr p y (w0 k x y)) -> D G (Emp y) -> D G (P2k k f' x).
Proof.
  intros HU HP He. destruct k; cbn [w0] in HP; unfold P2k.
  - apply P2a_intro. pose proof (D_sh1 _ (Emp 0) _ HU) as HU'. rs3in HU'.
    pose proof (D_sh1 _ (Emp 0) _ HP) as HP'. rs3in HP'. pose proof (D_sh1 _ (Emp 0) _ He) as He'. rs3in He'.
    have E (Eqv (S y) 0). { apply D_sym. apply D_EmpUq; [hyp|exact He']. }
    have A1 (App (S f') (S y) (S x)). { apply (AppU_new _ _ _ _ _ _ _ _ HU' HP'); apply D_refl. }
    pose proof (D_leib _ (App (S (S f')) 0 (S (S x))) _ _ E) as L. rs3in L. exact (L A1).
  - apply P2m_intro. pose proof (D_sh1 _ (Emp 0) _ HU) as HU'. rs3in HU'.
    pose proof (D_sh1 _ (Emp 0) _ HP) as HP'. rs3in HP'. pose proof (D_sh1 _ (Emp 0) _ He) as He'. rs3in He'.
    have E (Eqv (S y) 0). { apply D_sym. apply D_EmpUq; [hyp|exact He']. }
    have A1 (App (S f') (S y) (S y)). { apply (AppU_new _ _ _ _ _ _ _ _ HU' HP'); apply D_refl. }
    pose proof (D_leib _ (App (S (S f')) 0 0) _ _ E) as L. rs3in L. exact (L A1).
Qed.

Lemma Step_P2 k G f' r p x : D G (All (Qf (Mem 0 (S f')) (Df (Mem 0 (S r)) (Eqv 0 (S p))))) ->
  D G (P2k k r x) -> D G (P2k k f' x).
Proof.
  intros HU H2. destruct k; unfold P2k in *.
  - apply P2a_intro. pose proof (D_sh1 _ (Emp 0) _ HU) as HU'. rs3in HU'.
    pose proof (D_sh1 _ (Emp 0) _ H2) as H2'. rs3in H2'.
    apply (AppU_old _ _ _ _ _ _ HU'). apply (P2a_use _ _ _ _ H2'). hyp.
  - apply P2m_intro. pose proof (D_sh1 _ (Emp 0) _ HU) as HU'. rs3in HU'.
    pose proof (D_sh1 _ (Emp 0) _ H2) as H2'. rs3in H2'.
    apply (AppU_old _ _ _ _ _ _ HU'). apply (P2m_use _ _ _ H2'). hyp.
Qed.

Lemma FinVal0 k a G f x i w : D G (Num a x) -> D G (Fnc f) -> D G (P2k k f x) -> D G (Emp i) -> D G (App f i w) ->
  D G (Num (Vk k a 0) w).
Proof.
  intros Hx Hf H2 Hi Hw. destruct k; unfold P2k in H2; cbn [Vk].
  - pose proof (P2a_use _ _ _ _ H2 Hi) as A1. pose proof (D_FncApp _ _ _ _ _ Hf Hw A1) as E.
    rewrite Nat.add_0_r. exact (D_Num_eq _ _ _ _ (D_sym _ _ _ E) Hx).
  - pose proof (P2m_use _ _ _ H2 Hi) as A1. pose proof (D_FncApp _ _ _ _ _ Hf Hw A1) as E.
    rewrite Num_0. pose proof (D_Num_eq _ 0 _ _ (D_sym _ _ _ E)) as H. rewrite !Num_0 in H. exact (H Hi).
Qed.

(* the hypotheses on f, x, y while the value is followed along y *)
Definition HB (k : bool) (a b f x y : nat) : list form := [Num a x; Num b y; Fnc f; P2k k f x; P3 f y; P4 f y (C4k k x)].
Arguments HB : simpl never.
Lemma ren_HB s k a b f x y : map (ren s) (HB k a b f x y) = HB k a b (s f) (s x) (s y).
Proof. unfold HB. rs3. reflexivity. Qed.

Lemma FinVal k a
  (S2 : forall n G x z w, D G (Num a x) -> D G (Num (Vk k a n) z) -> D G (CCk k x z w) -> D G (Num (Vk k a (S n)) w)) :
  forall n G b f x y i w, n <= b -> D G (cj (HB k a b f x y)) -> D G (Num n i) -> D G (App f i w) ->
  D G (Num (Vk k a n) w).
Proof.
  induction n as [|n IH]; intros G b f x y i w Hn HB0 Hi Hw.
  - rewrite Num_0 in Hi.
    apply (FinVal0 k a _ f x i w); [cjE (HB k a b f x y) HB0|cjE (HB k a b f x y) HB0|cjE (HB k a b f x y) HB0|exact Hi|exact Hw].
  - rewrite Num_S in Hi. apply (D_exE2 _ _ _ _ Hi). rs3.
    pose proof (D_sh2 _ (Num n 0) (Suc (S i) 0) _ HB0) as HB1. rewrite cj_ren, ren_HB in HB1.
    have Nb (Num b (S y)). { cjE (HB k a b (S f) (S x) (S y)) HB1. }
    have P3' (P3 (S f) (S y)). { cjE (HB k a b (S f) (S x) (S y)) HB1. }
    have Hm (Mem 0 (S y)). { apply (NumIn n b _ 0 (S y)); [lia|hyp|exact Nb]. }
    pose proof (P3_use _ _ _ _ P3' Hm) as Hex.
    apply (D_exE _ _ _ Hex). rs3.
    pose proof (D_sh1 _ (App (S (S f)) 1 0) _ HB1) as HB2. rewrite cj_ren, ren_HB in HB2. rs3in HB2.
    have IHv (Num (Vk k a n) 0). { apply (IH _ b (S (S f)) (S (S x)) (S (S y)) 1 0); [lia|exact HB2|hyp|hyp]. }
    have P4' (P4 (S (S f)) (S (S y)) (C4k k (S (S x)))). { cjE (HB k a b (S (S f)) (S (S x)) (S (S y))) HB2. }
    have Na (Num a (S (S x))). { cjE (HB k a b (S (S f)) (S (S x)) (S (S y))) HB2. }
    pose proof (D_sh1 _ (App (S (S f)) 1 0) _ Hm) as Hm2. rs3in Hm2.
    pose proof (D_sh2 _ (Num n 0) (Suc (S i) 0) _ Hw) as Hw1. rs3in Hw1.
    pose proof (D_sh1 _ (App (S (S f)) 1 0) _ Hw1) as Hw2. rs3in Hw2.
    have Hc (CCk k (S (S x)) 0 (S (S w))).
    { apply (P4_use _ _ _ _ _ 1 (S (S i)) 0 (S (S w)) P4'); [exact Hm2|hyp|hyp|exact Hw2]. }
    exact (S2 n _ _ _ _ Na IHv Hc).
Qed.

(* ---- the finite function exists: f with z = f(y), and nothing else in its domain *)
Definition EL (k : bool) (a b x y : nat) : list form :=
  [Num (Vk k a b) 0; Fnc 1; P2k k 1 (S (S x)); P3 1 (S (S y)); P4 1 (S (S y)) (C4k k (S (S x))); App 1 (S (S y)) 0;
   Dom 1 (S (S y))].
Definition EL' (k : bool) (a b x y F Z : nat) : list form :=
  [Num (Vk k a b) Z; Fnc F; P2k k F x; P3 F y; P4 F y (C4k k x); App F y Z; Dom F y].
Arguments EL : simpl never.

Lemma ren_XXEL s k a b x y : ren s (Xf (Xf (cj (EL k a b x y)))) = Xf (Xf (cj (EL k a b (s x) (s y)))).
Proof. rewrite !ren_Xf, cj_ren. unfold EL. rs3. reflexivity. Qed.

Lemma pack k a G b x y F Z : (forall g, In g (EL' k a b x y F Z) -> D G g) -> D G (Xf (Xf (cj (EL k a b x y)))).
Proof.
  intros H. apply (D_exI _ _ F). rewrite ren_Xf, cj_ren. apply (D_exI _ _ Z). rewrite cj_ren. unfold EL. rs3.
  change (D G (cj (EL' k a b x y F Z))).
  apply D_cjI. exact H.
Qed.

Lemma oldY G F Yp Y b i w c : D G (Dom F Yp) -> D G (Num b Yp) -> D G (Num (S b) Y) -> D G (App F i w) ->
  D G (Eqv i Y) -> D G c.
Proof.
  intros Hd Hb HY Ha E. pose proof (Dom_use _ _ _ _ _ Hd Ha) as H. apply (D_orE _ _ _ _ H).
  - apply (D_absurd _ (Mem Y Yp)).
    + pose proof (D_leib _ (Mem 0 (S Yp)) i Y (D_add _ (Mem i Yp) _ E)) as L. rs3in L. apply L. hyp.
    + apply (NumNotIn (S b) b); [lia|apply D_add; exact HY|apply D_add; exact Hb].
  - apply (D_absurd _ (Eqv Y Yp)).
    + apply (D_trans _ _ i); [apply D_sym; apply D_add; exact E|hyp].
    + apply (NumNe (S b) b); [lia|apply D_add; exact HY|apply D_add; exact Hb].
Qed.

Lemma D_andl2 G a b c : D G (Kf (Kf a b) c) -> D G a.
Proof. intros H. exact (D_andl _ _ _ (D_andl _ _ _ H)). Qed.

Lemma FinExt0 k a G x y : D G (Num a x) -> D G (Num 0 y) -> D G (Xf (Xf (cj (EL k a 0 x y)))).
Proof.
  intros Hx Hy. rewrite Num_0 in Hy. apply (D_cut2 _ _ _ _ Hx Hy).
  apply (D_exE _ (Opr 0 (S y) (S (w0 k x y)))); [apply D_thm; apply F_OprEx|]. rewrite ren_XXEL. rs3. rewrite ?w0_S.
  apply (D_exE _ (All (Qf (Mem 0 1) (Df (Mem 0 (S (S (S y)))) (Eqv 0 2))))); [apply D_thm; apply (F_AddEx (S y) 0)|].
  rewrite ren_XXEL. rs3. rewrite ?w0_S.
  apply (pack _ _ _ _ _ _ 0 (w0 k (S (S x)) (S (S y)))). intros g Hg. cbn in Hg.
  repeat destruct Hg as [<-|Hg]; [| | | | | | |destruct Hg].
  - apply Base_V; hyp.
  - apply Fnc_intro. rs3. rewrite ?w0_S.
    have A1 (Kf (Eqv 2 (5 + y)) (Eqv 1 (w0 k (5 + x) (5 + y)))).
    { apply (AppU_single _ 3 (5 + y) 4); [hyp|hyp|hyp|]. apply (D_andl _ _ (App 3 2 0)). hyp. }
    have A2 (Kf (Eqv 2 (5 + y)) (Eqv 0 (w0 k (5 + x) (5 + y)))).
    { apply (AppU_single _ 3 (5 + y) 4); [hyp|hyp|hyp|]. apply (D_andr _ (App 3 2 1)). hyp. }
    apply (D_trans _ _ (w0 k (5 + x) (5 + y))); [exact (D_andr _ _ _ A1)|apply D_sym; exact (D_andr _ _ _ A2)].
  - apply (Base_P2 k _ 0 (S (S y)) 1 (S (S x)) (S (S y))); hyp.
  - apply P3_intro. rs3. apply (D_absurd _ (Mem 0 (S (S (S y))))); [hyp|]. apply D_Emp_nomem. hyp.
  - apply P4_intro. rs3. apply (D_absurd _ (Mem 3 (6 + y))).
    + apply (D_andl2 _ _ (Suc 2 3) (App 4 3 1)). apply (D_andl _ _ (App 4 2 0)). hyp.
    + apply D_Emp_nomem. hyp.
  - apply (AppU_new _ _ (S (S y)) 1 _ _ (S (S y)) (w0 k (S (S x)) (S (S y)))); [hyp|hyp|apply D_refl|apply D_refl].
  - apply Dom_intro. rs3. rewrite ?w0_S. apply D_orr.
    have A1 (Kf (Eqv 1 (4 + y)) (Eqv 0 (w0 k (4 + x) (4 + y)))).
    { apply (AppU_single _ 2 (4 + y) 3); hyp. }
    exact (D_andl _ _ _ A1).
Qed.

Ltac addh f := apply (D_cut _ f).
Ltac lb a x y := match goal with |- D ?G _ => let L := fresh "L" in pose proof (D_leib G a x y) as L; rs3in L; apply L; clear L end.

Lemma FinExt k a
  (S1 : forall n G x z, D G (Num a x) -> D G (Num (Vk k a n) z) ->
        D G (Xf (Kf (Num (Vk k a (S n)) 0) (CCk k (S x) (S z) 0)))) :
  forall b G x y, D G (Num a x) -> D G (Num b y) -> D G (Xf (Xf (cj (EL k a b x y)))).
Proof.
  induction b as [|b IH]; intros G x y Hx Hy; [exact (FinExt0 k a G x y Hx Hy)|].
  rewrite Num_S in Hy. apply (D_cut _ _ _ Hx).
  apply (D_exE2 _ _ _ _ (D_add _ (Num a x) _ Hy)). rewrite ren_XXEL. rs3.
  apply (D_exE_cj2 _ (EL k a b (S x) 0)); [apply IH; hyp|].
  rewrite !ren_XXEL. unfold EL at 1. rs3.
  apply (D_exE2 _ (Num (Vk k a (S b)) 0) (CCk k (S (S (S (S x)))) 1 0)); [apply S1; hyp|]. rewrite ren_XXEL. rs3.
  apply (D_exE _ (Opr 0 (5 + y) 1)); [apply D_thm; apply (F_OprEx (4 + y) 0)|]. rewrite ren_XXEL. rs3.
  apply (D_exE _ (All (Qf (Mem 0 1) (Df (Mem 0 5) (Eqv 0 2))))); [apply D_thm; apply (F_AddEx 3 0)|].
  rewrite ren_XXEL. rs3.
  addh (Num (S b) (6 + y)). { rewrite Num_S. apply (D_exI _ _ 5). rs3. apply D_and; hyp. }
  apply (pack _ _ _ _ _ _ 0 2). intros g Hg. cbn in Hg.
  repeat destruct Hg as [<-|Hg]; [| | | | | | |destruct Hg].
  - hyp.
  - (* Fnc *)
    apply Fnc_intro. rs3.
    addh (Df (App 7 2 1) (Kf (Eqv 2 (9 + y)) (Eqv 1 5))).
    { apply (AppU _ 3 7 4 _ _ (9 + y) 5); [hyp|hyp|]. apply (D_andl _ _ (App 3 2 0)). hyp. }
    addh (Df (App 7 2 0) (Kf (Eqv 2 (9 + y)) (Eqv 0 5))).
    { apply (AppU _ 3 7 4 _ _ (9 + y) 5); [hyp|hyp|]. apply (D_andr _ (App 3 2 1)). hyp. }
    apply (D_orE _ (App 7 2 1) (Kf (Eqv 2 (9 + y)) (Eqv 1 5))); [hyp| |].
    + apply (D_orE _ (App 7 2 0) (Kf (Eqv 2 (9 + y)) (Eqv 0 5))); [hyp| |].
      * apply (D_FncApp _ 7 2); hyp.
      * apply (oldY _ 7 8 (9 + y) b 2 1); [hyp|hyp|hyp|hyp|]. apply (D_andl _ _ (Eqv 0 5)). hyp.
    + apply (D_orE _ (App 7 2 0) (Kf (Eqv 2 (9 + y)) (Eqv 0 5))); [hyp| |].
      * apply (oldY _ 7 8 (9 + y) b 2 0); [hyp|hyp|hyp|hyp|]. apply (D_andl _ _ (Eqv 1 5)). hyp.
      * apply (D_trans _ _ 5); [apply (D_andr _ (Eqv 2 (9 + y))); hyp|apply D_sym; apply (D_andr _ (Eqv 2 (9 + y))); hyp].
  - (* P2 *)
    apply (Step_P2 k _ 0 4 1 (6 + x)); hyp.
  - (* P3 *)
    apply P3_intro. rs3.
    addh (Df (Mem 0 6) (Eqv 0 6)). { apply (D_iffl _ (Mem 0 (7 + y))); [apply D_Suc_mem; hyp|hyp]. }
    apply (D_orE _ (Mem 0 6) (Eqv 0 6)); [hyp| |].
    + apply (D_exE _ (App 6 1 0)); [apply (P3_use _ 5 6 0); hyp|]. rs3.
      apply (D_exI _ _ 0). rs3. apply (AppU_old _ 2 6 3); hyp.
    + addh (App 1 6 4). { apply (AppU_old _ 1 5 2); hyp. }
      apply (D_exI _ _ 4). rs3.
      apply (D_leib _ (App 2 0 5) 6 0); [apply D_sym; hyp|rs3; hyp].
  - (* P4 *)
    apply P4_intro. rs3. rewrite C4k_CC. cbn.
    addh (Mem 3 (10 + y)).
    { apply (D_andl _ _ (Suc 2 3)). apply (D_andl _ _ (App 4 3 1)). apply (D_andl _ _ (App 4 2 0)). hyp. }
    addh (Suc 2 3). { apply (D_andr _ (Mem 3 (10 + y))). apply (D_andl _ _ (App 4 3 1)). apply (D_andl _ _ (App 4 2 0)). hyp. }
    addh (App 4 3 1). { apply (D_andr _ (Kf (Mem 3 (10 + y)) (Suc 2 3))). apply (D_andl _ _ (App 4 2 0)). hyp. }
    addh (App 4 2 0). { apply (D_andr _ (Kf (Kf (Mem 3 (10 + y)) (Suc 2 3)) (App 4 3 1))). hyp. }
    addh (App 8 3 1).
    { apply (D_orE _ (App 8 3 1) (Kf (Eqv 3 (10 + y)) (Eqv 1 6))); [apply (AppU _ 4 8 5 _ _ (10 + y) 6); hyp|hyp|].
      apply (D_NoSelf _ (10 + y)). apply (D_leib _ (Mem 0 (11 + y)) 3 (10 + y)); [apply (D_andl _ _ (Eqv 1 6)); hyp|rs3; hyp]. }
    addh (Df (Mem 3 9) (Eqv 3 9)). { apply (D_iffl _ (Mem 3 (10 + y))); [apply D_Suc_mem; hyp|hyp]. }
    addh (Df (App 8 2 0) (Kf (Eqv 2 (10 + y)) (Eqv 0 6))). { apply (AppU _ 4 8 5 _ _ (10 + y) 6); hyp. }
    apply (D_orE _ (Mem 3 9) (Eqv 3 9)); [hyp| |].
    + apply (D_orE _ (App 8 2 0) (Kf (Eqv 2 (10 + y)) (Eqv 0 6))); [hyp| |].
      * apply (P4_use _ k 8 9 (10 + x) 3 2 1 0); hyp.
      * addh (Suc (10 + y) 3).
        { apply (D_leib _ (Suc 0 4) 2 (10 + y)); [apply (D_andl _ _ (Eqv 0 6)); hyp|rs3; hyp]. }
        addh (Eqv 3 9). { apply (D_SucInj _ (10 + y)); hyp. }
        apply (D_NoSelf _ 9). apply (D_leib _ (Mem 0 10) 3 9); [hyp|rs3; hyp].
    + addh (App 8 9 1). { apply (D_leib _ (App 9 0 2) 3 9); [hyp|rs3; hyp]. }
      addh (Eqv 1 7). { apply (D_FncApp _ 8 9); hyp. }
      apply (D_orE _ (App 8 2 0) (Kf (Eqv 2 (10 + y)) (Eqv 0 6))); [hyp| |].
      * addh (Suc 2 9). { apply (D_leib _ (Suc 3 0) 3 9); [hyp|rs3; hyp]. }
        addh (Eqv 2 (10 + y)). { apply (D_SucUq _ 2 (10 + y) 9); hyp. }
        apply (oldY _ 8 9 (10 + y) b 2 0); hyp.
      * apply (CC_eq k _ (10 + x) 7 6 1 0); [apply D_sym; hyp|apply D_sym; apply (D_andr _ (Eqv 2 (10 + y))); hyp|hyp].
  - (* the value at y' *)
    apply (AppU_new _ 0 4 1 _ _ (6 + y) 2); [hyp|hyp|apply D_refl|apply D_refl].
  - (* the domain *)
    apply Dom_intro. rs3.
    addh (Df (App 6 1 0) (Kf (Eqv 1 (8 + y)) (Eqv 0 4))). { apply (AppU _ 2 6 3); hyp. }
    apply (D_orE _ (App 6 1 0) (Kf (Eqv 1 (8 + y)) (Eqv 0 4))); [hyp| |].
    + apply D_orl. apply (D_iffr _ (Mem 1 (8 + y)) (Df (Mem 1 7) (Eqv 1 7))); [apply D_Suc_mem; hyp|].
      apply (Dom_use _ 6 7 1 0); hyp.
    + apply D_orr. apply (D_andl _ _ (Eqv 0 4)). hyp.
Qed.

(* ---- the characterizations *)
Arguments FinBody : simpl never.
Lemma ren_FinBody s p2 f y z c : ren s (FinBody p2 f y z c) = FinBody (ren s p2) (s f) (s y) (s z) (ren (up (up (up (up s)))) c).
Proof. reflexivity. Qed.

Lemma FinBody_parts G p2 f y z c : D G (FinBody p2 f y z c) ->
  D G (Fnc f) /\ D G p2 /\ D G (P3 f y) /\ D G (P4 f y c) /\ D G (App f y z).
Proof.
  intros H. unfold FinBody in H.
  pose proof (D_andl _ _ _ H) as H1. pose proof (D_andl _ _ _ H1) as H2. pose proof (D_andl _ _ _ H2) as H3.
  repeat split; [exact (D_andl _ _ _ H3)|exact (D_andr _ _ _ H3)|exact (D_andr _ _ _ H2)|exact (D_andr _ _ _ H1)|
    exact (D_andr _ _ _ H)].
Qed.

Lemma FinBody_intro G p2 f y z c : D G (Fnc f) -> D G p2 -> D G (P3 f y) -> D G (P4 f y c) -> D G (App f y z) ->
  D G (FinBody p2 f y z c).
Proof. intros H1 H2 H3 H4 H5. unfold FinBody. repeat apply D_and; assumption. Qed.

Lemma FinVal_top k a
  (S2 : forall n G x z w, D G (Num a x) -> D G (Num (Vk k a n) z) -> D G (CCk k x z w) -> D G (Num (Vk k a (S n)) w))
  b G x y z : D G (Num a x) -> D G (Num b y) -> D G (FinK k x y z) -> D G (Num (Vk k a b) z).
Proof.
  intros Hx Hy H. unfold FinK in H. apply (D_cut2 _ _ _ _ Hx Hy).
  apply (D_exE _ _ _ (D_add _ (Num a x) _ (D_add _ (Num b y) _ H))). rs3.
  pose proof (FinBody_parts (FinBody (P2k k 0 (S x)) 0 (S y) (S z) (C4k k (S x)) :: Num a (S x) :: Num b (S y) ::
    map (ren S) G) _ _ _ _ _ ltac:(hyp)) as [H1 [H2 [H3 [H4 H5]]]].
  apply (FinVal k a S2 b _ b 0 (S x) (S y) (S y) (S z)); [lia| |hyp|exact H5].
  apply D_cjI. intros g Hg. cbn in Hg. repeat destruct Hg as [<-|Hg]; [hyp|hyp|exact H1|exact H2|exact H3|exact H4|destruct Hg].
Qed.

Lemma FinExist k a
  (S1 : forall n G x z, D G (Num a x) -> D G (Num (Vk k a n) z) ->
        D G (Xf (Kf (Num (Vk k a (S n)) 0) (CCk k (S x) (S z) 0))))
  b G x y : D G (Num a x) -> D G (Num b y) -> D G (Xf (Kf (Num (Vk k a b) 0) (FinK k (S x) (S y) 0))).
Proof.
  intros Hx Hy. apply (D_exE_cj2 _ (EL k a b x y)); [apply (FinExt k a S1); assumption|]. unfold EL at 1. rs3.
  apply (D_exI _ _ 0). rs3. apply D_and; [hyp|]. unfold FinK. apply (D_exI _ _ 1). rewrite ren_FinBody. rs3.
  apply FinBody_intro; hyp.
Qed.

Lemma FinChar k a
  (S1 : forall n G x z, D G (Num a x) -> D G (Num (Vk k a n) z) ->
        D G (Xf (Kf (Num (Vk k a (S n)) 0) (CCk k (S x) (S z) 0))))
  (S2 : forall n G x z w, D G (Num a x) -> D G (Num (Vk k a n) z) -> D G (CCk k x z w) -> D G (Num (Vk k a (S n)) w))
  b G x y z : D G (Num a x) -> D G (Num b y) -> D G (Qf (FinK k x y z) (Num (Vk k a b) z)).
Proof.
  intros Hx Hy. apply D_iffi.
  - apply (FinVal_top k a S2 b _ x y z); [apply D_add; exact Hx|apply D_add; exact Hy|hyp].
  - apply (D_exE2 _ _ _ _ (FinExist k a S1 b _ x y (D_add _ _ _ Hx) (D_add _ _ _ Hy))). rs3.
    lb (FinK k (S (S x)) (S (S y)) 0) 0 (S z); [|hyp].
    apply (NumUq (Vk k a b)); hyp.
Qed.

(* addition *)
Lemma S2_add a : forall n G x z w, D G (Num a x) -> D G (Num (Vk true a n) z) -> D G (CCk true x z w) ->
  D G (Num (Vk true a (S n)) w).
Proof.
  intros n G x z w _ Hz Hc. cbn [Vk] in *. unfold CCk in Hc. rewrite Nat.add_succ_r, Num_S.
  apply (D_exI _ _ z). rs3. apply D_and; assumption.
Qed.

Lemma S1_add a : forall n G x z, D G (Num a x) -> D G (Num (Vk true a n) z) ->
  D G (Xf (Kf (Num (Vk true a (S n)) 0) (CCk true (S x) (S z) 0))).
Proof.
  intros n G x z Hx Hz. apply (D_cut2 _ _ _ _ Hx Hz).
  apply (D_exE _ (Suc 0 (S z))); [apply D_thm; apply F_SucEx|]. rs3.
  apply (D_exI _ _ 0). rs3. unfold CCk. apply D_and; [|hyp].
  apply (S2_add a n _ (S x) (S z) 0); [hyp|hyp|unfold CCk; hyp].
Qed.

Theorem AddChar a b G x y z : D G (Num a x) -> D G (Num b y) -> D G (Qf (AddF x y z) (Num (a + b) z)).
Proof. intros Hx Hy. rewrite <- FinK_add. exact (FinChar true a (S1_add a) (S2_add a) b G x y z Hx Hy). Qed.

Lemma AddVal a b G x y z : D G (Num a x) -> D G (Num b y) -> D G (AddF x y z) -> D G (Num (a + b) z).
Proof. intros Hx Hy H. exact (D_iffl _ _ _ (AddChar a b G x y z Hx Hy) H). Qed.

Lemma AddExist a b G x y : D G (Num a x) -> D G (Num b y) -> D G (Xf (Kf (Num (a + b) 0) (AddF (S x) (S y) 0))).
Proof. intros Hx Hy. rewrite <- FinK_add. exact (FinExist true a (S1_add a) b G x y Hx Hy). Qed.

(* multiplication *)
Lemma S2_mul a : forall n G x z w, D G (Num a x) -> D G (Num (Vk false a n) z) -> D G (CCk false x z w) ->
  D G (Num (Vk false a (S n)) w).
Proof.
  intros n G x z w Hx Hz Hc. cbn [Vk] in *. unfold CCk in Hc.
  replace (S n * a) with (n * a + a) by lia. exact (AddVal (n * a) a G z x w Hz Hx Hc).
Qed.

Lemma S1_mul a : forall n G x z, D G (Num a x) -> D G (Num (Vk false a n) z) ->
  D G (Xf (Kf (Num (Vk false a (S n)) 0) (CCk false (S x) (S z) 0))).
Proof.
  intros n G x z Hx Hz. cbn [Vk] in *. unfold CCk.
  replace (S n * a) with (n * a + a) by lia. exact (AddExist (n * a) a G z x Hz Hx).
Qed.

Theorem MulChar a b G x y z : D G (Num a x) -> D G (Num b y) -> D G (Qf (MulF x y z) (Num (b * a) z)).
Proof. intros Hx Hy. rewrite <- FinK_mul. exact (FinChar false a (S1_mul a) (S2_mul a) b G x y z Hx Hy). Qed.

Lemma MulExist a b G x y : D G (Num a x) -> D G (Num b y) -> D G (Xf (Kf (Num (b * a) 0) (MulF (S x) (S y) 0))).
Proof. intros Hx Hy. rewrite <- FinK_mul. exact (FinExist false a (S1_mul a) b G x y Hx Hy). Qed.
