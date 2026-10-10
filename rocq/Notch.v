(* Notch.v - TNotchT (kernel: I CohP1 pp Vw439x2 pp pp) as the value statement Coh(pp) -> TOP(V(pi notCH-star)).
   The value of a formula doubles at every quantifier (Q repeats its arguments), so the value of pi notCH* is never built;
   the kernel's Vw/Vz definitions share it. A certificate follows the definitions one level at a time: at each node the
   definition's body, instantiated, is the one-level value construction (valN, valI, valA) over the children's atoms, or
   another definition's atom, or the value of an E/= atom. chk verifies a certificate against a formula; chk_sound: a
   verified certificate gives Gam |- R <-> V g. The certificate for notCH* is read off the definitions (dec) and checked. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Expand Pure.
Import ListNotations.
Open Scope nat_scope.

Lemma ren_Qf s a b : ren s (Qf a b) = Qf (ren s a) (ren s b).
Proof. reflexivity. Qed.

(* ---- the value constructors respect equivalence *)
Ltac cong := first [ assumption | apply iff_refl | apply iff_neg; cong | apply iff_all; cong | apply iff_imp; cong ].

Lemma cong_N X Y : prov Gam (Qf X Y) -> prov Gam (Qf (valN X) (valN Y)).
Proof.
  intros H. pose proof (prov_Gam_ren _ H rN) as R. rewrite ren_Qf in R. unfold valN. cong.
Qed.

Lemma cong_I X1 Y1 X2 Y2 : prov Gam (Qf X1 Y1) -> prov Gam (Qf X2 Y2) -> prov Gam (Qf (valI X1 X2) (valI Y1 Y2)).
Proof.
  intros H1 H2. pose proof (prov_Gam_ren _ H1 rI1) as R1. pose proof (prov_Gam_ren _ H2 rI0) as R2.
  rewrite ren_Qf in R1, R2. unfold valI. cong.
Qed.

Lemma cong_A X Y : prov Gam (Qf X Y) -> prov Gam (Qf (valA X) (valA Y)).
Proof.
  intros H. pose proof (prov_Gam_ren _ H rA) as R. rewrite ren_Qf in R. unfold valA. cong.
Qed.

(* ---- certificates *)
Inductive cert : Type :=
| CAt : cert
| CDef : nat -> list nat -> cert -> cert
| CN : cert -> cert
| CI : cert -> cert -> cert
| CA : cert -> cert.

Fixpoint Rf (c : cert) (g : form) : form :=
  match c with
  | CAt => V g
  | CDef w args _ => Pr w args
  | CN c' => match g with Neg g' => valN (Rf c' g') | _ => Top end
  | CI c1 c2 => match g with Imp g1 g2 => valI (Rf c1 g1) (Rf c2 g2) | _ => Top end
  | CA c' => match g with All g' => valA (Rf c' g') | _ => Top end
  end.

Fixpoint chk (T : list (nat * nat * form)) (c : cert) (g : form) : bool :=
  match c with
  | CAt => match g with Mem _ _ | Eqv _ _ => true | _ => false end
  | CDef w args c' =>
      match tlook T w with
      | Some (k, B) => Nat.eqb (List.length args) k && form_eqb (ren (argr args) B) (Rf c' g) && chk T c' g
      | None => false
      end
  | CN c' => match g with Neg g' => chk T c' g' | _ => false end
  | CI c1 c2 => match g with Imp g1 g2 => chk T c1 g1 && chk T c2 g2 | _ => false end
  | CA c' => match g with All g' => chk T c' g' | _ => false end
  end.

Theorem chk_sound T : Good T -> forall c g, chk T c g = true -> prov Gam (Qf (Rf c g) (V g)).
Proof.
  intros G c. induction c as [|w args c IH|c IH|c1 IH1 c2 IH2|c IH]; intros g H.
  - apply iff_refl.
  - simpl in H. destruct (tlook T w) as [[k B]|] eqn:E; [|discriminate].
    apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Nat.eqb_eq in H1. apply form_eqb_true in H2. subst k.
    pose proof (prov_Gam_ren _ (G w (List.length args) B E) (argr args)) as R. rewrite ren_Qf in R.
    assert (A : ren (argr args) (Pr w (seq 0 (List.length args))) = Pr w args)
      by (simpl; rewrite map_argr_seq; reflexivity).
    rewrite A, H2 in R. exact (iff_trans _ _ _ _ R (IH g H3)).
  - destruct g; try discriminate. simpl in H. exact (cong_N _ _ (IH g H)).
  - destruct g; try discriminate. simpl in H. apply andb_true_iff in H as [H1 H2].
    exact (cong_I _ _ _ _ (IH1 g1 H1) (IH2 g2 H2)).
  - destruct g; try discriminate. simpl in H. exact (cong_A _ _ (IH g H)).
Qed.

Lemma good_sub T : (forall d, In d T -> In d Dall) -> Good T.
Proof.
  intros H p k B E. apply tlook_in in E. exact (defax_prov (p, k, B) (H _ E)).
Qed.

(* ---- the definitions of the value of notCH*: the Vw/Vz definitions Vw439x2 depends on (VE4 VQ4 VN3 VI4 and the
   object definitions excluded: their atoms stay) *)
Definition need1 : list string := [
  "Vw13x4"; "Vw12x3"; "VzEmp3"; "Vw11x4"; "Vw10x4"; "Vw9x4"; "Vw8x3"; "Vw7x3"; "Vw26x4"; "Vw25x5"; "Vw28x5"; 
  "Vw27x5"; "Vw24x5"; "Vw23x5"; "Vw22x4"; "VzSuc4"; "Vw21x5"; "Vw20x5"; "Vw19x5"; "Vw18x4"; "Vw17x4"; "Vw16x4"; 
  "Vw15x3"; "Vw14x3"; "Vw6x3"; "Vw5x3"; "VzInd3"; "Vw43x5"; "Vw183x4"; "VzSub4"; "Vw182x4"; "Vw181x3"; "Vw180x3"; 
  "Vw179x3"; "Vw178x3"; "VzOm3"; "Vw250x5"; "Vw252x5"; "Vw251x5"; "Vw249x5"; "Vw248x5"; "Vw247x4"; "VzSng4"; 
  "Vw246x4"; "Vw258x4"; "Vw257x5"; "Vw256x6"; "Vw260x6"; "Vw259x6"; "Vw255x6"; "Vw254x6"; "Vw253x5"; "VzUpr5"; 
  "Vw245x5"; "Vw244x6"; "Vw262x6"; "Vw261x6"; "Vw243x6"; "Vw242x6"; "Vw241x5"; "VzOpr5"; "Vw240x5"; "Vw239x6"; 
  "Vw238x6"; "Vw237x6"; "Vw236x5"; "Vw235x5"; "VzApp5"; "Vw263x5"; "Vw234x6"; "Vw233x6"; "Vw232x6"; "Vw231x5"; 
  "Vw230x4"; "Vw229x3"; "VzFnc3"; "Vw270x6"; "Vw269x6"; "Vw268x6"; "Vw267x5"; "Vw266x4"; "Vw265x3"; "VzInj3"; 
  "Vw264x3"; "Vw228x3"; "Vw227x3"; "Vw277x4"; "Vw276x4"; "Vw275x5"; "Vw274x4"; "VzTot4"; "Vw281x6"; "Vw280x5"; 
  "Vw279x4"; "VzRng4"; "Vw278x4"; "Vw273x5"; "Vw272x5"; "Vw271x5"; "Vw226x5"; "Vw225x5"; "Vw224x5"; "Vw223x4"; 
  "Vw222x4"; "VzLe4"; "Vw426x5"; "Vw425x4"; "Vw424x4"; "Vw423x4"; "Vw422x4"; "Vw421x5"; "Vw420x5"; "Vw428x4"; 
  "Vw427x4"; "Vw419x5"; "Vw418x5"; "Vw417x5"; "Vw416x5"; "Vw415x5"; "Vw414x4"; "Vw429x4"; "Vw433x4"; "Vw432x3"; 
  "Vw434x3"; "Vw438x3"; "Vw437x2"; "Vw439x2"

].
Definition D1 : list (nat * nat * form) :=
  somes (map pdef (filter (fun d => match d with (n, _, _) => existsb (String.eqb n) need1 end) defs)).
Definition T1 : list (nat * nat * form) := Eval vm_compute in D1.
Lemma T1_eq : T1 = D1. Proof. vm_compute. reflexivity. Qed.
Lemma T1_len : List.length T1 = 127. Proof. vm_compute. reflexivity. Qed.

(* every entry of T1 is one of Gam's definitions: checked on the literal, so the kernel never evaluates D1 *)
Definition dd_eqb (d e : nat * nat * form) : bool :=
  match d, e with (p, k, B), (q, j, C) => Nat.eqb p q && Nat.eqb k j && form_eqb B C end.
Lemma dd_eqb_true d e : dd_eqb d e = true -> d = e.
Proof.
  destruct d as [[p k] B], e as [[q j] C]. simpl. intros H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H1, H2. apply form_eqb_true in H3. subst. reflexivity.
Qed.
Lemma T1_in_x : forallb (fun d => existsb (dd_eqb d) Dall) T1 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma good_T1 : Good T1.
Proof.
  apply good_sub. intros d H. pose proof T1_in_x as C. rewrite forallb_forall in C.
  specialize (C d H). apply existsb_exists in C as [e [He E]]. apply dd_eqb_true in E. subst e. exact He.
Qed.

(* ---- reading the certificate off the definitions (not trusted: chk verifies what it returns) *)
Definition rNi (n : nat) : nat := match n with 0 => 0 | 2 => 1 | S (S (S i)) => 2 + i | _ => 1000000 end.
Definition rI1i (n : nat) : nat := match n with 1 => 0 | 3 => 1 | S (S (S (S i))) => 2 + i | _ => 1000000 end.
Definition rI0i (n : nat) : nat := match n with 0 => 0 | 3 => 1 | S (S (S (S i))) => 2 + i | _ => 1000000 end.
Definition rAi (n : nat) : nat := match n with 0 => 0 | 4 => 1 | 1 => 2 | S (S (S (S (S i)))) => 3 + i | _ => 1000000 end.
Definition unr (s : nat -> nat) (R : form) : form := match R with Pr q l => Pr q (map s l) | _ => R end.

Fixpoint dec (T : list (nat * nat * form)) (fuel : nat) (R : form) : option (cert * form) :=
  match fuel with
  | 0 => None
  | S n =>
    match R with
    | Pr p args =>
      if Nat.eqb p sVE then match args with [_; _; x; y] => Some (CAt, Mem (x - 2) (y - 2)) | _ => None end
      else if Nat.eqb p sVQ then match args with [_; _; x; y] => Some (CAt, Eqv (x - 2) (y - 2)) | _ => None end
      else match tlook T p with
      | None => None
      | Some (k, B) =>
        let X := ren (argr args) B in
        match X with
        | Neg (All (Neg (Neg (Imp X1 _)))) =>
            match dec T n (unr rNi X1) with Some (c, g) => Some (CDef p args (CN c), Neg g) | None => None end
        | Neg (All (Neg (Neg (All (Neg (Neg (Imp (Neg (Imp X1 (Neg X2))) _))))))) =>
            match dec T n (unr rI1i X1), dec T n (unr rI0i X2) with
            | Some (c1, g1), Some (c2, g2) => Some (CDef p args (CI c1 c2), Imp g1 g2)
            | _, _ => None
            end
        | All (Neg (Imp (Imp _ (Neg (Imp _ (Neg (All (Neg (All (Neg (Neg (Imp X1 _)))))))))) _)) =>
            match dec T n (unr rAi X1) with Some (c, g) => Some (CDef p args (CA c), All g) | None => None end
        | Pr _ _ => match dec T n X with Some (c, g) => Some (CDef p args c, g) | None => None end
        | _ => None
        end
      end
    | _ => None
    end
  end.

Definition vw439 : nat := Eval vm_compute in sid_of "Vw439x2".
Definition decN : option (cert * form) := dec T1 100000 (Pr vw439 [0; 1]).
Definition cN : cert := match decN with Some (c, _) => c | None => CAt end.
Definition gN : form := match decN with Some (_, g) => g | None => Top end.

Lemma chk_N : chk T1 cN gN = true. Proof. vm_compute. reflexivity. Qed.
Lemma Rf_N : form_eqb (Rf cN gN) (Pr vw439 [0; 1]) = true. Proof. vm_compute. reflexivity. Qed.
Lemma gN_pi : form_eqb gN (pi notch) = true. Proof. vm_compute. reflexivity. Qed.

Lemma tnotch_parse : pstmt symtab ["pp"%string] tnotcht = Some (Imp (Pr coh [0]) (Pr vw439 [0; 0])).
Proof. vm_compute. reflexivity. Qed.

Definition TNOTCH : Prop := forall f, pstmt symtab ["pp"%string] tnotcht = Some f -> prov Gam f.

Theorem notch_value : TNOTCH -> prov Gam (Imp (Pr coh [0]) (TOPf (V (pi notch)))).
Proof.
  intros TN. pose proof (TN _ tnotch_parse) as H.
  pose proof (chk_sound T1 good_T1 cN gN chk_N) as S.
  rewrite (form_eqb_true _ _ Rf_N), (form_eqb_true _ _ gN_pi) in S.
  pose proof (prov_Gam_ren _ S Nat.pred) as S'. rewrite ren_Qf in S'.
  change (ren Nat.pred (Pr vw439 [0; 1])) with (Pr vw439 [0; 0]) in S'.
  change (ren Nat.pred (V (pi notch))) with (TOPf (V (pi notch))) in S'.
  apply iff_l in S'.
  apply (mp2 _ _ _ _ H S').
  pose proof (ptaut_prov Gam (PI (PI (PV 0) (PV 1)) (PI (PI (PV 1) (PV 2)) (PI (PV 0) (PV 2))))
    (lv [Pr coh [0]; Pr vw439 [0; 0]; TOPf (V (pi notch))]) ltac:(vm_compute; reflexivity)) as T.
  exact T.
Qed.
