(* Checks.v - every interface statement and every placeholder hypothesis, as the kernel wrote it (Data.v), parses to the
   formula the Rocq side builds with val / EX / UQ / RG / TOP / SUB from the placeholder formulas. Checked by computation. *)
From Stdlib Require Import List Arith Bool PeanoNat String.
From Cohen Require Import Syn Prov Val Inv Parse Data.
Import ListNotations.
Open Scope string_scope.

Definition sid_of (s : string) : nat := match idx s symtab with Some n => n | None => 0%nat end.
Arguments sid_of : simpl never.

Definition ua := Eval vm_compute in sid_of "Usa0".  Definition ub := Eval vm_compute in sid_of "Usb0".  Definition ud := Eval vm_compute in sid_of "Usd0".
Definition uc := Eval vm_compute in sid_of "Usc1".  Definition ud1 := Eval vm_compute in sid_of "Usd1". Definition uc2 := Eval vm_compute in sid_of "Usc2".
Definition uf := Eval vm_compute in sid_of "Usf2".  Definition ug := Eval vm_compute in sid_of "Usg3".
Definition coh := Eval vm_compute in sid_of "CohP1".

(* the value symbol of each placeholder; any other symbol p goes to 1000 + p, outside the table *)
Definition phpairs : list (nat * nat) := Eval vm_compute in
  [(ua, sid_of "VzUsa2"); (ub, sid_of "VzUsb2"); (ud, sid_of "VzUsd2"); (uc, sid_of "VzUsc3");
   (ud1, sid_of "VzUsd3"); (uc2, sid_of "VzUsc4"); (uf, sid_of "VzUsf4"); (ug, sid_of "VzUsg5")].
Fixpoint nlook (l : list (nat * nat)) (p : nat) : option nat :=
  match l with [] => None | (q, v) :: r => if Nat.eqb p q then Some v else nlook r p end.
Definition vz (p : nat) : nat := match nlook phpairs p with Some v => v | None => 1000 + p end.

(* Separation and Collection as the kernel states them; g: x = 0, z = 1 (Sep); y = 0, x = 1, a = 2 (Coll); parameters after *)
Definition skip1 (n : nat) : nat := match n with 0 => 0 | S m => S (S m) end.
Definition ins2 (n : nat) : nat := match n with 0 => 0 | 1 => 1 | S (S m) => S (S (S m)) end.
Definition SepF (g : form) : form := All (Xf (All (Qf (Mem 0 1) (Kf (Mem 0 2) (ren skip1 g))))).
Definition CollF (g : form) : form :=
  All (Imp (All (Imp (Mem 0 1) (Xf g))) (Xf (All (Imp (Mem 0 2) (Xf (Kf (Mem 0 2) (ren ins2 g))))))).
Definition swap01 (n : nat) : nat := match n with 0 => 1 | 1 => 0 | m => m end.
Definition Bot : form := Neg (All (Eqv 0 0)).

Definition lookup3 {A : Type} (n : string) (l : list (string * list string * string * A)) : option (list string * string) :=
  match find (fun e => match e with (m, _, _, _) => String.eqb m n end) l with
  | Some (_, fr, st, _) => Some (fr, st) | None => None end.
Definition lookup2 (n : string) (l : list (string * list string * string)) : option (list string * string) :=
  match find (fun e => match e with (m, _, _) => String.eqb m n end) l with
  | Some (_, fr, st) => Some (fr, st) | None => None end.
Definition pif (n : string) : option form := match lookup3 n iface with Some (fr, st) => pstmt symtab fr st | None => None end.
Definition phy (n : string) : option form := match lookup2 n hyps with Some (fr, st) => pstmt symtab fr st | None => None end.

Definition PA := Pr ua []. Definition PB := Pr ub []. Definition PD := Pr ud [].
Definition V := val vz.

(* the seven axioms, parsed from the kernel's table (lib/zfc.pmp ZF_INIT) *)
Definition ax_texts : list string := [
  "A x A y I A z Q E z x E z y = x y"; "A x A y X z K E x z E y z"; "A f X a A y A x I K E x y E y f E x a";
  "A x X y A z I A u I E u z E u x E z y";
  "X w K X e K A u N E u e E e w A y I E y w X s K A u Q E u s D E u y = u y E s w";
  "A x I X y E y x X y K E y x N X z K E z x E z y";
  "A f I K A a I E a f X u E u a A a A b I K E a f K E b f N = a b N X u K E u a E u b X c A a I E a f X u K K E u a E u c A v I K E v a E v c = v u"].
Definition axf (i : nat) : form := match pstmt symtab [] (nth i ax_texts "") with Some f => f | None => Bot end.

Definition expected : list (string * form) := [
  ("TplNex", EXf (V (Neg PA))); ("TplNuq", UQf (V (Neg PA))); ("TplNrg", RGf (V (Neg PA)));
  ("TplIex", EXf (V (Imp PA PB))); ("TplIuq", UQf (V (Imp PA PB))); ("TplIrg", RGf (V (Imp PA PB)));
  ("TplAex", EXf (V (All (Pr uc [0])))); ("TplAuq", UQf (V (All (Pr uc [0])))); ("TplArg", RGf (V (All (Pr uc [0]))));
  ("TplEex", EXf (V (Mem 0 1))); ("TplEuq", UQf (V (Mem 0 1))); ("TplErg", RGf (V (Mem 0 1)));
  ("TplQex", EXf (V (Eqv 0 1))); ("TplQuq", UQf (V (Eqv 0 1))); ("TplQrg", RGf (V (Eqv 0 1)));
  ("TplSn", SUBf vz (Neg (Pr uc [2])) 2 0 1); ("TplSi", SUBf vz (Imp (Pr uc [2]) (Pr ud1 [2])) 2 0 1);
  ("TplSa", SUBf vz (All (Pr uc2 [0; 3])) 2 0 1); ("TplSo", SUBf vz PA 2 0 1);
  ("TplSe1", SUBf vz (Mem 3 2) 3 0 1); ("TplSe2", SUBf vz (Mem 2 3) 3 0 1); ("TplSe3", SUBf vz (Mem 2 2) 2 0 1);
  ("TplSq1", SUBf vz (Eqv 3 2) 3 0 1); ("TplSq2", SUBf vz (Eqv 2 3) 3 0 1); ("TplSq3", SUBf vz (Eqv 2 2) 2 0 1);
  ("TplK", TOPf (V (Imp PA (Imp PB PA))));
  ("TplS", TOPf (V (Imp (Imp PA (Imp PB PD)) (Imp (Imp PA PB) (Imp PA PD)))));
  ("TplC", TOPf (V (Imp (Imp (Neg PA) (Neg PB)) (Imp PB PA))));
  ("TplInst", TOPf (V (Imp (All (Pr uc [0])) (Pr uc [0]))));
  ("TplVac", TOPf (V (Imp PA (All PA))));
  ("TplDist", TOPf (V (Imp (All (Imp (Pr uc [0]) (Pr ud1 [0]))) (Imp (All (Pr uc [0])) (All (Pr ud1 [0]))))));
  ("TplRefl", TOPf (V (Eqv 0 0)));
  ("TplLeib", TOPf (V (Imp (Eqv 0 1) (Imp (Pr uc [0]) (Pr uc [1])))));
  ("TplSep", TOPf (V (SepF (Pr uf [0; 1]))));
  ("TplColl", TOPf (V (CollF (Pr ug [1; 0; 2]))));
  ("TplIff", TOPf (V (Qf PA PA)));
  ("TplMp", Imp (Kf (TOPf (V PA)) (TOPf (V (Imp PA PB)))) (TOPf (V PB)));
  ("TplGen", Imp (All (ren swap01 (TOPf (V (Pr uc [0]))))) (TOPf (V (All (Pr uc [0])))));
  ("TplExt", TOPf (V (axf 0))); ("TplPair", TOPf (V (axf 1))); ("TplUnion", TOPf (V (axf 2)));
  ("TplPower", TOPf (V (axf 3))); ("TplInf", TOPf (V (axf 4))); ("TplFound", TOPf (V (axf 5)));
  ("TplChoice", TOPf (V (axf 6)));
  ("TplFN", Imp (Pr coh [0]) (Neg (TOPf (V Bot))))].

Definition expected_hyps : list (string * form) := [
  ("HsexUsa2", EXf (V PA)); ("HsuqUsa2", UQf (V PA)); ("HsrgUsa2", RGf (V PA));
  ("HsexUsb2", EXf (V PB)); ("HsuqUsb2", UQf (V PB)); ("HsrgUsb2", RGf (V PB));
  ("HsexUsd2", EXf (V PD)); ("HsuqUsd2", UQf (V PD)); ("HsrgUsd2", RGf (V PD));
  ("HsexUsc3", EXf (V (Pr uc [0]))); ("HsuqUsc3", UQf (V (Pr uc [0]))); ("HsrgUsc3", RGf (V (Pr uc [0])));
  ("HsexUsd3", EXf (V (Pr ud1 [0]))); ("HsuqUsd3", UQf (V (Pr ud1 [0]))); ("HsrgUsd3", RGf (V (Pr ud1 [0])));
  ("HsexUsc4", EXf (V (Pr uc2 [0; 1])));
  ("HsexUsf4", EXf (V (Pr uf [0; 1]))); ("HsuqUsf4", UQf (V (Pr uf [0; 1]))); ("HsrgUsf4", RGf (V (Pr uf [0; 1])));
  ("HsexUsg5", EXf (V (Pr ug [0; 1; 2]))); ("HsuqUsg5", UQf (V (Pr ug [0; 1; 2]))); ("HsrgUsg5", RGf (V (Pr ug [0; 1; 2])));
  ("Hssub24", SUBf vz (Pr uc [2]) 2 0 1); ("Hssub82", SUBf vz (Pr uc [2]) 2 0 1); ("Hssub26", SUBf vz (Pr ud1 [2]) 2 0 1);
  ("Hssub28", SUBf vz (Pr uc2 [2; 3]) 3 0 1);
  ("Hssub97", SUBf vz (Pr uf [3; 2]) 3 0 1); ("Hssub102", SUBf vz (Pr uf [3; 2]) 3 0 1);
  ("Hssub193", SUBf vz (Pr ug [4; 2; 3]) 4 0 1)].

Definition check_all : bool :=
  forallb (fun e => match e with (n, f) => match pif n with Some g => form_eqb g f | None => false end end) expected
  && forallb (fun e => match e with (n, f) => match phy n with Some g => form_eqb g f | None => false end end) expected_hyps
  && Nat.eqb (List.length expected) (List.length iface) && Nat.eqb (List.length expected_hyps) (List.length hyps).

Definition failing : list string :=
  map fst (filter (fun e => match e with (n, f) => match pif n with Some g => negb (form_eqb g f) | None => true end end) expected)
  ++ map fst (filter (fun e => match e with (n, f) => match phy n with Some g => negb (form_eqb g f) | None => true end end) expected_hyps).

Eval vm_compute in failing.
Eval vm_compute in (List.length expected, List.length iface, List.length expected_hyps, List.length hyps).

Lemma check_all_ok : check_all = true.
Proof. vm_compute. reflexivity. Qed.
