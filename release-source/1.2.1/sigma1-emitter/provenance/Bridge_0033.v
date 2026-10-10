(* Bridge_0033.v - lane L2R, 2026-10-10. The bridge between the two definitions of + and * in ZF:
     Ad / Mu   : from the replay's recursion theorem (replay 95), as the L2D/L8 certificate emitters use them;
     AddF/MulF : sigma1.rkt's finite-function formulas, as L2RFin.v states them (bounded_complete, sigma1_complete).
   The file bridge-addmul-t1-0033.jdg (bridge-0033.rkt / bridge2-0033.rkt over L2D's kernel; pmp and Racket judges
   ACCEPT, 79 theorems, 2534 steps) is transcribed by LCH's jdg2v.rkt into BrB_0033.v and replayed here by
   Replay2.check_batch over REGP = the first 677 entries of RpInitOk.REG0, sound by Replay3.check_batch_ok.
   Frame: w = 0, p = 1, g = 2, o = 3 and Ctx = Om(w) & Pr(p,w,w) & CapS(g,p,w) & Emp(o).
     bridge_add : prov Gam (Ctx -> forall x y z (x in w -> y in w -> (Ad(x,y,z) <-> AddF x y z)))
     bridge_mul : prov Gam (Ctx -> forall x y z (x in w -> y in w -> (Mu(x,y,z) <-> MulF x y z)))
   and their universal closures over w, p, g, o. *)
From Stdlib Require Import List Arith Bool PeanoNat NArith.
From Cohen Require Import Syn Prov Kal Ax Checks Replay Replay2 Replay3 Expand Pure RpInit RpInitOk RpFinal.
From L2R Require Import L2RLogic L2RArith L2RFin.
From L2R.b0033 Require Import BrB_0033.
Import ListNotations.
Open Scope nat_scope.

Definition REGP : list entry := firstn 677 REG0.
Lemma REGP_ok : reg_ok hypf REGP.
Proof.
  intros i d h E. apply (REG0_ok i d h).
  assert (Hi : i < List.length REGP) by (apply nth_error_Some; congruence).
  rewrite <- (firstn_skipn 677 REG0). rewrite nth_error_app1 by exact Hi. exact E.
Qed.
Lemma BRB_ok : check_batch REGP BRB = true. Proof. vm_compute. reflexivity. Qed.
Lemma REGB_ok : reg_ok hypf (REGP ++ map ent BRB). Proof. exact (check_batch_ok hypf REGP BRB REGP_ok BRB_ok). Qed.

Definition entry_isB (i : nat) (f : form) : bool :=
  match nth_error (REGP ++ map ent BRB) i with Some (d, []) => form_eqb (tof d) f | _ => false end.
Lemma entry_isB_prov i f : entry_isB i f = true -> prov Gam f.
Proof.
  unfold entry_isB. destruct (nth_error (REGP ++ map ent BRB) i) as [[d [|h r]]|] eqn:E; try discriminate.
  intros Q. apply form_eqb_true in Q. subst f.
  apply (prov_mono (AH hypf [])); [|exact (REGB_ok i d [] E)].
  intros g [G|[h [[] _]]]. exact G.
Qed.

(* ---- the statements *)
Definition CtxF : form := Kf (Kf (Kf (Pr 20 [0]) (Pr 28 [1; 0; 0])) (Pr 38 [2; 1; 0])) (Emp 3).
(* Ad(x,y,z) = exists a (Rec(a,w,g,w,x) & App(a,y,z)), with w, g, x, y, z as seen where the formula stands *)
Definition AdF (w g x y z : nat) : form := Xf (Kf (Pr 30 [0; S w; S g; S w; S x]) (App 0 (S y) (S z))).
(* Mu(x,y,z) = exists m exists a ((Rec(a,w,g,w,x) & Rec(m,w,a,w,o)) & App(m,y,z)) *)
Definition MuF (w g o x y z : nat) : form :=
  Xf (Xf (Kf (Kf (Pr 30 [0; 2 + w; 2 + g; 2 + w; 2 + x]) (Pr 30 [1; 2 + w; 0; 2 + w; 2 + o])) (App 1 (2 + y) (2 + z)))).

(* under the three binders x = 2, y = 1, z = 0 and w = 3, g = 5, o = 6 *)
Definition BAddS : form :=
  Imp CtxF (All (All (All (Imp (Mem 2 3) (Imp (Mem 1 3) (Qf (AdF 3 5 2 1 0) (AddF 2 1 0))))))).
Definition BMulS : form :=
  Imp CtxF (All (All (All (Imp (Mem 2 3) (Imp (Mem 1 3) (Qf (MuF 3 5 6 2 1 0) (MulF 2 1 0))))))).

Lemma badd_entry : entry_isB 740 BAddS = true. Proof. vm_compute. reflexivity. Qed.
Lemma bmul_entry : entry_isB 755 BMulS = true. Proof. vm_compute. reflexivity. Qed.

Theorem bridge_add : prov Gam BAddS.
Proof. exact (entry_isB_prov 740 BAddS badd_entry). Qed.
Theorem bridge_mul : prov Gam BMulS.
Proof. exact (entry_isB_prov 755 BMulS bmul_entry). Qed.

Theorem bridge_add_closed : prov Gam (All (All (All (All BAddS)))).
Proof. repeat apply p_gen. exact bridge_add. Qed.
Theorem bridge_mul_closed : prov Gam (All (All (All (All BMulS)))).
Proof. repeat apply p_gen. exact bridge_mul. Qed.
