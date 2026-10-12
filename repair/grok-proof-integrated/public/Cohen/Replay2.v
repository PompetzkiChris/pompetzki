(* Replay2.v - the step language, the registry, the checker and its soundness.
   Data formulas (dform) carry numbers in binary (N) and the kernel's abbreviations K D Q X, so a transcribed proof is as
   long as the kernel's text; tof expands them (sharing the repeated parts). A theorem is its statement over its own
   free variables, the map sig of those into the theorem's frame, its lines, and the placeholder hypotheses it claims.
   A registry entry is a statement with the placeholder hypotheses it rests on; AH hs is Gam with those hypotheses. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Sub Expand Replay ReplayT.
Import ListNotations.
Open Scope nat_scope.

Inductive dform : Type :=
| dE (x y : N) | dEq (x y : N) | dP (p : N) (a : list N)
| dN (a : dform) | dI (a b : dform) | dA (a : dform)
| dK (a b : dform) | dD (a b : dform) | dQ (a b : dform) | dX (a : dform).

Fixpoint tof (d : dform) : form :=
  match d with
  | dE x y => Mem (N.to_nat x) (N.to_nat y)
  | dEq x y => Eqv (N.to_nat x) (N.to_nat y)
  | dP p a => Pr (N.to_nat p) (map N.to_nat a)
  | dN a => Neg (tof a)
  | dI a b => Imp (tof a) (tof b)
  | dA a => All (tof a)
  | dK a b => Kf (tof a) (tof b)
  | dD a b => Df (tof a) (tof b)
  | dQ a b => Qf (tof a) (tof b)
  | dX a => Xf (tof a)
  end.

Inductive step : Type :=
| SUse (r : N) (sig : list N)            (* registry entry r, its variables to the frame by sig *)
| SSpec (l : N) (ts : list N)            (* line l, its leading A's instantiated by frame variables ts *)
| SGen (l : N) (k : N)                   (* A (frame variable k) (line l) *)
| SMp (i j : N)
| STaut (ls : list N) (g : dform)
| SExi (t : N) (g : dform)
| SExel (l k : N) (g : dform)
| SAlli (k l : N) (g : dform)
| SInst (t : N) (g : dform)
| SLeib (a : dform) (g : dform)
| SAx (g : dform).                       (* k s c dist vac refl sep coll *)

Record thm : Type := Thm { t_stmt : dform; t_sig : list N; t_steps : list step; t_hyps : list N }.
Definition entry : Type := (dform * list N)%type.

(* ---- the axiom shapes *)
Definition unskip (n : nat) : nat := match n with 0 => 0 | 1 => 0 | S (S m) => S m end.
Definition isSep (g : form) : bool :=
  match g with
  | All (Neg (All (Neg (All (Neg (Imp (Imp _ (Neg (Imp _ (Neg F)))) _)))))) =>
      negb (free 1 F) && form_eqb g (SepF (ren unskip F))
  | _ => false
  end.
Definition isColl (g : form) : bool :=
  match g with All (Imp (All (Imp _ (Neg (All (Neg F))))) _) => form_eqb g (CollF F) | _ => false end.
Fixpoint isSepN (g : form) : bool := isSep g || match g with All h => isSepN h | _ => false end.
Fixpoint isCollN (g : form) : bool := isColl g || match g with All h => isCollN h | _ => false end.

Definition axshape (g : form) : bool :=
  match g with
  | Imp a (Imp b a') => form_eqb a a'
  | _ => false
  end
  || match g with
     | Imp (Imp a (Imp b c)) (Imp (Imp a' b') (Imp a'' c')) =>
         form_eqb a a' && form_eqb a a'' && form_eqb b b' && form_eqb c c'
     | _ => false
     end
  || match g with Imp (Imp (Neg a) (Neg b)) (Imp b' a') => form_eqb a a' && form_eqb b b' | _ => false end
  || match g with
     | Imp (All (Imp a b)) (Imp (All a') (All b')) => form_eqb a a' && form_eqb b b'
     | _ => false
     end
  || match g with Imp a (All b) => form_eqb b (ren S a) | _ => false end
  || match g with Eqv x y => Nat.eqb x y | _ => false end
  || isSepN g || isCollN g.

(* ---- one step *)
Definition nthN {A : Type} (l : list A) (i : N) : option A := nth_error l (N.to_nat i).
Definition sigf (sig : list N) : nat -> nat := fun i => nth i (map N.to_nat sig) 0.

Fixpoint specn (f : form) (ts : list N) : option form :=
  match ts with
  | [] => Some f
  | t :: r => match f with All b => specn (ren (scons (N.to_nat t) sid) b) r | _ => None end
  end.

Fixpoint prems (lines : list form) (ls : list N) : option (list form) :=
  match ls with
  | [] => Some []
  | l :: r => match nthN lines l, prems lines r with Some f, Some fs => Some (f :: fs) | _, _ => None end
  end.

Definition sstep (reg : list entry) (lines : list form) (st : step) : option (form * list N) :=
  match st with
  | SUse r sig => match nthN reg r with Some (d, h) => Some (ren (sigf sig) (tof d), h) | None => None end
  | SSpec l ts => match nthN lines l with Some F => option_map (fun G => (G, [])) (specn F ts) | None => None end
  | SGen l k => match nthN lines l with Some F => Some (All (ren (absk (N.to_nat k)) F), []) | None => None end
  | SMp i j =>
      match nthN lines i, nthN lines j with
      | Some a, Some (Imp a' b) => if form_eqb a a' then Some (b, []) else None
      | _, _ => None
      end
  | STaut ls g =>
      let G := tof g in
      match prems lines ls with Some ps => if tautchk2 (fold_right Imp G ps) then Some (G, []) else None | None => None end
  | SExi t g =>
      let G := tof g in
      match G with
      | Imp F (Neg (All (Neg f))) => if form_eqb F (ren (scons (N.to_nat t) sid) f) then Some (G, []) else None
      | _ => None
      end
  | SExel l k g =>
      let G := tof g in
      match G, nthN lines l with
      | Imp (Neg (All (Neg P'))) G2, Some (Imp P G3) =>
          if form_eqb G2 G3 && form_eqb P' (ren (absk (N.to_nat k)) P) && negb (free (N.to_nat k) G2)
          then Some (G, []) else None
      | _, _ => None
      end
  | SAlli k l g =>
      let G := tof g in
      match G, nthN lines l with
      | Imp H (All f'), Some (Imp H2 f) =>
          if form_eqb H H2 && form_eqb f' (ren (absk (N.to_nat k)) f) && negb (free (N.to_nat k) H)
          then Some (G, []) else None
      | _, _ => None
      end
  | SInst t g =>
      let G := tof g in
      match G with
      | Imp (All f) G2 => if form_eqb G2 (ren (scons (N.to_nat t) sid) f) then Some (G, []) else None
      | _ => None
      end
  | SLeib a g =>
      let G := tof g in let A := tof a in
      match G with
      | Imp (Eqv s t) (Imp X Y) =>
          if form_eqb X (ren (scons s sid) A) && form_eqb Y (ren (scons t sid) A) then Some (G, []) else None
      | _ => None
      end
  | SAx g => let G := tof g in if axshape G then Some (G, []) else None
  end.

Fixpoint run (reg : list entry) (lines : list form) (hs : list N) (sts : list step) : option (list form * list N) :=
  match sts with
  | [] => Some (lines, hs)
  | st :: r => match sstep reg lines st with Some (f, h) => run reg (lines ++ [f]) (hs ++ h) r | None => None end
  end.

Fixpoint idxn (j : nat) (l : list nat) : nat := match l with [] => 0 | x :: r => if Nat.eqb j x then 0 else S (idxn j r) end.
Fixpoint nodupb (l : list nat) : bool := match l with [] => true | x :: r => negb (existsb (Nat.eqb x) r) && nodupb r end.
Definition subsetb (a b : list N) : bool := forallb (fun h => existsb (N.eqb h) b) a.

Definition check_thm (reg : list entry) (t : thm) : bool :=
  match run reg [] [] (t_steps t) with
  | Some (lines, hs) =>
      match last lines Bot with
      | L => form_eqb L (ren (sigf (t_sig t)) (tof (t_stmt t)))
             && nodupb (map N.to_nat (t_sig t)) && closedk (length (t_sig t)) (tof (t_stmt t))
             && subsetb hs (t_hyps t) && negb (Nat.eqb (length lines) 0)
      end
  | None => false
  end.

Definition ent (t : thm) : entry := (t_stmt t, t_hyps t).

Fixpoint check_batch (reg : list entry) (ts : list thm) : bool :=
  match ts with [] => true | t :: r => check_thm reg t && check_batch (reg ++ [ent t]) r end.

(* ---- soundness *)
Section Sound.
Variable hypf : N -> form.
Definition AH (hs : list N) : form -> Prop := fun g => Gam g \/ exists h, In h hs /\ g = hypf h.
Definition reg_ok (reg : list entry) : Prop := forall i d h, nth_error reg i = Some (d, h) -> prov (AH h) (tof d).

Lemma AH_mono hs hs' f : incl hs hs' -> prov (AH hs) f -> prov (AH hs') f.
Proof.
  intros I. apply prov_mono. intros g [G|[h [Hh E]]]; [left; exact G|right; exists h; split; [apply I; exact Hh|exact E]].
Qed.

Lemma ren_Qf' s a b : ren s (Qf a b) = Qf (ren s a) (ren s b). Proof. reflexivity. Qed.

Lemma allN_sep g : isSepN g = true -> forall hs, prov (AH hs) g.
Proof.
  induction g; intros H hs; simpl in H; try discriminate.
  apply orb_true_iff in H as [H|H].
  - unfold isSep in H.
    destruct g as [| | | g1 | |]; try discriminate.
    destruct g1 as [| | | | |g2]; try discriminate.
    destruct g2 as [| | |g3| |]; try discriminate.
    destruct g3 as [| | | | |g4]; try discriminate.
    destruct g4 as [| | |g5| |]; try discriminate.
    destruct g5 as [| | | |g6 g7|]; try discriminate.
    destruct g6 as [| | | |g8 g9|]; try discriminate.
    destruct g9 as [| | |g10| |]; try discriminate.
    destruct g10 as [| | | |g11 g12|]; try discriminate.
    destruct g12 as [| | |F| |]; try discriminate.
    apply andb_true_iff in H as [_ H]. apply form_eqb_true in H. rewrite H. apply p_ax. left. right. left. eexists. reflexivity.
  - apply p_gen. apply IHg. exact H.
Qed.

Lemma allN_coll g : isCollN g = true -> forall hs, prov (AH hs) g.
Proof.
  induction g; intros H hs; simpl in H; try discriminate.
  apply orb_true_iff in H as [H|H].
  - unfold isColl in H.
    destruct g as [| | | |g1 g2|]; try discriminate.
    destruct g1 as [| | | | |g3]; try discriminate.
    destruct g3 as [| | | |g4 g5|]; try discriminate.
    destruct g5 as [| | |g6| |]; try discriminate.
    destruct g6 as [| | | | |g7]; try discriminate.
    destruct g7 as [| | |F| |]; try discriminate.
    apply form_eqb_true in H. rewrite H. apply p_ax. left. right. right. left. eexists. reflexivity.
  - apply p_gen. apply IHg. exact H.
Qed.

Lemma isSep_notall_coll g : isSepN g = false -> isCollN g = true -> forall hs, prov (AH hs) g.
Proof. intros _ H. apply allN_coll. exact H. Qed.

Lemma axshape_ok g hs : axshape g = true -> prov (AH hs) g.
Proof.
  unfold axshape. intros H.
  repeat (apply orb_true_iff in H as [H|H]).
  - destruct g as [| | | |a [| | | |b a'|]|]; try discriminate. apply form_eqb_true in H. subst. apply p_k.
  - destruct g as [| | | |[| | | |a [| | | |b c|]|] [| | | |[| | | |a' b'|] [| | | |a'' c'|]|]|]; try discriminate.
    repeat (apply andb_true_iff in H as [H ?]); repeat match goal with E : form_eqb _ _ = true |- _ => apply form_eqb_true in E end.
    subst. apply p_s.
  - destruct g as [| | | |[| | | |[| | |a| |] [| | |b| |]|] [| | | |b' a'|]|]; try discriminate.
    apply andb_true_iff in H as [H1 H2]. apply form_eqb_true in H1, H2. subst. apply p_c.
  - destruct g as [| | | |[| | | | |[| | | |a b|]] [| | | |[| | | | |a'] [| | | | |b']|]|]; try discriminate.
    apply andb_true_iff in H as [H1 H2]. apply form_eqb_true in H1, H2. subst. apply p_dist.
  - destruct g as [| | | |a [| | | | |b]|]; try discriminate. apply form_eqb_true in H. subst. apply p_vac.
  - destruct g as [| x y| | | |]; try discriminate. apply Nat.eqb_eq in H. subst. apply p_refl.
  - apply allN_sep. exact H.
  - apply allN_coll. exact H.
Qed.
End Sound.
