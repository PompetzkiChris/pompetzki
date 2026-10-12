(* C2Link.ExecSim - a program P run inside a whole program Pw through an index map phi
   (2026-09-25).  Generalizes ExecEmbed (phi = addn o, no gosub) to routines that call each
   other with gosub and lie at different places of Pw (for example JCNUM and JCPEEK of
   jcanon.pmp: P = P_jcnum ++ P_jcpeek, phi sends each block to its place).
   Hypotheses: the statement of P at pc is the statement of Pw at phi pc; a statement that can
   continue at the next index (all but goto and return) has phi (pc+1) = phi pc + 1 (this also
   makes the return index of a gosub correspond); every label of P that is not a stop is found in
   Pw at the image of its place in P.
     exec_sim   a run of P from pc with the stack ks is the run of Pw from phi pc with the stack
                map phi ks ++ K: the same stop, and a return of P with an empty stack continues
                Pw at k with the stack K' when K = k :: K', with less fuel. *)
From Stdlib Require Import String ZArith Lia.
From mathcomp Require Import all_ssreflect.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition falls (s : stmt) : bool := match s with SGoto _ | SReturn => false | _ => true end.

Section Sim.
Variables (P Pw : seq stmt) (stops : seq string) (phi : nat -> nat).
Hypothesis H1 : forall pc, (pc < size P)%N ->
  (phi pc < size Pw)%N /\ nth (STrace true) Pw (phi pc) = nth (STrace true) P pc.
Hypothesis H2 : forall pc, (pc < size P)%N -> falls (nth (STrace true) P pc) -> phi pc.+1 = (phi pc).+1.
Hypothesis H3 : forall l i, ~~ has (String.eqb l) stops -> find_label P l = Some i ->
  find_label Pw l = Some (phi i).

Lemma exec_sim f : forall pc ks st K,
  match exec f P stops pc ks st with
  | OStop l st' => exec f Pw stops (phi pc) (map phi ks ++ K) st = OStop l st'
  | OReturn st' =>
      match K with
      | [::] => exec f Pw stops (phi pc) (map phi ks ++ K) st = OReturn st'
      | k :: K' => exists g, (g < f)%N /\ exec f Pw stops (phi pc) (map phi ks ++ K) st = exec g Pw stops k K' st'
      end
  | _ => True
  end.
Proof.
elim: f => [//|f ih] pc ks st K.
case: (ltnP pc (size P)) => hpc; last first.
  have -> : exec f.+1 P stops pc ks st = OStuck pc.
    have E : exec f.+1 P stops pc ks st =
      if Nat.ltb pc (size P) then run_stmt f P stops pc ks st (nth (STrace true) P pc) else OStuck pc by [].
    by rewrite E; move/leP/Nat.ltb_ge: hpc => ->.
  by [].
have [hw hn] := H1 hpc.
have hf := H2 hpc.
rewrite (@exec_S f P stops pc ks st hpc) (@exec_S f Pw stops (phi pc) (map phi ks ++ K) st hw) hn.
(* a jump from pc with the stack ks of P *)
have jmp : forall l ks0 K0, (match jumpo f P stops pc l ks0 st with
  | OStop l0 st' => jumpo f Pw stops (phi pc) l (map phi ks0 ++ K0) st = OStop l0 st'
  | OReturn st' =>
      match K0 with
      | [::] => jumpo f Pw stops (phi pc) l (map phi ks0 ++ K0) st = OReturn st'
      | k :: K' => exists g, (g < f.+1)%N /\ jumpo f Pw stops (phi pc) l (map phi ks0 ++ K0) st = exec g Pw stops k K' st'
      end
  | _ => True
  end : Prop).
  move=> l ks0 K0; rewrite /jumpo.
  case hs: (has (String.eqb l) stops) => //.
  case hfl: (find_label P l) => [i|] //.
  rewrite (H3 (negbT hs) hfl).
  have := ih i ks0 st K0.
  case: (exec f P stops i ks0 st) => // st'.
  case: K0 => [//|k K'] [g [hg e]].
  by exists g; split=> //; apply: ltnW.
(* continuing at pc + 1 with the state st1 *)
have nxt : forall st1, falls (nth (STrace true) P pc) -> (match exec f P stops pc.+1 ks st1 with
  | OStop l0 st' => exec f Pw stops (phi pc).+1 (map phi ks ++ K) st1 = OStop l0 st'
  | OReturn st' =>
      match K with
      | [::] => exec f Pw stops (phi pc).+1 (map phi ks ++ K) st1 = OReturn st'
      | k :: K' => exists g, (g < f.+1)%N /\ exec f Pw stops (phi pc).+1 (map phi ks ++ K) st1 = exec g Pw stops k K' st'
      end
  | _ => True
  end : Prop).
  move=> st1 fl; rewrite -(hf fl).
  have := ih pc.+1 ks st1 K.
  case: (exec f P stops pc.+1 ks st1) => // st'.
  case: K => [//|k K'] [g [hg e]].
  by exists g; split=> //; apply: ltnW.
move: hf nxt; case: (nth (STrace true) P pc) => [x a|x a b|x a b|x a b|x a w|a w b|x a|x bs|x a l|x a b|c a l|l|l||l|b] hf nxt;
  cbn [run_stmt]; try (by apply: nxt).
- by case: (test c (ev st a)); [exact: (jmp l ks K) | apply: nxt].
- exact: (jmp l ks K).
- have e : (phi pc).+1 :: map phi ks ++ K = map phi (pc.+1 :: ks) ++ K by rewrite /= (hf erefl).
  by rewrite e; exact: (jmp l (pc.+1 :: ks) K).
- clear jmp nxt; case: ks => [|k ks'] /=.
  + by case: K => [//|k K']; exists f.
  + have := ih k ks' st K.
    case: (exec f P stops k ks' st) => // st'.
    case: K => [//|k' K'] [g [hg e]].
    by exists g; split=> //; apply: ltnW.
Qed.
End Sim.
