(* L2RAgreeMut.v - lane L2R, 2026-10-09. The comparison of L2RAgree.v rejects wrong pairings: each statement against the
   truth value flipped (78 mutants), and against the sentence of the next case in the list (78 mutants, the last against
   the first). *)
From Stdlib Require Import List Arith Bool PeanoNat String.
From Cohen Require Import Syn.
From L2R Require Import L2RSent L2RCases L2RAgree.
Import ListNotations.

Definition flip (c : string * fm * bool * form) : string * fm * bool * form :=
  match c with (n, A, tv, f) => (n, A, negb tv, f) end.

Definition shifted : list (string * fm * bool * form) :=
  map (fun p => match p with ((n, _, tv, f), (_, B, _, _)) => (n, B, tv, f) end)
      (combine cases (tl cases ++ [hd ("", feq (tnum 0) (tnum 0), true, Eqv 0 0) cases])).

Lemma flipped_rejected : forallb (fun c => negb (agrees (flip c))) cases = true.
Proof. vm_compute. reflexivity. Qed.

Lemma shifted_rejected : forallb (fun c => negb (agrees c)) shifted = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mutant_count : (List.length cases + List.length shifted = 156)%nat.
Proof. vm_compute. reflexivity. Qed.
