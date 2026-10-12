(* C2Link.ExecStep - one step of PmpCore.exec as a rewrite rule, and reading variables of the
   states the statements build (2026-09-25).  Used to run a routine symbolically one statement
   at a time without unfolding the program text into the goal.
     exec_S        with fuel f+1 at an index inside the program, exec runs the statement there
                   (run_stmt, the body of exec written out; jumpo is its jump)
     text_new_get  the variables after text x "LIT" *)
From Stdlib Require Import String ZArith Lia.
From Stdlib Require Import Init.Byte.
From mathcomp Require Import all_ssreflect.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope Z_scope.

Definition jumpo (f : nat) (P : seq stmt) (stops : seq string) (pc : nat) (l : string)
    (ks : seq nat) (st : state) : outcome :=
  if has (String.eqb l) stops then OStop l st
  else match find_label P l with Some i => exec f P stops i ks st | None => OStuck pc end.

Definition run_stmt (f : nat) (P : seq stmt) (stops : seq string) (pc : nat) (ks : seq nat)
    (st : state) (s : stmt) : outcome :=
  match s with
  | SConst x a => exec f P stops pc.+1 ks (setv st x (ev st a))
  | SAdd x a b => exec f P stops pc.+1 ks (setv st x (ev st a + ev st b))
  | SSub x a b => exec f P stops pc.+1 ks (setv st x (ev st a - ev st b))
  | SMul x a b => exec f P stops pc.+1 ks (setv st x (ev st a * ev st b))
  | SPeek x a w => exec f P stops pc.+1 ks (setv st x (peek st (ev st a) w))
  | SPoke a w b => exec f P stops pc.+1 ks (poke st (ev st a) w (ev st b))
  | SAlloc x a => exec f P stops pc.+1 ks (seth (setv st x (hp st)) (hp st + ev st a))
  | STextLit x bs => exec f P stops pc.+1 ks (text_new st x bs)
  | STextPad x a l => exec f P stops pc.+1 ks (text_new st x (bytes_at st (ev st a) (Z.to_nat (ev st l))))
  | STextCmp x a b =>
      exec f P stops pc.+1 ks (setv st x (if text_of st a == text_of st b then 0 else 1))
  | SWhen c a l => if test c (ev st a) then jumpo f P stops pc l ks st else exec f P stops pc.+1 ks st
  | SGoto l => jumpo f P stops pc l ks st
  | SGosub l => jumpo f P stops pc l (pc.+1 :: ks) st
  | SReturn => if ks is k :: ks' then exec f P stops k ks' st else OReturn st
  | SLabel _ | STrace _ => exec f P stops pc.+1 ks st
  end.

Lemma exec_S f P stops pc ks st : (pc < size P)%N ->
  exec f.+1 P stops pc ks st = run_stmt f P stops pc ks st (nth (STrace true) P pc).
Proof.
move/ltP/Nat.ltb_lt => h.
have E : exec f.+1 P stops pc ks st =
  if Nat.ltb pc (size P) then run_stmt f P stops pc ks st (nth (STrace true) P pc) else OStuck pc.
  by [].
by rewrite E h.
Qed.

Lemma text_new_get st x bs y : vars (text_new st x bs) y =
  if String.eqb y (lenv x) then Z.of_nat (size bs) else if String.eqb y x then hp st else vars st y.
Proof. by rewrite /text_new /= write_bytes_vars. Qed.

Lemma text_new_hpE st x bs : hp (text_new st x bs) = hp st + Z.of_nat (size bs) + 1.
Proof. by []. Qed.
