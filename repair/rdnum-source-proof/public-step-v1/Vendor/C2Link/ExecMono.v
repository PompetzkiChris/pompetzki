(* C2Link.ExecMono - more fuel does not change a finished run; runs that finish (2026-09-25).
     exec_mono    exec f ... <> OFuel -> exec (f + g) ... = exec f ...
     evals P stops pc ks st r   the run from (pc, ks, st) finishes with r: for all large fuel,
                  exec gives r (r is then not OFuel when r is a return or a stop)
     evals_step   one statement from (pc, ks, st) goes to (pc', ks', st'): a finished run from
                  the second is a finished run from the first
     evals_now    one statement from (pc, ks, st) gives r directly *)
From Stdlib Require Import String ZArith Lia.
From mathcomp Require Import all_ssreflect.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma exec_unfold f P stops pc ks st : exec f.+1 P stops pc ks st =
  if Nat.ltb pc (size P) then run_stmt f P stops pc ks st (nth (STrace true) P pc) else OStuck pc.
Proof. by []. Qed.

Lemma exec_mono f : forall g P stops pc ks st, exec f P stops pc ks st <> OFuel ->
  exec (f + g) P stops pc ks st = exec f P stops pc ks st.
Proof.
elim: f => [//|f ih] g P stops pc ks st.
rewrite addSn !exec_unfold.
case: (Nat.ltb pc (size P)) => //.
case: (nth (STrace true) P pc) => [x a|x a b|x a b|x a b|x a w|a w b|x a|x bs|x a l|x a b|c a l|l|l||l|b] /=;
  try exact: ih.
- case: (test c (ev st a)); last exact: ih.
  rewrite /jumpo; case: (has _ _) => //; case: (find_label P l) => [i|] //; exact: ih.
- rewrite /jumpo; case: (has _ _) => //; case: (find_label P l) => [i|] //; exact: ih.
- rewrite /jumpo; case: (has _ _) => //; case: (find_label P l) => [i|] //; exact: ih.
- by case: ks => [|k ks] //; exact: ih.
Qed.

Definition evals (P : seq stmt) (stops : seq string) (pc : nat) (ks : seq nat) (st : state)
  (r : outcome) : Prop :=
  exists f0, forall f, (f0 <= f)%N -> exec f P stops pc ks st = r.

Lemma evals_exec f P stops pc ks st : exec f P stops pc ks st <> OFuel ->
  evals P stops pc ks st (exec f P stops pc ks st).
Proof.
move=> h; exists f => f' le.
by rewrite -(subnKC le) exec_mono.
Qed.

Lemma evals_fun P stops pc ks st r1 r2 : evals P stops pc ks st r1 -> evals P stops pc ks st r2 -> r1 = r2.
Proof.
case=> f1 h1 [f2 h2].
by rewrite -(h1 (maxn f1 f2)) ?leq_maxl // -(h2 (maxn f1 f2)) ?leq_maxr.
Qed.

Lemma evals_step P stops pc ks st pc' ks' st' r :
  (forall f, exec f.+1 P stops pc ks st = exec f P stops pc' ks' st') ->
  evals P stops pc' ks' st' r -> evals P stops pc ks st r.
Proof.
move=> h [f0 h0]; exists f0.+1 => [[//|f] le].
by rewrite h; apply: h0.
Qed.

Lemma evals_now P stops pc ks st r :
  (forall f, exec f.+1 P stops pc ks st = r) -> evals P stops pc ks st r.
Proof. by move=> h; exists 1%N => [[//|f] _]; rewrite h. Qed.
