(* GrokCompose47.v - Grok Bot, new file. Composes numeric-v5 (DecimalSignificantV4) with
   GrokAuthGate and the released check_thm_ok / check_batch_ok soundness.
   All statements concern Gallina definitions only. NOT proved here: that the pmp / Racket /
   native token parser computes parse_decimal or builds these entries, compiler lowering, or
   executable byte correspondence. numeric-v5 is a standalone model over digit lists (list Z);
   no Rocq definition in the judge development parses text, so the link below is through the
   numbers occurring in entries, not through a verified parser. *)
From Stdlib Require Import List Arith NArith ZArith Bool Lia.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInitOk.
From PMPRepair Require Import PrefixSoundness CanonicalRegistryData CanonicalPrefixSoundness GrokAuthGate.
From NumericV5 Require Import DecimalSignificantV4.
Import ListNotations.

Fixpoint dform_nums (d : dform) : list N :=
  match d with
  | dE x y | dEq x y => [x; y]
  | dP p a => p :: a
  | dN a | dA a | dX a => dform_nums a
  | dI a b | dK a b | dD a b | dQ a b => dform_nums a ++ dform_nums b
  end.
Definition entry_nums (e : entry) : list N := dform_nums (fst e) ++ snd e.
Definition reg_nums (reg : list entry) : list N := flat_map entry_nums reg.
Definition policy_max : N := 999999999999%N.

(* Decoder: numeric-v5 value as N. *)
Definition decN (ds : list Z) : option N := option_map Z.to_N (parse_decimal ds).

Theorem decN_bound ds v : decN ds = Some v -> (v <= policy_max)%N.
Proof.
  unfold decN. destruct (parse_decimal ds) as [z|] eqn:E; simpl; intro H; [|discriminate].
  injection H as <-. apply parse_decimal_bound in E. unfold policy_max. lia.
Qed.

Theorem decN_padded k d tail : decN (repeat 0%Z k ++ d :: tail) = decN (d :: tail).
Proof. unfold decN. rewrite padded_decimal_preserves. reflexivity. Qed.

(* Canonical decimal spelling (most significant digit first), fuel 13 >= digits of policy_max. *)
Fixpoint digits_rev (fuel : nat) (z : Z) : list Z :=
  match fuel with
  | O => []
  | S f => if (z <? 10)%Z then [z] else (z mod 10)%Z :: digits_rev f (z / 10)%Z
  end.
Definition spell (x : N) : list Z := rev (digits_rev 13 (Z.of_N x)).

(* Finite exact check over the 706 proved entries. *)
Definition reg_policy_ok (reg : list entry) : bool :=
  forallb (fun x => (x <=? policy_max)%N &&
                    match decN (spell x) with Some y => N.eqb x y | None => false end)
          (reg_nums reg).

Theorem REG0_policy_ok : reg_policy_ok REG0 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma reg_nums_firstn n reg x : In x (reg_nums (firstn n reg)) -> In x (reg_nums reg).
Proof.
  unfold reg_nums. rewrite !in_flat_map. intros [e [He Hx]].
  exists e. split; [|exact Hx]. revert reg He. induction n; intros [|a r] He; simpl in *; try tauto.
  destruct He as [->|He]; [left; reflexivity|right; apply IHn; exact He].
Qed.

Theorem auth_gate_nums_within_policy reg x :
  auth_gate reg = true -> In x (reg_nums reg) ->
  (x <= policy_max)%N /\ decN (spell x) = Some x.
Proof.
  intros [n ->]%auth_gate_iff Hx. apply reg_nums_firstn in Hx.
  pose proof REG0_policy_ok as P. unfold reg_policy_ok in P. rewrite forallb_forall in P.
  specialize (P x Hx). apply andb_true_iff in P as [P1 P2]. split; [apply N.leb_le; exact P1|].
  destruct (decN (spell x)) as [y|]; [apply N.eqb_eq in P2; subst; reflexivity|discriminate].
Qed.

(* Every padded spelling of a gate-accepted number decodes to that number. *)
Theorem auth_gate_padded_spelling reg x k :
  auth_gate reg = true -> In x (reg_nums reg) ->
  decN (repeat 0%Z k ++ spell x) = Some x.
Proof.
  intros G Hx. destruct (auth_gate_nums_within_policy reg x G Hx) as [_ D].
  destruct (spell x) as [|d tail] eqn:Es; [discriminate|]. rewrite decN_padded. exact D.
Qed.

Theorem auth_gate_check_thm_ok_within_policy reg t :
  auth_gate reg = true -> check_thm reg t = true ->
  prov (AH hypf (t_hyps t)) (tof (t_stmt t)) /\
  (forall x, In x (reg_nums reg) -> (x <= policy_max)%N /\ decN (spell x) = Some x).
Proof.
  intros G C. split; [exact (auth_gate_check_thm_ok reg t G C)|].
  intros x Hx. exact (auth_gate_nums_within_policy reg x G Hx).
Qed.

Theorem auth_gate_check_batch_ok_within_policy reg ts :
  auth_gate reg = true -> check_batch reg ts = true ->
  reg_ok hypf (reg ++ map ent ts) /\
  (forall x, In x (reg_nums reg) -> (x <= policy_max)%N /\ decN (spell x) = Some x).
Proof.
  intros G C. split; [exact (auth_gate_check_batch_ok reg ts G C)|].
  intros x Hx. exact (auth_gate_nums_within_policy reg x G Hx).
Qed.
