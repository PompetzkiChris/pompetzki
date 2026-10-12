(* New source-bound instantiation of the retained v3 reader argument.
   Existing PmpCore semantics is unchanged; Preader is the current v5 fragment. *)
From Stdlib Require Import List String ZArith Lia.
From mathcomp Require Import all_ssreflect zify.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
From RDNUM Require Import RDNUMSource RDNUMTools.
Set Implicit Arguments.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Definition whitespace (b : Z) : Prop := b = 32 \/ b = 10 \/ b = 13 \/ b = 9.
Definition xpos (s:state) := vars s "pos".
Definition xlim (s:state) := vars s "lim".
Definition byte_at (s:state) (p:Z) := peek s p 1.
Definition reader_frame (names:list string) (s t:state) : Prop :=
  mem t=mem s /\ hp t=hp s /\ forall x, ~List.In x names -> vars t x=vars s x.
Lemma reader_frame_refl ns s : reader_frame ns s s.
Proof. repeat split; reflexivity. Qed.
Lemma reader_frame_trans ns s t u :
 reader_frame ns s t -> reader_frame ns t u -> reader_frame ns s u.
Proof. intros [Hm [Hh Hv]] [Hm' [Hh' Hv']]. split; [congruence|].
 split; [congruence|]. intros x Hx. exact (eq_trans (Hv' x Hx) (Hv x Hx)). Qed.
Lemma reader_frame_var ns s t x : reader_frame ns s t -> ~List.In x ns -> vars t x=vars s x.
Proof. intros [_ [_ H]] Hx. exact (H x Hx). Qed.
Lemma reader_frame_byte ns s t p : reader_frame ns s t -> byte_at t p=byte_at s p.
Proof. intros [H _]. unfold byte_at,peek; simpl; now rewrite H. Qed.
Lemma reader_frame_lim s t : reader_frame [:: "pos";"t";"c"] s t -> xlim t=xlim s.
Proof. intros H. apply (@reader_frame_var [:: "pos";"t";"c"] s t "lim" H).
 simpl; intuition discriminate. Qed.
Ltac rframe := unfold reader_frame; repeat split; try reflexivity;
 intros x Hx; repeat rewrite setv_get;
 repeat match goal with |- context [String.eqb x ?name] =>
  let H:=fresh "Hname" in assert (H:String.eqb x name=false) by
   (apply String.eqb_neq; intro Heq; subst x; apply Hx; simpl; auto); rewrite H
 end; reflexivity.
Definition sw_limit (s : state) := setv s "t" (xpos s - xlim s).
Definition sw_byte (s : state) := setv (sw_limit s) "c" (byte_at s (xpos s)).
Definition sw32 (s : state) := setv (sw_byte s) "t" (byte_at s (xpos s) - 32).
Definition sw10 (s : state) := setv (sw32 s) "t" (byte_at s (xpos s) - 10).
Definition sw13 (s : state) := setv (sw10 s) "t" (byte_at s (xpos s) - 13).
Definition sw9 (s : state) := setv (sw13 s) "t" (byte_at s (xpos s) - 9).

Lemma SKIPWS_end s : xlim s <= xpos s ->
  evals Preader reader_stops pc_SKIPWS [::] s (OReturn (sw_limit s)).
Proof.
  intros H. have Hneg : (xpos s - xlim s <? 0)%Z = false by (apply Z.ltb_ge; lia).
  rs. rs. rsw ltac:(rvars; change (vars (s) "pos" - vars (s) "lim" <? 0)%Z with
    (xpos s - xlim s <? 0)%Z; rewrite Hneg). rsn. reflexivity.
Qed.

Print Assumptions SKIPWS_end.

Lemma not_whitespace_tests b : ~ whitespace b ->
  (b - 32 =? 0)%Z = false /\ (b - 10 =? 0)%Z = false /\
  (b - 13 =? 0)%Z = false /\ (b - 9 =? 0)%Z = false.
Proof. unfold whitespace. intros H. repeat split; apply Z.eqb_neq; lia. Qed.

Lemma SKIPWS_nonwhite s : xpos s < xlim s -> ~ whitespace (byte_at s (xpos s)) ->
  evals Preader reader_stops pc_SKIPWS [::] s (OReturn (sw9 s)).
Proof.
  intros Hlt Hwhite.
  have Hneg : (vars (s) "pos" - vars (s) "lim" <? 0)%Z = true
    by (apply Z.ltb_lt; unfold xpos, xlim in Hlt; lia).
  have [H32 [H10 [H13 H9]]] := not_whitespace_tests Hwhite.
  cbn [byte_at xpos peek] in H32, H10, H13, H9.
  rs. rs. rsw ltac:(rvars; rewrite Hneg).
  rs. rs. rs. rsw ltac:(rvars; unfold peek; cbn; rewrite H32).
  rs. rsw ltac:(rvars; unfold peek; cbn; rewrite H10).
  rs. rsw ltac:(rvars; unfold peek; cbn; rewrite H13).
  rs. rsw ltac:(rvars; unfold peek; cbn; rewrite H9).
  rsn. reflexivity.
Qed.

Lemma ENDTOK_end s : xlim s <= xpos s ->
  evals Preader reader_stops pc_ENDTOK [::] s (OReturn (sw_limit s)).
Proof.
  intros H. have Hneg : (xpos s - xlim s <? 0)%Z = false by (apply Z.ltb_ge; lia).
  rs. rs. rsw ltac:(rvars; change (vars (s) "pos" - vars (s) "lim" <? 0)%Z with
    (xpos s - xlim s <? 0)%Z; rewrite Hneg). rsn. reflexivity.
Qed.

Print Assumptions SKIPWS_nonwhite.
Print Assumptions ENDTOK_end.

Definition sw_choice (s : state) : state :=
  let b := byte_at s (xpos s) in
  if (b =? 32)%Z then sw32 s else
  if (b =? 10)%Z then sw10 s else
  if (b =? 13)%Z then sw13 s else sw9 s.
Definition sw_next (s : state) : state := setv (sw_choice s) "pos" (xpos s + 1).

Lemma sw_next_pos s : xpos (sw_next s) = xpos s + 1.
Proof. unfold sw_next, xpos. rewrite setv_get. reflexivity. Qed.
Lemma sw_choice_frame s : reader_frame [:: "pos"; "t"; "c"] s (sw_choice s).
Proof. unfold sw_choice.
  destruct (byte_at s (xpos s) =? 32)%Z;
  destruct (byte_at s (xpos s) =? 10)%Z;
  destruct (byte_at s (xpos s) =? 13)%Z;
  unfold sw9, sw13, sw10, sw32, sw_byte, sw_limit, setv; rframe. Qed.
Lemma sw_next_frame s : reader_frame [:: "pos"; "t"; "c"] s (sw_next s).
Proof. eapply reader_frame_trans; [apply sw_choice_frame|]. unfold sw_next, setv; rframe. Qed.

Ltac white_cond Hb :=
  rvars; unfold peek; cbn;
  lazymatch goal with |- (if ?b then _ else _) = _ =>
    let H := fresh "Htest" in
    first [assert (H : b = true) by (rewrite Hb; reflexivity)
          |assert (H : b = false) by (rewrite Hb; reflexivity)];
    rewrite H
  end.

Lemma SKIPWS_white s r : xpos s < xlim s -> whitespace (byte_at s (xpos s)) ->
  evals Preader reader_stops pc_SKIPWS [::] (sw_next s) r ->
  evals Preader reader_stops pc_SKIPWS [::] s r.
Proof.
  intros Hlt Hw Hrun.
  have Hneg : (vars (s) "pos" - vars (s) "lim" <? 0)%Z = true
    by (apply Z.ltb_lt; unfold xpos, xlim in Hlt; lia).
  unfold whitespace in Hw. destruct Hw as [Hb|[Hb|[Hb|Hb]]].
  - unfold sw_next, sw_choice in Hrun.
    rewrite Hb in Hrun. cbn in Hrun.
    unfold byte_at, xpos, peek in Hb. cbn in Hb.
    rs. rs. rsw ltac:(rvars; rewrite Hneg). rs. rs. rs.
    rsw ltac:(white_cond Hb). rs. rs. rs. exact Hrun.
  - unfold sw_next, sw_choice in Hrun. rewrite Hb in Hrun. cbn in Hrun.
    unfold byte_at, xpos, peek in Hb. cbn in Hb.
    rs. rs. rsw ltac:(rvars; rewrite Hneg). rs. rs. rs.
    rsw ltac:(white_cond Hb). rs. rsw ltac:(white_cond Hb). rs. rs. rs. exact Hrun.
  - unfold sw_next, sw_choice in Hrun. rewrite Hb in Hrun. cbn in Hrun.
    unfold byte_at, xpos, peek in Hb. cbn in Hb.
    rs. rs. rsw ltac:(rvars; rewrite Hneg). rs. rs. rs.
    rsw ltac:(white_cond Hb). rs. rsw ltac:(white_cond Hb).
    rs. rsw ltac:(white_cond Hb). rs. rs. rs. exact Hrun.
  - unfold sw_next, sw_choice in Hrun. rewrite Hb in Hrun. cbn in Hrun.
    unfold byte_at, xpos, peek in Hb. cbn in Hb.
    rs. rs. rsw ltac:(rvars; rewrite Hneg). rs. rs. rs.
    rsw ltac:(white_cond Hb). rs. rsw ltac:(white_cond Hb).
    rs. rsw ltac:(white_cond Hb). rs. rsw ltac:(white_cond Hb).
    rs. rs. rs. exact Hrun.
Qed.

Print Assumptions SKIPWS_white.

Lemma sw_limit_pos s : xpos (sw_limit s) = xpos s.
Proof. unfold xpos, sw_limit, setv. rvars. reflexivity. Qed.
Lemma sw9_pos s : xpos (sw9 s) = xpos s.
Proof. unfold xpos, sw9, sw13, sw10, sw32, sw_byte, sw_limit, setv. rvars. reflexivity. Qed.
Lemma sw_limit_frame s : reader_frame [:: "pos"; "t"; "c"] s (sw_limit s).
Proof. unfold sw_limit, setv; rframe. Qed.
Lemma sw9_frame s : reader_frame [:: "pos"; "t"; "c"] s (sw9 s).
Proof. unfold sw9, sw13, sw10, sw32, sw_byte, sw_limit, setv; rframe. Qed.

Definition white_prefix (s : state) (n : nat) : Prop :=
  forall i, (i < n)%coq_nat -> whitespace (byte_at s (xpos s + Z.of_nat i)).

Theorem SKIPWS_success s n :
  xpos s + Z.of_nat n <= xlim s -> white_prefix s n ->
  (xpos s + Z.of_nat n = xlim s \/
   ~ whitespace (byte_at s (xpos s + Z.of_nat n))) ->
  exists s', evals Preader reader_stops pc_SKIPWS [::] s (OReturn s') /\
    xpos s' = xpos s + Z.of_nat n /\ reader_frame [:: "pos"; "t"; "c"] s s'.
Proof.
  induction n as [|n IH] in s |- *.
  - intros Hb Hp He. simpl in Hb, He. rewrite Z.add_0_r in Hb, He.
    destruct He as [He|He].
    + exists (sw_limit s). split.
      * apply SKIPWS_end. lia.
      * split; [rewrite sw_limit_pos; lia|apply sw_limit_frame].
    + destruct (Z_lt_ge_dec (xpos s) (xlim s)) as [Hlt|Hge].
      * exists (sw9 s). split.
        -- apply SKIPWS_nonwhite; assumption.
        -- split; [rewrite sw9_pos; lia|apply sw9_frame].
      * exists (sw_limit s). split.
        -- apply SKIPWS_end. lia.
        -- split; [rewrite sw_limit_pos; lia|apply sw_limit_frame].
  - intros Hb Hp He.
    have Hlt : xpos s < xlim s by (rewrite Nat2Z.inj_succ in Hb; lia).
    have Hwhite : whitespace (byte_at s (xpos s)).
    { specialize (Hp 0%N). simpl in Hp. rewrite Z.add_0_r in Hp. apply Hp. lia. }
    have Hframe := sw_next_frame s.
    have Hlim := reader_frame_lim Hframe.
    have Haddr : xpos (sw_next s) + Z.of_nat n = xpos s + Z.of_nat (S n).
    { rewrite sw_next_pos Nat2Z.inj_succ. lia. }
    have Hb' : xpos (sw_next s) + Z.of_nat n <= xlim (sw_next s).
    { rewrite Haddr Hlim. exact Hb. }
    have Hp' : white_prefix (sw_next s) n.
    { intros i Hi. rewrite (@reader_frame_byte [:: "pos"; "t"; "c"] s (sw_next s) _ Hframe).
      have Haddr' : xpos (sw_next s) + Z.of_nat i = xpos s + Z.of_nat (S i).
      { rewrite sw_next_pos Nat2Z.inj_succ. lia. }
      rewrite Haddr'. apply Hp. lia. }
    have He' : xpos (sw_next s) + Z.of_nat n = xlim (sw_next s) \/
      ~ whitespace (byte_at (sw_next s) (xpos (sw_next s) + Z.of_nat n)).
    { rewrite (@reader_frame_byte [:: "pos"; "t"; "c"] s (sw_next s) _ Hframe).
      rewrite Haddr Hlim. exact He. }
    destruct (IH (sw_next s) Hb' Hp' He') as [s' [Hrun [Hpos Hf]]].
    exists s'. split.
    + apply SKIPWS_white; assumption.
    + split; [rewrite Hpos Haddr; reflexivity|].
      exact (reader_frame_trans Hframe Hf).
Qed.

Print Assumptions SKIPWS_success.

Lemma sw_choice_pos s : xpos (sw_choice s) = xpos s.
Proof. unfold sw_choice.
  destruct (byte_at s (xpos s) =? 32)%Z;
  destruct (byte_at s (xpos s) =? 10)%Z;
  destruct (byte_at s (xpos s) =? 13)%Z;
  unfold xpos, sw9, sw13, sw10, sw32, sw_byte, sw_limit, setv; rvars; reflexivity.
Qed.

Lemma ENDTOK_white s : xpos s < xlim s -> whitespace (byte_at s (xpos s)) ->
  evals Preader reader_stops pc_ENDTOK [::] s (OReturn (sw_choice s)).
Proof.
  intros Hlt Hw.
  have Hneg : (vars (s) "pos" - vars (s) "lim" <? 0)%Z = true
    by (apply Z.ltb_lt; unfold xpos, xlim in Hlt; lia).
  unfold whitespace in Hw. destruct Hw as [Hb|[Hb|[Hb|Hb]]].
  - unfold sw_choice. rewrite Hb. cbn.
    unfold byte_at, xpos, peek in Hb. cbn in Hb.
    rs. rs. rsw ltac:(rvars; rewrite Hneg). rs. rs. rs.
    rsw ltac:(white_cond Hb). rs. rsn. reflexivity.
  - unfold sw_choice. rewrite Hb. cbn.
    unfold byte_at, xpos, peek in Hb. cbn in Hb.
    rs. rs. rsw ltac:(rvars; rewrite Hneg). rs. rs. rs.
    rsw ltac:(white_cond Hb). rs. rsw ltac:(white_cond Hb). rs. rsn. reflexivity.
  - unfold sw_choice. rewrite Hb. cbn.
    unfold byte_at, xpos, peek in Hb. cbn in Hb.
    rs. rs. rsw ltac:(rvars; rewrite Hneg). rs. rs. rs.
    rsw ltac:(white_cond Hb). rs. rsw ltac:(white_cond Hb).
    rs. rsw ltac:(white_cond Hb). rs. rsn. reflexivity.
  - unfold sw_choice. rewrite Hb. cbn.
    unfold byte_at, xpos, peek in Hb. cbn in Hb.
    rs. rs. rsw ltac:(rvars; rewrite Hneg). rs. rs. rs.
    rsw ltac:(white_cond Hb). rs. rsw ltac:(white_cond Hb).
    rs. rsw ltac:(white_cond Hb). rs. rsw ltac:(white_cond Hb).
    rs. rsn. reflexivity.
Qed.

Theorem ENDTOK_success s : xpos s <= xlim s ->
  (xpos s = xlim s \/ whitespace (byte_at s (xpos s))) ->
  exists s', evals Preader reader_stops pc_ENDTOK [::] s (OReturn s') /\
    xpos s' = xpos s /\ reader_frame [:: "pos"; "t"; "c"] s s'.
Proof.
  intros Hb He. destruct (Z_lt_ge_dec (xpos s) (xlim s)) as [Hlt|Hge].
  - have Hw : whitespace (byte_at s (xpos s)) by (destruct He; [lia|assumption]).
    exists (sw_choice s). split; [apply ENDTOK_white; assumption|].
    split; [apply sw_choice_pos|apply sw_choice_frame].
  - exists (sw_limit s). split; [apply ENDTOK_end; lia|].
    split; [apply sw_limit_pos|apply sw_limit_frame].
Qed.

Definition token_failure (s : state) : state :=
  (text_new ((sw9 s)) "WHY"
    (bytes_of_str "a token does not end in white space")).

Theorem ENDTOK_failure s : xpos s < xlim s ->
  ~ whitespace (byte_at s (xpos s)) ->
  evals Preader reader_stops pc_ENDTOK [::] s (OStop "FAIL" (token_failure s)).
Proof.
  intros Hlt Hw.
  have Hneg : (vars (s) "pos" - vars (s) "lim" <? 0)%Z = true
    by (apply Z.ltb_lt; unfold xpos, xlim in Hlt; lia).
  have [H32 [H10 [H13 H9]]] := not_whitespace_tests Hw.
  cbn [byte_at xpos peek] in H32, H10, H13, H9.
  rs. rs. rsw ltac:(rvars; rewrite Hneg). rs. rs. rs.
  rsw ltac:(rvars; unfold peek; cbn; rewrite H32).
  rs. rsw ltac:(rvars; unfold peek; cbn; rewrite H10).
  rs. rsw ltac:(rvars; unfold peek; cbn; rewrite H13).
  rs. rsw ltac:(rvars; unfold peek; cbn; rewrite H9).
  rs. rsn. reflexivity.
Qed.

Print Assumptions ENDTOK_success.
Print Assumptions ENDTOK_failure.

