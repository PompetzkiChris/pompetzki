(* GrokAsciiDecimal.v - Grok Bot, new file. An explicit ASCII byte decoder in front of the
   unchanged numeric-v5 model (DecimalSignificantV4.parse_decimal).
   Byte representation: list Z. A byte is an integer; ascii_digit accepts exactly 48..57 and
   every other integer (including values outside 0..255) is malformed. Hence every theorem
   below holds for all lists of Z, in particular for all lists of byte values 0..255.
   MODEL THEOREMS ONLY: nothing here is about the pmp/Racket tokenizers, the compiler, or
   executable bytes. *)
From Stdlib Require Import ZArith List Lia Bool.
From NumericV5 Require Import DecimalSignificantV4.
From GrokNumeric Require Import GrokNumericGaps.
Import ListNotations.
Open Scope Z_scope.

Definition ascii_digit (b : Z) : bool := (48 <=? b) && (b <=? 57).
Definition decode_byte (b : Z) : Z := b - 48.
Fixpoint decode_ascii (bs : list Z) : option (list Z) :=
  match bs with
  | [] => Some []
  | b :: r => if ascii_digit b then option_map (cons (decode_byte b)) (decode_ascii r) else None
  end.
Definition parse_ascii_decimal (bs : list Z) : option Z :=
  match decode_ascii bs with Some ds => parse_decimal ds | None => None end.

Definition all_ascii_digits (bs : list Z) : Prop := Forall (fun b => ascii_digit b = true) bs.

(* ---- decoder *)
Theorem decode_ascii_ok_iff : forall bs ds,
  decode_ascii bs = Some ds <-> all_ascii_digits bs /\ ds = map decode_byte bs.
Proof.
  unfold all_ascii_digits. induction bs as [|b r IH]; intros ds; simpl.
  - split; [intros H; injection H as <-; split; [constructor|reflexivity]|intros [_ ->]; reflexivity].
  - destruct (ascii_digit b) eqn:Hb.
    + destruct (decode_ascii r) as [l|] eqn:Er; simpl.
      * specialize (IH l). destruct IH as [IH1 _]. destruct (IH1 eq_refl) as [F ->].
        split; [intros H; injection H as <-; split; [constructor; assumption|reflexivity]|].
        intros [_ ->]; reflexivity.
      * split; [discriminate|]. intros [F _]. inversion F as [|? ? _ Fr].
        pose proof (proj2 (IH (map decode_byte r)) (conj Fr eq_refl)) as C. congruence.
    + split; [discriminate|]. intros [F _]. inversion F; congruence.
Qed.

Lemma decode_ascii_digits_true : forall bs, all_ascii_digits bs -> decode_ascii bs = Some (map decode_byte bs).
Proof. intros bs F. apply decode_ascii_ok_iff. split; [exact F|reflexivity]. Qed.

Lemma decode_ascii_none : forall bs, ~ all_ascii_digits bs -> decode_ascii bs = None.
Proof.
  intros bs NF. destruct (decode_ascii bs) as [ds|] eqn:E; [|reflexivity].
  exfalso. apply NF. apply (proj1 (decode_ascii_ok_iff bs ds) E).
Qed.

Lemma ascii_digit_decode : forall b, ascii_digit b = true -> digit (decode_byte b) = true.
Proof.
  intros b H. unfold ascii_digit in H. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. unfold digit, decode_byte.
  apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
Qed.

Theorem decode_ascii_digits : forall bs ds,
  decode_ascii bs = Some ds -> Forall (fun d => digit d = true) ds.
Proof.
  intros bs ds E. apply decode_ascii_ok_iff in E as [F ->].
  induction F; constructor; [apply ascii_digit_decode; assumption|assumption].
Qed.

(* ---- malformed / empty / zeros *)
Theorem ascii_malformed_refused : forall bs, ~ all_ascii_digits bs -> parse_ascii_decimal bs = None.
Proof. intros bs NF. unfold parse_ascii_decimal. rewrite decode_ascii_none by exact NF. reflexivity. Qed.

Theorem ascii_empty_refused : parse_ascii_decimal [] = None.
Proof. reflexivity. Qed.

Lemma decode_repeat48_app : forall k bs,
  decode_ascii (repeat 48 k ++ bs) = option_map (fun ds => repeat 0 k ++ ds) (decode_ascii bs).
Proof.
  induction k as [|k IH]; intros bs; simpl.
  - destruct (decode_ascii bs); reflexivity.
  - rewrite IH. destruct (decode_ascii bs); reflexivity.
Qed.

Theorem ascii_all_zeros : forall n : nat, (1 <= n)%nat -> parse_ascii_decimal (repeat 48 n) = Some 0.
Proof.
  intros n H. unfold parse_ascii_decimal.
  rewrite <- (app_nil_r (repeat 48 n)), decode_repeat48_app. simpl. rewrite app_nil_r.
  apply parse_decimal_all_zeros; exact H.
Qed.

(* ---- padding: only nonemptiness of bs is needed (no nonzero-first premise). For bs = [] and
   k >= 1 the statement is false: left side Some 0, right side None. *)
Theorem ascii_padding : forall k bs, bs <> [] ->
  parse_ascii_decimal (repeat 48 k ++ bs) = parse_ascii_decimal bs.
Proof.
  intros k bs NE. unfold parse_ascii_decimal. rewrite decode_repeat48_app.
  destruct (decode_ascii bs) as [ds|] eqn:E; simpl; [|reflexivity].
  apply decode_ascii_ok_iff in E as [_ ->]. destruct bs as [|b r]; [contradiction|].
  simpl. apply padded_decimal_preserves.
Qed.

(* ---- more than twelve significant ASCII digits. No validity premise on b or tail is needed
   (a non-digit byte is refused anyway); b <> 48 marks the first significant byte. *)
Definition ascii_significant_split (bs : list Z) (k : nat) (b : Z) (tail : list Z) : Prop :=
  bs = repeat 48 k ++ b :: tail /\ b <> 48.

Theorem ascii_more_than_twelve_refused : forall bs k b tail,
  ascii_significant_split bs k b tail -> (12 < length (b :: tail))%nat -> parse_ascii_decimal bs = None.
Proof.
  intros bs k b tail [-> Hb] L. unfold parse_ascii_decimal. rewrite decode_repeat48_app.
  destruct (decode_ascii (b :: tail)) as [ds|] eqn:E; simpl; [|reflexivity].
  apply decode_ascii_ok_iff in E as [_ ->]. simpl.
  apply (more_than_twelve_significant_refused _ k (decode_byte b) (map decode_byte tail)).
  - split; [reflexivity|unfold decode_byte; lia].
  - simpl in *. rewrite length_map. exact L.
Qed.

Theorem ascii_bound : forall bs v, parse_ascii_decimal bs = Some v -> 0 <= v <= 999999999999.
Proof.
  unfold parse_ascii_decimal. intros bs v. destruct (decode_ascii bs); [apply parse_decimal_bound|discriminate].
Qed.

(* ---- characterization *)
Lemma map_decode_repeat0 : forall l k, map decode_byte l = repeat 0 k -> l = repeat 48 k.
Proof.
  induction l as [|b r IH]; intros [|k] H; simpl in *; try discriminate; [reflexivity|].
  injection H as Hb Hr. f_equal; [unfold decode_byte in Hb; lia|apply IH; exact Hr].
Qed.

Lemma all_ascii_digits_dec : forall bs, {all_ascii_digits bs} + {~ all_ascii_digits bs}.
Proof.
  unfold all_ascii_digits. induction bs as [|b r IH]; [left; constructor|].
  destruct (ascii_digit b) eqn:Hb.
  - destruct IH as [F|NF]; [left; constructor; assumption|right; intro C; inversion C; contradiction].
  - right; intro C; inversion C; congruence.
Defined.

Theorem parse_ascii_decimal_none_iff : forall bs,
  parse_ascii_decimal bs = None <->
  bs = [] \/ ~ all_ascii_digits bs \/
  (exists k b tail, ascii_significant_split bs k b tail /\ (12 < length (b :: tail))%nat).
Proof.
  intros bs. split.
  - intros N. destruct (all_ascii_digits_dec bs) as [F|NF]; [|right; left; exact NF].
    unfold parse_ascii_decimal in N. rewrite decode_ascii_digits_true in N by exact F.
    assert (FD : Forall (fun d => digit d = true) (map decode_byte bs))
      by (apply (decode_ascii_digits bs); apply decode_ascii_digits_true; exact F).
    apply (parse_decimal_none_iff _ FD) in N as [E|[k [d [tail [[E Hd] L]]]]].
    + left. destruct bs; [reflexivity|discriminate].
    + right; right. apply map_eq_app in E as [l1 [l2 [-> [E1 E2]]]].
      apply map_eq_cons in E2 as [b [t [-> [Eb Et]]]].
      exists k, b, t. split; [split|].
      * rewrite (map_decode_repeat0 l1 k E1). reflexivity.
      * intro C. subst. apply Hd. reflexivity.
      * simpl in *. rewrite <- Et, length_map in L. exact L.
  - intros [->|[NF|[k [b [tail [S L]]]]]].
    + reflexivity.
    + apply ascii_malformed_refused; exact NF.
    + exact (ascii_more_than_twelve_refused bs k b tail S L).
Qed.

(* ---- round trip *)
Definition horner (ds : list Z) (a : Z) : Z := fold_left (fun acc d => 10 * acc + d) ds a.

Lemma parse_digits_horner : forall ds a (c : nat),
  Forall (fun d => digit d = true) ds -> (c = 0%nat -> a = 0) -> (c + length ds <= 12)%nat ->
  parse_digits ds a c = Some (horner ds a).
Proof.
  induction ds as [|d t IH]; intros a c F Ha L; [reflexivity|].
  inversion F as [|? ? Hd Ft]; subst. simpl. rewrite Hd. unfold horner; simpl; fold (horner t (10 * a + d)).
  destruct ((Nat.eqb c 0 && (d =? 0))%bool) eqn:Z0.
  - apply andb_true_iff in Z0 as [C D]. apply Nat.eqb_eq in C. apply Z.eqb_eq in D. subst.
    rewrite (Ha eq_refl). simpl in L. replace (10 * 0 + 0) with 0 by lia.
    apply IH; [exact Ft|intros _; reflexivity|lia].
  - simpl in L. replace (Nat.ltb c 12) with true by (symmetry; apply Nat.ltb_lt; lia).
    apply IH; [exact Ft|discriminate|lia].
Qed.

Fixpoint digits_w (w : nat) (v : Z) : list Z :=
  match w with O => [] | S w' => digits_w w' (v / 10) ++ [v mod 10] end.

Lemma digits_w_length : forall w v, length (digits_w w v) = w.
Proof. induction w; intros v; simpl; [reflexivity|rewrite length_app, IHw; simpl; lia]. Qed.

Lemma digits_w_valid : forall w v, Forall (fun d => digit d = true) (digits_w w v).
Proof.
  induction w; intros v; simpl; [constructor|]. apply Forall_app; split; [apply IHw|].
  constructor; [|constructor]. unfold digit. apply andb_true_iff; split;
  [apply Z.leb_le|apply Z.ltb_lt]; pose proof (Z.mod_pos_bound v 10); lia.
Qed.

Lemma digits_w_value : forall w v, 0 <= v -> horner (digits_w w v) 0 = v mod pow10 w.
Proof.
  induction w as [|w IH]; intros v Hv; cbn [digits_w pow10].
  - rewrite Z.mod_1_r. reflexivity.
  - unfold horner. rewrite fold_left_app. fold (horner (digits_w w (v / 10)) 0). cbn [fold_left].
    rewrite IH by (apply Z.div_pos; lia).
    pose proof (pow10_positive w) as P0.
    apply (Z.mod_unique v (10 * pow10 w) ((v / 10) / pow10 w)).
    + left. pose proof (Z.mod_pos_bound (v / 10) (pow10 w) P0).
      pose proof (Z.mod_pos_bound v 10 ltac:(lia)). lia.
    + pose proof (Z.div_mod v 10 ltac:(lia)) as H1.
      pose proof (Z.div_mod (v / 10) (pow10 w) ltac:(lia)) as H2.
      set (q := v / 10) in *. set (P := pow10 w) in *. set (Q := q / P) in *. nia.
Qed.

Definition ascii_spell12 (v : Z) : list Z := map (fun d => d + 48) (digits_w 12 v).

Lemma decode_spelled : forall ds, Forall (fun d => digit d = true) ds ->
  decode_ascii (map (fun d => d + 48) ds) = Some ds.
Proof.
  induction ds as [|d t IH]; intros F; [reflexivity|]. inversion F as [|? ? Hd Ft]; subst.
  apply digit_spec in Hd. simpl.
  replace (ascii_digit (d + 48)) with true by
    (symmetry; unfold ascii_digit; apply andb_true_iff; split; apply Z.leb_le; lia).
  rewrite IH by exact Ft. simpl. unfold decode_byte. f_equal. f_equal. lia.
Qed.

Theorem ascii_round_trip12 : forall v, 0 <= v <= 999999999999 ->
  parse_ascii_decimal (ascii_spell12 v) = Some v.
Proof.
  intros v Hv. unfold parse_ascii_decimal, ascii_spell12. rewrite decode_spelled by apply digits_w_valid.
  destruct (digits_w 12 v) as [|d t] eqn:E; [pose proof (digits_w_length 12 v) as L; rewrite E in L; discriminate|].
  unfold parse_decimal. rewrite <- E.
  rewrite parse_digits_horner; [|apply digits_w_valid|intros _; reflexivity|rewrite digits_w_length; lia].
  rewrite digits_w_value by lia. f_equal. apply Z.mod_small. cbn [pow10]. lia.
Qed.

Theorem ascii_round_trip12_padded : forall k v, 0 <= v <= 999999999999 ->
  parse_ascii_decimal (repeat 48 k ++ ascii_spell12 v) = Some v.
Proof.
  intros k v Hv. rewrite ascii_padding; [apply ascii_round_trip12; exact Hv|].
  unfold ascii_spell12. destruct (digits_w 12 v) eqn:E; [pose proof (digits_w_length 12 v) as L; rewrite E in L; discriminate|discriminate].
Qed.

(* Minimal spelling: strip leading '0' bytes; "0" for v = 0. *)
Fixpoint strip48 (bs : list Z) : list Z :=
  match bs with [] => [] | b :: r => if b =? 48 then strip48 r else bs end.

Lemma strip48_split : forall bs, exists k, bs = repeat 48 k ++ strip48 bs.
Proof.
  induction bs as [|b r [k IH]]; [exists 0%nat; reflexivity|]. simpl.
  destruct (b =? 48) eqn:E; [apply Z.eqb_eq in E; subst; exists (S k); simpl; rewrite <- IH; reflexivity|].
  exists 0%nat; reflexivity.
Qed.

Lemma strip48_head : forall bs b r, strip48 bs = b :: r -> b <> 48.
Proof.
  induction bs as [|x t IH]; intros b r H; simpl in H; [discriminate|].
  destruct (x =? 48) eqn:E; [exact (IH b r H)|]. injection H as <- _. apply Z.eqb_neq; exact E.
Qed.

Definition ascii_spell (v : Z) : list Z :=
  match strip48 (ascii_spell12 v) with [] => [48] | s => s end.

Theorem ascii_spell_no_leading_zero : forall v b r, ascii_spell v = b :: r -> b = 48 -> r = [].
Proof.
  intros v b r. unfold ascii_spell. destruct (strip48 (ascii_spell12 v)) as [|x t] eqn:E.
  - intros H _. injection H as _ <-. reflexivity.
  - intros H Hb. injection H as -> ->. exfalso. exact (strip48_head _ _ _ E Hb).
Qed.

Theorem ascii_round_trip : forall v, 0 <= v <= 999999999999 ->
  parse_ascii_decimal (ascii_spell v) = Some v.
Proof.
  intros v Hv. pose proof (ascii_round_trip12 v Hv) as P. destruct (strip48_split (ascii_spell12 v)) as [k Ek].
  unfold ascii_spell. destruct (strip48 (ascii_spell12 v)) as [|x t] eqn:E.
  - rewrite Ek, app_nil_r in P. destruct k as [|k].
    + exfalso. unfold ascii_spell12 in Ek. pose proof (digits_w_length 12 v) as L.
      destruct (digits_w 12 v); simpl in Ek; [discriminate|discriminate].
    + rewrite ascii_all_zeros in P by lia. injection P as <-. reflexivity.
  - rewrite Ek, ascii_padding in P by discriminate. exact P.
Qed.

Theorem ascii_round_trip_padded : forall k v, 0 <= v <= 999999999999 ->
  parse_ascii_decimal (repeat 48 k ++ ascii_spell v) = Some v.
Proof.
  intros k v Hv. rewrite ascii_padding; [apply ascii_round_trip; exact Hv|].
  unfold ascii_spell. destruct (strip48 (ascii_spell12 v)); discriminate.
Qed.
