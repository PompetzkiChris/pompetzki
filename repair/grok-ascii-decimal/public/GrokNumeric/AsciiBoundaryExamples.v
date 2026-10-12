(* Codex supplemental concrete checks of the received Grok ASCII model. *)
From Stdlib Require Import ZArith List Bool.
From GrokNumeric Require Import GrokAsciiDecimal.
Import ListNotations.
Open Scope Z_scope.

Example empty_refused : parse_ascii_decimal [] = None.
Proof. reflexivity. Qed.
Example zero_one_byte : parse_ascii_decimal [48] = Some 0.
Proof. reflexivity. Qed.
Example zero_thirteen_bytes : parse_ascii_decimal (repeat 48 13) = Some 0.
Proof. vm_compute. reflexivity. Qed.
Example zero_256_bytes : parse_ascii_decimal (repeat 48 256) = Some 0.
Proof. vm_compute. reflexivity. Qed.
Example empty_padding_counterexample :
  parse_ascii_decimal (repeat 48 1 ++ []) = Some 0 /\ parse_ascii_decimal [] = None.
Proof. split; reflexivity. Qed.
Example padded_fourteen : parse_ascii_decimal (repeat 48 256 ++ [49; 52]) = Some 14.
Proof. vm_compute. reflexivity. Qed.
Example twelve_significant_accepted : parse_ascii_decimal (repeat 57 12) = Some 999999999999.
Proof. vm_compute. reflexivity. Qed.
Example thirteen_significant_refused : parse_ascii_decimal (repeat 57 13) = None.
Proof. vm_compute. reflexivity. Qed.
Example padded_thirteen_significant_refused : parse_ascii_decimal (repeat 48 256 ++ repeat 57 13) = None.
Proof. vm_compute. reflexivity. Qed.
Example plus_sign_refused : parse_ascii_decimal [43; 49] = None.
Proof. reflexivity. Qed.
Example minus_sign_refused : parse_ascii_decimal [45; 49] = None.
Proof. reflexivity. Qed.
Example space_refused : parse_ascii_decimal [49; 32] = None.
Proof. reflexivity. Qed.
Example comma_refused : parse_ascii_decimal [49; 44] = None.
Proof. reflexivity. Qed.
Example newline_refused : parse_ascii_decimal [49; 10] = None.
Proof. reflexivity. Qed.
Example alphabetic_refused : parse_ascii_decimal [65] = None.
Proof. reflexivity. Qed.
Example negative_integer_refused : parse_ascii_decimal [-1] = None.
Proof. reflexivity. Qed.
Example integer_256_refused : parse_ascii_decimal [256] = None.
Proof. reflexivity. Qed.
Example byte_range_exact_check :
  forallb (fun n => Bool.eqb (ascii_digit (Z.of_nat n))
       ((48 <=? Z.of_nat n) && (Z.of_nat n <=? 57))) (seq 0 256) = true.
Proof. vm_compute. reflexivity. Qed.
Example zero_minimal_spelling : ascii_spell 0 = [48].
Proof. vm_compute. reflexivity. Qed.
Example maximum_minimal_spelling : ascii_spell 999999999999 = repeat 57 12.
Proof. vm_compute. reflexivity. Qed.
Example maximum_roundtrip : parse_ascii_decimal (ascii_spell 999999999999) = Some 999999999999.
Proof. vm_compute. reflexivity. Qed.
Example zero_roundtrip_padded : parse_ascii_decimal (repeat 48 256 ++ ascii_spell 0) = Some 0.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions empty_refused.
Print Assumptions zero_one_byte.
Print Assumptions zero_thirteen_bytes.
Print Assumptions zero_256_bytes.
Print Assumptions empty_padding_counterexample.
Print Assumptions padded_fourteen.
Print Assumptions twelve_significant_accepted.
Print Assumptions thirteen_significant_refused.
Print Assumptions padded_thirteen_significant_refused.
Print Assumptions plus_sign_refused.
Print Assumptions minus_sign_refused.
Print Assumptions space_refused.
Print Assumptions comma_refused.
Print Assumptions newline_refused.
Print Assumptions alphabetic_refused.
Print Assumptions negative_integer_refused.
Print Assumptions integer_256_refused.
Print Assumptions byte_range_exact_check.
Print Assumptions zero_minimal_spelling.
Print Assumptions maximum_minimal_spelling.
Print Assumptions maximum_roundtrip.
Print Assumptions zero_roundtrip_padded.
