# Gallina decimal-model gap proofs

The new Grok Bot `GrokNumericGaps.v` and its exact statement/assumption receipt
`GrokNumericGapsVerify.v` are copied unchanged from the received archive. They
use the unchanged `NumericV5/DecimalSignificantV4.v` definitions. Source credit,
hashes and the project MIT license are included. External tools and libraries
retain their separate licenses.

The two input cases are distinguished explicitly:

```coq
parse_decimal_empty : parse_decimal [] = None

parse_decimal_all_zeros : forall n : nat,
  (1 <= n)%nat -> parse_decimal (repeat 0 n) = Some 0
```

The significant-digit statement is:

```coq
significant_split ds k d tail :=
  ds = repeat 0 k ++ d :: tail /\ d <> 0

more_than_twelve_significant_refused : forall ds k d tail,
  significant_split ds k d tail ->
  (12 < length (d :: tail))%nat -> parse_decimal ds = None
```

This theorem requires no digit-validity premise. `invalid_digit_refused` separately
proves refusal when any list element is not a valid digit. For valid digit lists,
`parse_decimal_none_iff` characterizes refusal exactly as empty input or more than
twelve significant digits. Five supporting results complete the ten statements
printed in `numeric-types-and-assumptions.txt`.

These are the received statements about the Gallina `list Z` model. They do not
prove a character/byte tokenizer, executable numeric parsing, compiler preservation,
or shipped-byte correspondence. No received hypothesis or conclusion was weakened.

With Python 3 and Rocq plus its standard library, run:

```sh
python build-numeric-gaps-proof.py --output "fresh numeric proof build"
```

The output directory must be new. The builder copies and freshly compiles the
numeric model, new proof module and receipt, then recursively kernel-checks
`GrokNumeric.GrokNumericGapsVerify` with `rocqchk -silent -o`. It uses neither
`-admit` nor `-norec`. Tools can be selected with `--coqc` and `--rocqchk`.

This addendum reports three locally compiled project modules and the recursive
kernel check. It does not adopt the archive's claimed library-count figure.
The received compiled objects are preserved with the archive and excluded from
this source-only public component. Fresh objects and private run artifacts are
separate. The public manifest explicitly lists code, credit, raw successful
outputs, result and hashes.
