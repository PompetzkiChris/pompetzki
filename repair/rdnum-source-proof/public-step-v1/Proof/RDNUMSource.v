From Stdlib Require Import List String ZArith Lia.
From Stdlib Require Import Init.Byte.
From mathcomp Require Import all_ssreflect.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore ExecStep ExecMono.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition pinned_judge_sha256 : string := "4d936cb8103c6aa97fb6ec290f88b3ee636c69f94f0cdb089a4621d9ba251d1b".
Definition retained_reader_bytes : seq byte := [:: x6c; x61; x62; x65; x6c; x20; x53; x4b; x49; x50; x57; x53; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x70; x6f; x73; x20; x6c; x69; x6d; x0a; x77; x68; x65; x6e; x20; x6e; x65; x67; x61; x74; x69; x76; x65; x20; x74; x20; x67; x6f; x74; x6f; x20; x53; x4b; x49; x50; x57; x53; x32; x0a; x72; x65; x74; x75; x72; x6e; x0a; x6c; x61; x62; x65; x6c; x20; x53; x4b; x49; x50; x57; x53; x32; x0a; x73; x65; x74; x20; x63; x20; x70; x65; x65; x6b; x20; x70; x6f; x73; x20; x31; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x63; x20; x33; x32; x0a; x77; x68; x65; x6e; x20; x7a; x65; x72; x6f; x20; x74; x20; x67; x6f; x74; x6f; x20; x53; x4b; x49; x50; x57; x53; x33; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x63; x20; x31; x30; x0a; x77; x68; x65; x6e; x20; x7a; x65; x72; x6f; x20; x74; x20; x67; x6f; x74; x6f; x20; x53; x4b; x49; x50; x57; x53; x33; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x63; x20; x31; x33; x0a; x77; x68; x65; x6e; x20; x7a; x65; x72; x6f; x20; x74; x20; x67; x6f; x74; x6f; x20; x53; x4b; x49; x50; x57; x53; x33; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x63; x20; x39; x0a; x77; x68; x65; x6e; x20; x7a; x65; x72; x6f; x20; x74; x20; x67; x6f; x74; x6f; x20; x53; x4b; x49; x50; x57; x53; x33; x0a; x72; x65; x74; x75; x72; x6e; x0a; x6c; x61; x62; x65; x6c; x20; x53; x4b; x49; x50; x57; x53; x33; x0a; x73; x65; x74; x20; x70; x6f; x73; x20; x61; x64; x64; x20; x70; x6f; x73; x20; x31; x0a; x67; x6f; x74; x6f; x20; x53; x4b; x49; x50; x57; x53; x0a; x0a; x3b; x20; x45; x4e; x44; x54; x4f; x4b; x3a; x20; x74; x68; x65; x20; x74; x6f; x6b; x65; x6e; x20; x65; x6e; x64; x73; x20; x68; x65; x72; x65; x20; x28; x74; x68; x65; x20; x65; x6e; x64; x20; x6f; x66; x20; x74; x68; x65; x20; x69; x6e; x70; x75; x74; x20; x6f; x72; x20; x77; x68; x69; x74; x65; x20; x73; x70; x61; x63; x65; x29; x0a; x6c; x61; x62; x65; x6c; x20; x45; x4e; x44; x54; x4f; x4b; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x70; x6f; x73; x20; x6c; x69; x6d; x0a; x77; x68; x65; x6e; x20; x6e; x65; x67; x61; x74; x69; x76; x65; x20; x74; x20; x67; x6f; x74; x6f; x20; x45; x4e; x44; x54; x4f; x4b; x31; x0a; x72; x65; x74; x75; x72; x6e; x0a; x6c; x61; x62; x65; x6c; x20; x45; x4e; x44; x54; x4f; x4b; x31; x0a; x73; x65; x74; x20; x63; x20; x70; x65; x65; x6b; x20; x70; x6f; x73; x20; x31; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x63; x20; x33; x32; x0a; x77; x68; x65; x6e; x20; x7a; x65; x72; x6f; x20; x74; x20; x67; x6f; x74; x6f; x20; x45; x4e; x44; x54; x4f; x4b; x32; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x63; x20; x31; x30; x0a; x77; x68; x65; x6e; x20; x7a; x65; x72; x6f; x20; x74; x20; x67; x6f; x74; x6f; x20; x45; x4e; x44; x54; x4f; x4b; x32; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x63; x20; x31; x33; x0a; x77; x68; x65; x6e; x20; x7a; x65; x72; x6f; x20; x74; x20; x67; x6f; x74; x6f; x20; x45; x4e; x44; x54; x4f; x4b; x32; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x63; x20; x39; x0a; x77; x68; x65; x6e; x20; x7a; x65; x72; x6f; x20; x74; x20; x67; x6f; x74; x6f; x20; x45; x4e; x44; x54; x4f; x4b; x32; x0a; x74; x65; x78; x74; x20; x57; x48; x59; x20; x22; x61; x20; x74; x6f; x6b; x65; x6e; x20; x64; x6f; x65; x73; x20; x6e; x6f; x74; x20; x65; x6e; x64; x20; x69; x6e; x20; x77; x68; x69; x74; x65; x20; x73; x70; x61; x63; x65; x22; x0a; x67; x6f; x74; x6f; x20; x46; x41; x49; x4c; x0a; x6c; x61; x62; x65; x6c; x20; x45; x4e; x44; x54; x4f; x4b; x32; x0a; x72; x65; x74; x75; x72; x6e; x0a; x0a; x3b; x20; x52; x44; x4e; x55; x4d; x3a; x20; x65; x78; x61; x63; x74; x20; x64; x65; x63; x69; x6d; x61; x6c; x20; x30; x2e; x2e; x39; x39; x39; x39; x39; x39; x39; x39; x39; x39; x39; x39; x3b; x20; x6c; x65; x61; x64; x69; x6e; x67; x20; x7a; x65; x72; x6f; x73; x20; x64; x6f; x20; x6e; x6f; x74; x20; x63; x6f; x75; x6e; x74; x2e; x0a; x3b; x20; x6e; x64; x20; x63; x6f; x75; x6e; x74; x73; x20; x73; x69; x67; x6e; x69; x66; x69; x63; x61; x6e; x74; x20; x64; x69; x67; x69; x74; x73; x2e; x20; x6e; x73; x65; x65; x6e; x20; x72; x65; x63; x6f; x72; x64; x73; x20; x61; x20; x64; x69; x67; x69; x74; x20; x65; x76; x65; x6e; x20; x69; x6e; x20; x61; x6e; x20; x61; x6c; x6c; x2d; x7a; x65; x72; x6f; x20; x74; x6f; x6b; x65; x6e; x2e; x0a; x3b; x20; x54; x68; x65; x20; x31; x33; x74; x68; x20; x73; x69; x67; x6e; x69; x66; x69; x63; x61; x6e; x74; x20; x64; x69; x67; x69; x74; x20; x69; x73; x20; x72; x65; x66; x75; x73; x65; x64; x20; x62; x65; x66; x6f; x72; x65; x20; x6d; x75; x6c; x74; x69; x70; x6c; x69; x63; x61; x74; x69; x6f; x6e; x20; x6f; x72; x20; x61; x64; x64; x69; x74; x69; x6f; x6e; x2e; x0a; x6c; x61; x62; x65; x6c; x20; x52; x44; x4e; x55; x4d; x0a; x67; x6f; x73; x75; x62; x20; x53; x4b; x49; x50; x57; x53; x0a; x73; x65; x74; x20; x6e; x75; x6d; x20; x63; x6f; x6e; x73; x74; x20; x30; x0a; x73; x65; x74; x20; x6e; x64; x20; x63; x6f; x6e; x73; x74; x20; x30; x0a; x73; x65; x74; x20; x6e; x73; x65; x65; x6e; x20; x63; x6f; x6e; x73; x74; x20; x30; x0a; x6c; x61; x62; x65; x6c; x20; x52; x44; x4e; x55; x4d; x31; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x70; x6f; x73; x20; x6c; x69; x6d; x0a; x77; x68; x65; x6e; x20; x6e; x65; x67; x61; x74; x69; x76; x65; x20; x74; x20; x67; x6f; x74; x6f; x20; x52; x44; x4e; x55; x4d; x32; x0a; x67; x6f; x74; x6f; x20; x52; x44; x4e; x55; x4d; x39; x0a; x6c; x61; x62; x65; x6c; x20; x52; x44; x4e; x55; x4d; x32; x0a; x73; x65; x74; x20; x63; x20; x70; x65; x65; x6b; x20; x70; x6f; x73; x20; x31; x0a; x73; x65; x74; x20; x64; x20; x73; x75; x62; x20; x63; x20; x34; x38; x0a; x77; x68; x65; x6e; x20; x6e; x65; x67; x61; x74; x69; x76; x65; x20; x64; x20; x67; x6f; x74; x6f; x20; x52; x44; x4e; x55; x4d; x39; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x64; x20; x31; x30; x0a; x77; x68; x65; x6e; x20; x6e; x65; x67; x61; x74; x69; x76; x65; x20; x74; x20; x67; x6f; x74; x6f; x20; x52; x44; x4e; x55; x4d; x33; x0a; x67; x6f; x74; x6f; x20; x52; x44; x4e; x55; x4d; x39; x0a; x6c; x61; x62; x65; x6c; x20; x52; x44; x4e; x55; x4d; x33; x0a; x73; x65; x74; x20; x6e; x73; x65; x65; x6e; x20; x63; x6f; x6e; x73; x74; x20; x31; x0a; x77; x68; x65; x6e; x20; x7a; x65; x72; x6f; x20; x6e; x64; x20; x67; x6f; x74; x6f; x20; x52; x44; x4e; x55; x4d; x4c; x45; x41; x44; x0a; x67; x6f; x74; x6f; x20; x52; x44; x4e; x55; x4d; x42; x4f; x55; x4e; x44; x0a; x6c; x61; x62; x65; x6c; x20; x52; x44; x4e; x55; x4d; x4c; x45; x41; x44; x0a; x77; x68; x65; x6e; x20; x7a; x65; x72; x6f; x20; x64; x20; x67; x6f; x74; x6f; x20; x52; x44; x4e; x55; x4d; x41; x44; x56; x41; x4e; x43; x45; x0a; x6c; x61; x62; x65; x6c; x20; x52; x44; x4e; x55; x4d; x42; x4f; x55; x4e; x44; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x6e; x64; x20; x31; x32; x0a; x77; x68; x65; x6e; x20; x6e; x65; x67; x61; x74; x69; x76; x65; x20; x74; x20; x67; x6f; x74; x6f; x20; x52; x44; x4e; x55; x4d; x34; x0a; x74; x65; x78; x74; x20; x57; x48; x59; x20; x22; x61; x20; x6e; x75; x6d; x62; x65; x72; x20; x68; x61; x73; x20; x6d; x6f; x72; x65; x20; x74; x68; x61; x6e; x20; x31; x32; x20; x73; x69; x67; x6e; x69; x66; x69; x63; x61; x6e; x74; x20; x64; x69; x67; x69; x74; x73; x22; x0a; x67; x6f; x74; x6f; x20; x46; x41; x49; x4c; x0a; x6c; x61; x62; x65; x6c; x20; x52; x44; x4e; x55; x4d; x34; x0a; x73; x65; x74; x20; x6e; x75; x6d; x20; x6d; x75; x6c; x20; x6e; x75; x6d; x20; x31; x30; x0a; x73; x65; x74; x20; x6e; x75; x6d; x20; x61; x64; x64; x20; x6e; x75; x6d; x20; x64; x0a; x73; x65; x74; x20; x6e; x64; x20; x61; x64; x64; x20; x6e; x64; x20; x31; x0a; x6c; x61; x62; x65; x6c; x20; x52; x44; x4e; x55; x4d; x41; x44; x56; x41; x4e; x43; x45; x0a; x73; x65; x74; x20; x70; x6f; x73; x20; x61; x64; x64; x20; x70; x6f; x73; x20; x31; x0a; x67; x6f; x74; x6f; x20; x52; x44; x4e; x55; x4d; x31; x0a; x6c; x61; x62; x65; x6c; x20; x52; x44; x4e; x55; x4d; x39; x0a; x77; x68; x65; x6e; x20; x7a; x65; x72; x6f; x20; x6e; x73; x65; x65; x6e; x20; x67; x6f; x74; x6f; x20; x52; x44; x4e; x55; x4d; x42; x41; x44; x0a; x67; x6f; x73; x75; x62; x20; x45; x4e; x44; x54; x4f; x4b; x0a; x72; x65; x74; x75; x72; x6e; x0a; x6c; x61; x62; x65; x6c; x20; x52; x44; x4e; x55; x4d; x42; x41; x44; x0a; x74; x65; x78; x74; x20; x57; x48; x59; x20; x22; x61; x20; x6e; x75; x6d; x62; x65; x72; x20; x77; x61; x73; x20; x65; x78; x70; x65; x63; x74; x65; x64; x22; x0a; x67; x6f; x74; x6f; x20; x46; x41; x49; x4c; x0a; x0a; x3b; x20; x52; x44; x54; x41; x47; x3a; x20; x6f; x6e; x65; x20; x63; x68; x61; x72; x61; x63; x74; x65; x72; x20; x2d; x3e; x20; x74; x67; x0a].
Definition Preader : seq stmt := [::
  SLabel "SKIPWS";
  SSub "t" (OV "pos") (OV "lim");
  SWhen CNeg (OV "t") "SKIPWS2";
  SReturn;
  SLabel "SKIPWS2";
  SPeek "c" (OV "pos") 1%N;
  SSub "t" (OV "c") (OL 32);
  SWhen CZero (OV "t") "SKIPWS3";
  SSub "t" (OV "c") (OL 10);
  SWhen CZero (OV "t") "SKIPWS3";
  SSub "t" (OV "c") (OL 13);
  SWhen CZero (OV "t") "SKIPWS3";
  SSub "t" (OV "c") (OL 9);
  SWhen CZero (OV "t") "SKIPWS3";
  SReturn;
  SLabel "SKIPWS3";
  SAdd "pos" (OV "pos") (OL 1);
  SGoto "SKIPWS";
  SLabel "ENDTOK";
  SSub "t" (OV "pos") (OV "lim");
  SWhen CNeg (OV "t") "ENDTOK1";
  SReturn;
  SLabel "ENDTOK1";
  SPeek "c" (OV "pos") 1%N;
  SSub "t" (OV "c") (OL 32);
  SWhen CZero (OV "t") "ENDTOK2";
  SSub "t" (OV "c") (OL 10);
  SWhen CZero (OV "t") "ENDTOK2";
  SSub "t" (OV "c") (OL 13);
  SWhen CZero (OV "t") "ENDTOK2";
  SSub "t" (OV "c") (OL 9);
  SWhen CZero (OV "t") "ENDTOK2";
  STextLit "WHY" (bytes_of_str "a token does not end in white space");
  SGoto "FAIL";
  SLabel "ENDTOK2";
  SReturn;
  SLabel "RDNUM";
  SGosub "SKIPWS";
  SConst "num" (OL 0);
  SConst "nd" (OL 0);
  SConst "nseen" (OL 0);
  SLabel "RDNUM1";
  SSub "t" (OV "pos") (OV "lim");
  SWhen CNeg (OV "t") "RDNUM2";
  SGoto "RDNUM9";
  SLabel "RDNUM2";
  SPeek "c" (OV "pos") 1%N;
  SSub "d" (OV "c") (OL 48);
  SWhen CNeg (OV "d") "RDNUM9";
  SSub "t" (OV "d") (OL 10);
  SWhen CNeg (OV "t") "RDNUM3";
  SGoto "RDNUM9";
  SLabel "RDNUM3";
  SConst "nseen" (OL 1);
  SWhen CZero (OV "nd") "RDNUMLEAD";
  SGoto "RDNUMBOUND";
  SLabel "RDNUMLEAD";
  SWhen CZero (OV "d") "RDNUMADVANCE";
  SLabel "RDNUMBOUND";
  SSub "t" (OV "nd") (OL 12);
  SWhen CNeg (OV "t") "RDNUM4";
  STextLit "WHY" (bytes_of_str "a number has more than 12 significant digits");
  SGoto "FAIL";
  SLabel "RDNUM4";
  SMul "num" (OV "num") (OL 10);
  SAdd "num" (OV "num") (OV "d");
  SAdd "nd" (OV "nd") (OL 1);
  SLabel "RDNUMADVANCE";
  SAdd "pos" (OV "pos") (OL 1);
  SGoto "RDNUM1";
  SLabel "RDNUM9";
  SWhen CZero (OV "nseen") "RDNUMBAD";
  SGosub "ENDTOK";
  SReturn;
  SLabel "RDNUMBAD";
  STextLit "WHY" (bytes_of_str "a number was expected");
  SGoto "FAIL"].
Definition reader_stops : seq string := [:: "FAIL"].
Definition pc_SKIPWS : nat := Eval vm_compute in odflt 0%N (find_label Preader "SKIPWS").
Lemma find_SKIPWS : find_label Preader "SKIPWS" = Some pc_SKIPWS.
Proof. vm_compute; reflexivity. Qed.
Definition pc_ENDTOK : nat := Eval vm_compute in odflt 0%N (find_label Preader "ENDTOK").
Lemma find_ENDTOK : find_label Preader "ENDTOK" = Some pc_ENDTOK.
Proof. vm_compute; reflexivity. Qed.
Definition pc_RDNUM : nat := Eval vm_compute in odflt 0%N (find_label Preader "RDNUM").
Lemma find_RDNUM : find_label Preader "RDNUM" = Some pc_RDNUM.
Proof. vm_compute; reflexivity. Qed.
Definition pc_RDNUM1 : nat := Eval vm_compute in odflt 0%N (find_label Preader "RDNUM1").
Lemma find_RDNUM1 : find_label Preader "RDNUM1" = Some pc_RDNUM1.
Proof. vm_compute; reflexivity. Qed.
Definition pc_RDNUM2 : nat := Eval vm_compute in odflt 0%N (find_label Preader "RDNUM2").
Lemma find_RDNUM2 : find_label Preader "RDNUM2" = Some pc_RDNUM2.
Proof. vm_compute; reflexivity. Qed.
Definition pc_RDNUM3 : nat := Eval vm_compute in odflt 0%N (find_label Preader "RDNUM3").
Lemma find_RDNUM3 : find_label Preader "RDNUM3" = Some pc_RDNUM3.
Proof. vm_compute; reflexivity. Qed.
Definition pc_RDNUMLEAD : nat := Eval vm_compute in odflt 0%N (find_label Preader "RDNUMLEAD").
Lemma find_RDNUMLEAD : find_label Preader "RDNUMLEAD" = Some pc_RDNUMLEAD.
Proof. vm_compute; reflexivity. Qed.
Definition pc_RDNUMBOUND : nat := Eval vm_compute in odflt 0%N (find_label Preader "RDNUMBOUND").
Lemma find_RDNUMBOUND : find_label Preader "RDNUMBOUND" = Some pc_RDNUMBOUND.
Proof. vm_compute; reflexivity. Qed.
Definition pc_RDNUM4 : nat := Eval vm_compute in odflt 0%N (find_label Preader "RDNUM4").
Lemma find_RDNUM4 : find_label Preader "RDNUM4" = Some pc_RDNUM4.
Proof. vm_compute; reflexivity. Qed.
Definition pc_RDNUMADVANCE : nat := Eval vm_compute in odflt 0%N (find_label Preader "RDNUMADVANCE").
Lemma find_RDNUMADVANCE : find_label Preader "RDNUMADVANCE" = Some pc_RDNUMADVANCE.
Proof. vm_compute; reflexivity. Qed.
Definition pc_RDNUM9 : nat := Eval vm_compute in odflt 0%N (find_label Preader "RDNUM9").
Lemma find_RDNUM9 : find_label Preader "RDNUM9" = Some pc_RDNUM9.
Proof. vm_compute; reflexivity. Qed.
Definition pc_RDNUMBAD : nat := Eval vm_compute in odflt 0%N (find_label Preader "RDNUMBAD").
Lemma find_RDNUMBAD : find_label Preader "RDNUMBAD" = Some pc_RDNUMBAD.
Proof. vm_compute; reflexivity. Qed.
Lemma retained_reader_length : size retained_reader_bytes = 1724%N.
Proof. vm_compute; reflexivity. Qed.
