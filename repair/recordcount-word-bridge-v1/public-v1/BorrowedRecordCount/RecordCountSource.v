From Stdlib Require Import List String ZArith Init.Byte.
From mathcomp Require Import all_ssreflect.
From Groebner Require Import ByteText.
From C2Link Require Import PmpCore.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Definition pinned_judge_sha256 : string := "87562735cf20dfd18eb5f26348878b2ac6306bc78714d6953565df9c833d0dc7".
Definition retained_recordcount_bytes : seq byte := [:: x6c; x61; x62; x65; x6c; x20; x52; x45; x43; x4f; x52; x44; x43; x4f; x55; x4e; x54; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x6c; x69; x6d; x20; x70; x6f; x73; x0a; x73; x65; x74; x20; x74; x20; x73; x75; x62; x20; x74; x20; x6e; x75; x6d; x0a; x77; x68; x65; x6e; x20; x6e; x65; x67; x61; x74; x69; x76; x65; x20; x74; x20; x67; x6f; x74; x6f; x20; x52; x45; x43; x4f; x52; x44; x43; x4f; x55; x4e; x54; x42; x41; x44; x0a; x72; x65; x74; x75; x72; x6e; x0a; x6c; x61; x62; x65; x6c; x20; x52; x45; x43; x4f; x52; x44; x43; x4f; x55; x4e; x54; x42; x41; x44; x0a; x74; x65; x78; x74; x20; x57; x48; x59; x20; x22; x61; x20; x72; x65; x63; x6f; x72; x64; x20; x63; x6f; x75; x6e; x74; x20; x65; x78; x63; x65; x65; x64; x73; x20; x72; x65; x6d; x61; x69; x6e; x69; x6e; x67; x20; x69; x6e; x70; x75; x74; x20; x62; x79; x74; x65; x73; x22; x0a; x67; x6f; x74; x6f; x20; x46; x41; x49; x4c; x0a].
Definition Precord : seq stmt := [::
  SLabel "RECORDCOUNT";
  SSub "t" (OV "lim") (OV "pos");
  SSub "t" (OV "t") (OV "num");
  SWhen CNeg (OV "t") "RECORDCOUNTBAD";
  SReturn;
  SLabel "RECORDCOUNTBAD";
  STextLit "WHY" (bytes_of_str "a record count exceeds remaining input bytes");
  SGoto "FAIL"].
Definition record_stops : seq string := [:: "FAIL"].
Definition pc_RECORDCOUNT : nat := 0%N.
Definition pc_RECORDCOUNTBAD : nat := 5%N.
Lemma find_RECORDCOUNT : find_label Precord "RECORDCOUNT" = Some pc_RECORDCOUNT.
Proof. vm_compute; reflexivity. Qed.
Lemma find_RECORDCOUNTBAD : find_label Precord "RECORDCOUNTBAD" = Some pc_RECORDCOUNTBAD.
Proof. vm_compute; reflexivity. Qed.
Lemma retained_recordcount_length : size retained_recordcount_bytes = 182%N.
Proof. vm_compute; reflexivity. Qed.
