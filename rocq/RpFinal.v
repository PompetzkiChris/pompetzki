(* RpFinal.v - the premises of Final.cohen_relative_consistency, proved: the kernel's derivations of TNotchT, CohEx and
   the 46 interface theorems (with every lemma they rest on: 4551 theorems of zfcbase, the chapters lambda and lhull,
   the chain and tpl1) replayed by the checker of Replay2.v (sound by Replay3.v). Then Con(ZFC) -> Con(ZFC + notCH-star)
   with no premise. *)
From Stdlib Require Import List Arith Lia Bool PeanoNat NArith String.
From Cohen Require Import Syn Prov Kal Val Inv Parse Data Checks Ax Use Sub Inv2 Expand Pure Notch Elim Final.
From Cohen Require Import Replay Replay2 Replay3 RpInit RpInitOk RpC10.
Import ListNotations.
Open Scope nat_scope.

Definition REGF : list entry := REG11.
Lemma REGF_ok : reg_ok hypf REGF. Proof. exact REG11_ok. Qed.

Lemma entry_gam i d : nth_error REGF i = Some (d, []) -> prov Gam (tof d).
Proof.
  intros E. apply (prov_mono (AH hypf [])); [|exact (REGF_ok i d [] E)].
  intros g [G|[h [[] _]]]. exact G.
Qed.

Definition entry_is (i : nat) (f : form) : bool :=
  match nth_error REGF i with Some (d, []) => form_eqb (tof d) f | _ => false end.

Lemma entry_is_prov i f : entry_is i f = true -> prov Gam f.
Proof.
  unfold entry_is. destruct (nth_error REGF i) as [[d [|h r]]|] eqn:E; try discriminate.
  intros Q. apply form_eqb_true in Q. subst f. exact (entry_gam i d E).
Qed.

(* ---- TNotchT and CohEx *)
Lemma tnotch_entry : entry_is 4190 (Imp (Pr coh [0]) (Pr vw439 [0; 0])) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cohex_entry : entry_is 1360 (Xf (Pr coh [0])) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem TNOTCH_proved : TNOTCH.
Proof. intros f P. rewrite tnotch_parse in P. injection P as <-. exact (entry_is_prov _ _ tnotch_entry). Qed.

Theorem COHEX_proved : COHEX.
Proof. intros f P. rewrite cohex_parse in P. injection P as <-. exact (entry_is_prov _ _ cohex_entry). Qed.

(* ---- the 46 interface theorems *)
Definition TPL : list (string * nat) := [
  ("TplAex", 5217); ("TplArg", 5219); ("TplAuq", 5218); ("TplC", 5238); ("TplChoice", 5255); ("TplColl", 5245);
  ("TplDist", 5241); ("TplEex", 5220); ("TplErg", 5222); ("TplEuq", 5221); ("TplExt", 5249); ("TplFN", 5256);
  ("TplFound", 5254); ("TplGen", 5248); ("TplIex", 5214); ("TplIff", 5246); ("TplInf", 5253); ("TplInst", 5239);
  ("TplIrg", 5216); ("TplIuq", 5215); ("TplK", 5236); ("TplLeib", 5243); ("TplMp", 5247); ("TplNex", 5211);
  ("TplNrg", 5213); ("TplNuq", 5212); ("TplPair", 5250); ("TplPower", 5252); ("TplQex", 5223);
  ("TplQrg", 5225); ("TplQuq", 5224); ("TplRefl", 5242); ("TplS", 5237); ("TplSa", 5228); ("TplSe1", 5230);
  ("TplSe2", 5231); ("TplSe3", 5232); ("TplSep", 5244); ("TplSi", 5227); ("TplSn", 5226); ("TplSo", 5229);
  ("TplSq1", 5233); ("TplSq2", 5234); ("TplSq3", 5235); ("TplUnion", 5251); ("TplVac", 5240)]%string.

Definition tpl_ok1 (n : string) (i : nat) : bool :=
  match nth_error REGF i, pif n with
  | Some (d, hs), Some f =>
      form_eqb (tof d) f && forallb (fun h => existsb (form_eqb (hypf h)) (hyps_named (iface_hyps n))) hs
  | _, _ => false
  end.

Lemma tpl_check_x :
  forallb (fun n => existsb (fun e => String.eqb (fst e) n && tpl_ok1 (fst e) (snd e)) TPL) iface_names = true.
Proof. vm_compute. reflexivity. Qed.

Theorem KERNEL_proved : KERNEL.
Proof.
  intros n f Hn Hp. pose proof tpl_check_x as C. rewrite forallb_forall in C.
  apply existsb_exists in Hn as [n' [Hn' En]]. apply String.eqb_eq in En. subst n'.
  specialize (C n Hn'). apply existsb_exists in C as [[m i] [_ Q]]. simpl in Q.
  apply andb_true_iff in Q as [Em Q]. apply String.eqb_eq in Em. subst m.
  unfold tpl_ok1 in Q. rewrite Hp in Q.
  destruct (nth_error REGF i) as [[d hs]|] eqn:E; [|discriminate].
  apply andb_true_iff in Q as [Q1 Q2]. apply form_eqb_true in Q1. subst f.
  apply (prov_mono (AH hypf hs)); [|exact (REGF_ok i d hs E)].
  intros g [G|[h [Hh ->]]]; [left; exact G|right].
  rewrite forallb_forall in Q2. specialize (Q2 h Hh). apply existsb_exists in Q2 as [g [Hg Eg]].
  apply form_eqb_true in Eg. rewrite Eg. exact Hg.
Qed.

(* ---- Con(ZFC) -> Con(ZFC + notCH-star), no premise *)
Theorem cohen_relative_consistency_closed : prov Gam0 Bot -> prov ZFpure Bot.
Proof. exact (cohen_relative_consistency KERNEL_proved TNOTCH_proved COHEX_proved). Qed.

Corollary con_zfc_con_notch_closed : ~ prov ZFpure Bot -> ~ prov Gam0 Bot.
Proof. intros C D. exact (C (cohen_relative_consistency_closed D)). Qed.
