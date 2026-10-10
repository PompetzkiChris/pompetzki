(* CohCmp_r4.v - lane LCH, written after the 19:30 outage (R4): replay of out10/05-coh.jdg (CohB-r4.v) and
   out12/06-cmp.jdg (CmpB-r4.v) by Replay2.check_batch over REGP. coh_cmp_ok: every theorem of both files is
   derivable in Gam (reg_ok). The statements are the last theorems of each file: Coh (two hierarchies agree where
   both are defined) and Cmp (any two ordinals are comparable). *)
From Stdlib Require Import List.
From Cohen Require Import Syn Prov Replay2 Replay3 RpInit RpInitOk.
From LCH Require Import LAXred2 CohB_r4 CmpB_r4.
Lemma CHB_ok : check_batch LAXred2.REGP CHB = true. Proof. vm_compute. reflexivity. Qed.
Lemma CMB_ok : check_batch LAXred2.REGP CMB = true. Proof. vm_compute. reflexivity. Qed.
Theorem coh_reg_ok : reg_ok hypf (LAXred2.REGP ++ map ent CHB).
Proof. exact (check_batch_ok hypf _ _ LAXred2.REGP_ok CHB_ok). Qed.
Theorem cmp_reg_ok : reg_ok hypf (LAXred2.REGP ++ map ent CMB).
Proof. exact (check_batch_ok hypf _ _ LAXred2.REGP_ok CMB_ok). Qed.
