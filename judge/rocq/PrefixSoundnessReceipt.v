From Stdlib Require Import List.
From Cohen Require Import Syn Prov Replay2 RpInitOk.
From PMPRepair Require Import PrefixSoundness.

Check firstn_lookup_preserved.
Check reg_ok_firstn.
Check REG0_prefix_ok.
Check authenticated_REG0_prefix_ok.
Check authenticated_REG0_prefix_check_thm_ok.
Check authenticated_REG0_prefix_check_batch_ok.

Print Assumptions firstn_lookup_preserved.
Print Assumptions reg_ok_firstn.
Print Assumptions REG0_prefix_ok.
Print Assumptions authenticated_REG0_prefix_ok.
Print Assumptions authenticated_REG0_prefix_check_thm_ok.
Print Assumptions authenticated_REG0_prefix_check_batch_ok.
