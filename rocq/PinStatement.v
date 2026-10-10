(* PinStatement.v - the statement of the closed theorem, pinned: this file compiles only if
   RpFinal.cohen_relative_consistency_closed has exactly this type. What Gam0, ZFpure, prov and Bot mean is pinned by
   the SHA-256 of the files that define them (STATEMENT.sha256, checked by check-closed.sh). *)
From Cohen Require Import Syn Prov Checks Ax Pure Elim RpFinal.
Definition CLOSED_STATEMENT : Prop := prov Gam0 Bot -> prov ZFpure Bot.
Definition pinned : CLOSED_STATEMENT := cohen_relative_consistency_closed.
Definition CLOSED_COROLLARY : Prop := ~ prov ZFpure Bot -> ~ prov Gam0 Bot.
Definition pinned_corollary : CLOSED_COROLLARY := con_zfc_con_notch_closed.
