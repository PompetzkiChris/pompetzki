# Lane LCH handoff R4 FINAL (corrections and additions to HANDOFF-R4.md)

Written 20:29:44 (`date`). HANDOFF-R4.md stays valid and is left as written. This file adds one item.

## Added: layers 05 and 06 replayed in Rocq

The judge-accepted files `out10/05-coh.jdg` (Coh) and `out12/06-cmp.jdg` (Cmp) are now replayed by `Replay2.check_batch` over REGP.

- `rocq/CohB_r4.v` and `rocq/CmpB_r4.v` are written by jdg2v.rkt. `CohB-r4.v` and `CmpB-r4.v` are the same text under file names with hyphens, which Rocq cannot load as modules.
- `rocq/CohCmp_r4.v` proves:
  - `coh_reg_ok : reg_ok hypf (LAXred2.REGP ++ map ent CHB)`
  - `cmp_reg_ok : reg_ok hypf (LAXred2.REGP ++ map ent CMB)`

  So every theorem of both files, including Coh and Cmp, is derivable in Gam.
- Receipts:
  - `rocq/coqc-r4.txt`: coqc exit 0 for all three files.
  - `rocq/coqchk-6-r4.txt`: LCH.CohCmp_r4, 20:26:01–20:29:27, real 3 m 24 s, Axioms: <none>, exit 0.

```
8bbf0286157ab66916e5047129065b0f11249f88f5a30fb194deead8f7ea7a3a rocq/CohB_r4.v
166e1d8ea6da0b1f09dede7d63ba4265559d7af8b9c25f569d71e911e50b047f rocq/CmpB_r4.v
d65c2200891f2e8c83e6d432b1a2c1874067c5d77de8c55374875fa7550ae084 rocq/CohCmp_r4.v
e8f28a7e4929575659bd1c352499517864e425e03add91ba6c790f9acde4415c rocq/coqc-r4.txt
ebe979999759f20645667269efe6f4e2eaf53a4b5b728971ce112bf1693150fb rocq/coqchk-6-r4.txt
```

## Open items (unchanged from HANDOFF-R4.md)

The open premises of `LRed.goedel_L`, each an exact statement:

- O3: `prov ZFpure (psub (LAXred2.tauM Lpure) sid (LAXred2.HT 1))`. Coh and Cmp are proved. Still missing: LevExt and the pair assembly.
- O4: the same with `HT 2`. Missing: LevExt and the union assembly.
- O5: the same with `HT 3`.
- O6: the same with `HT 4`.
- O7: `prov ZFpure (rel Lpure (axf 6))`.
- O8: `LSEP Lpure` (lane L2R).
- O9: `LCOLL Lpure` (lane L2R).
- O10: `prov ZFpure (rel Lpure VLpure)`.
- O11: `prov (ZFE VLpure) (pi ch)`.

Gödel's half, Con(ZFC) → Con(ZFC + CH), is not closed. Cohen's half over the same plain CH text is closed: `AlignCH.con_zfc_con_notch_plain`, no premise. No completion claim for the independence of CH may be published.
