Abschluss 1.2.1 — extracted bounded Sigma1 emitter

This package supplies an executable entry point for the extracted Rocq function `CEmitFinal_0033.emit`. It accepts a closed, well-formed bounded sentence over exact natural numbers and writes a new JDG1 proof batch. For a true sentence A it emits `tr A sid`; for a false sentence A it emits `Neg (tr A sid)`. The final theorem has an empty additional-hypothesis list.

The kernel theorem is universal over the represented language:

```text
emit_ok : EmitterOK emit
EmitterOK emit := forall A, wf 0 A -> bounded A ->
  check_batch REGP (emit A) = true /\
  exists t, last_thm (emit A) = Some t /\ t_hyps t = [] /\
            tof (t_stmt t) = stmt_of A (evb [] A).

emit_prov : forall A, wf 0 A -> bounded A ->
  prov Gam (stmt_of A (evb [] A)).
```

`Gam` is the represented theory `ZFC7 OR SepAx OR CollAx OR DefAx Dall`: the seven set-theory axioms, the Separation and Collection schemas, and the registered definition axioms. The empty theorem hypothesis list means that no additional hypothesis entries are claimed. `REGP` is the canonical initial 677 entries. Its equality with the extracted registry is checked whenever the entry point runs. The defining sources are included in `provenance/Ax.v`, `RpInit.v`, `Bridge_0033.v` and `CEmitSpec2_0033.v`.

The entry point is `runtime/emit-sentence.rkt`. Terms are exact natural numerals, `(v i)`, `(S t)`, `(+ t u)` and `(* t u)`. Formulas are `(= t u)`, `(< t u)`, `(<= t u)`, `not`, `and`, `or`, `->`, `<->`, and the bounded binders `all<`, `ex<`, `all<=`, `ex<=`. Inside a binder, `(v 0)` denotes the newest bound variable. Decimal numerals, negative numerals, free variables and unbounded existential sentences are outside this entry point's domain.

For example, from the extracted package directory:

```powershell
& 'C:\Program Files\Racket\Racket.exe' .\runtime\emit-sentence.rkt '(= 0 1)' '.\new-negative-certificate.jdg'
& 'C:\ClaudeOutput\pompetzki\pompetzki.exe' 'C:\ClaudeOutput\pompetzki\judge\judge-v3.pmp' '.\new-negative-certificate.jdg'
& 'C:\Program Files\Racket\Racket.exe' 'C:\ClaudeOutput\pompetzki\judge\racket\judge.rkt' '.\new-negative-certificate.jdg'
```

The output path must be new. `pmp` judges each emitted certificate; the Racket judge supplies an independent cross-check. The Scheme extraction, the Racket macros, the input parser and JDG text printer run outside Rocq's kernel. The entry point checks the exact final formula against `fromf (tr A sid)` or `fromf (Neg (tr A sid))`, checks the empty hypothesis list, and runs the extracted `check_batch`. These runtime checks do not replace pmp's judgment of the written certificate. The original `sigma1.rkt` generator is preserved; no equivalence theorem for that original generator's text was added.

The fresh executable controls are recorded in `judge-cli-receipt.tsv`:

| sentence | exact truth | JDG theorems / steps | pmp | Racket |
|---|---:|---:|---|---|
| `(= 0 0)` | true | 27 / 839 | ACCEPT, exit 0, 2,026 ms | ACCEPT, exit 0, 189 ms |
| `(= 0 1)` | false | 27 / 1,290 | ACCEPT, exit 0, 4,051 ms | ACCEPT, exit 0, 197 ms |

The negative certificate has SHA-256 `81dbfd1297d1e2dbde466fb09ee7e3be1d5da4e2fb949ac8d0863c6fcfd52c4a`. Its separately generated copy, its generic CLI copy and the output of a fresh source-only runtime are byte-identical. The source-only runtime used a fresh directory with no copied Racket compiled objects, completed in 5,702 ms, and is recorded in `source-runtime-check.log`.

The forged certificate changes only the final statement from `Neg (tr A sid)` to `tr A sid`, retaining the proof steps. Both judges reject it at theorem 26, step 883: pmp exit 1 in 3,754 ms; Racket exit 1 in 199 ms. Its SHA-256 is `8ebfdcc0ea371dce8192d5dcb8b437155e20a31f347126474afeedb2428c6bce`. The original negative-control acceptance and forgery rejection are recorded in `judge-negative-receipt.tsv`.

The Racket module body was compared with the copied Scheme extraction, after removing only the extraction's `(load ...)` line and adding the four-line module wrapper. Exact line equality passed (`source-binding.log`). `negative-binding.log` separately verifies the final formula, the empty hypothesis list and its JDG text.

A fresh byte-identical copy of `CEmitFinal_0033.v` was compiled as `GPTRecovery.CEmitFinal_0033`: coqc exit 0 in 631 ms. Its fresh object passed `coqchk -norec GPTRecovery.CEmitFinal_0033`, exit 0 in 439 ms. That target-only check admits the imported dependencies. The copied original full-chain check took 30m45s, exited 0 and reported `Axioms: <none>`; it is included as prior evidence in `provenance/coqchk-final-0033.log`. The fresh target check and the original full-chain receipt have separate scopes. The first fresh coqchk invocation put `-o` immediately after `-norec` and failed with `Cannot find library -o in loadpath`; its log remains beside the successful correction.

`source-object-associations.tsv` binds selected source and object hashes to their logical module names and receipts. `validator-sha256.tsv` binds the pmp executable, pmp program, Racket judge and Racket executable used for the controls. `SHA256SUMS.tsv` covers the package files. These controls exercise the executable true and false branches. The universal correspondence theorem is `emit_ok`; the finite controls do not prove a correspondence theorem for the Racket wrapper.

The CH obligations O10/O11, L2R DSEP0, generic Mathlib universes and the signed-rational source/object correspondence are outside this package's mathematical result.
