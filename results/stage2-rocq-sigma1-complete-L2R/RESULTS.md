# Lane L2R (Stage 2, Rocq): every true bounded sentence is derivable in Gam — results, 2026-10-09

Written 18:39 (`date`). Folder `C:\ClaudeOutput\pompetzki\lanes\L2R\`.

- **Toolchain:** Rocq 9.1.0 (Rocq Platform 2026.07.0); coqc and coqchk from
  `C:\ClaudeOutput\formalization-toolchain-20260924\tools\Rocq-Platform-2026.07.0-9.1\bin`.
- **Library:** compiled against the Cohen library `C:\ClaudeOutput\pompetzki\forcing-src\general\` (`-R … Cohen`), which
  is only read.
- **Build:** `sh build-L2R.sh`. The last run is in `build-run-1.log`.

## The theorems

```
bounded_complete
     : forall A : fm,
       bounded A ->
       wf 0 A ->
       (sat nil A -> Prov.prov Ax.Gam (tr A Prov.sid)) /\
       (~ sat nil A -> Prov.prov Ax.Gam (Syn.Neg (tr A Prov.sid)))
Closed under the global context

sigma1_complete
     : forall A : fm,
       pos A -> wf 0 A -> sat nil A -> Prov.prov Ax.Gam (tr A Prov.sid)
Closed under the global context

sigma1_all_statements
     : forall c : String.string * fm * bool * Syn.form,
       List.In c L2RCases.cases ->
       let (p, f) := c in
       let (p0, _) := p in let (_, _) := p0 in Prov.prov Ax.Gam f
Closed under the global context
```

This is the `Check` and `Print Assumptions` output (`PrintAxAll.out.txt`, `build-run-1.log`). `sigma1_bounded_statements`
states the same for the 73 bounded cases, and its assumptions are also closed.

- **bounded_complete** (`L2RSent.v`) is the task's theorem. Let A be any closed sentence without `some`. If A is true
  in ℕ, then `prov Gam [A]`. If A is false, then `prov Gam (¬[A])`.
- **sigma1_complete** (`L2RSigma1.v`) allows `some x A` (∃x ∈ ω) in positive places. `pos` lists these places: under
  and, or, the conclusion of imp, the bounded quantifiers, and `some` itself. Every other part must be bounded. A true
  sentence of this kind has `prov Gam [A]`.
- **sigma1_all_statements** (`L2RSigma1.v`) covers sigma1's sentence theorems. These are the 78 theorems in
  `out\04-bounded.jdg`, `06-sentences.jdg` and `07-sigma1.jdg` (12 + 61 + 5). Every one of their statements is
  `prov Gam`, as an instance of the two theorems above.

### What the words mean

- **`prov`, `Gam`, `form`:** from Prov.v, Ax.v and Syn.v, unchanged. Gam consists of:
  - the seven axioms of the kernel's table;
  - every Separation and Collection instance;
  - every definition of Data.v (`DefAx Dall`, in every renaming).
- **`fm`** (L2RSent.v):
  - Terms: `tnum n | tvar i | tS t | tadd t u | tmul t u`.
  - Formulas:
    - `feq flt fle` are =, <, ≤;
    - `fnot fand fdis fimp fiff` are the connectives;
    - `fall t A` is ∀x<t, `fex t A` is ∃x<t;
    - `falle t A` is ∀x≤t, `fexe t A` is ∃x≤t;
    - `fsome A` is ∃x∈ω.
  - Sentence variables are de Bruijn indices: `tvar 0` is the innermost bound variable. sigma1's sentences use named
    variables; `fm->rocq` in `agree.rkt` converts them one to one.
- **`sat e A`:** truth in ℕ with `e` as the values of the free variables. Quantifiers range over `nat`; bounded ones
  over k < t or k ≤ t.
- **`bounded A`:** A contains no `fsome`. **`wf 0 A`:** A is closed.
- **`tr A rho`:** sigma1.rkt's translation (`tr`, `wrap`, `bq-tr`, `rel-dsl`, `num`, `fin-parts`), written in de Bruijn
  form. `rho` places the sentence variables among the ZF variables; for a closed sentence it is `sid`.

```
Fixpoint wrap (t : tm) (rho : nat -> nat) (K : form) : form :=
  match t with
  | tnum n => Xf (Kf (Num n 0) K)
  | tvar i => ren (scons (rho i) sid) K
  | tS a => wrap a rho (Xf (Kf (Suc 0 1) (ren (up S) K)))
  | tadd a b => wrap a rho (wrap b (shS rho) (Xf (Kf (AddF 2 1 0) (ren (up (fun n => S (S n))) K))))
  | tmul a b => wrap a rho (wrap b (shS rho) (Xf (Kf (MulF 2 1 0) (ren (up (fun n => S (S n))) K))))
  end.
Fixpoint tr (A : fm) (rho : nat -> nat) : form :=
  match A with
  | feq t u => wrap t rho (wrap u (shS rho) (Eqv 1 0))
  | flt t u => wrap t rho (wrap u (shS rho) (Mem 1 0))
  | fle t u => wrap t rho (wrap u (shS rho) (Df (Mem 1 0) (Eqv 1 0)))
  | fnot A => Neg (tr A rho)
  | fand A B => Kf (tr A rho) (tr B rho)
  | fdis A B => Df (tr A rho) (tr B rho)
  | fimp A B => Imp (tr A rho) (tr B rho)
  | fiff A B => Qf (tr A rho) (tr B rho)
  | fall t A => wrap t rho (All (Imp (Mem 0 1) (tr A (rho2 rho))))
  | fex t A => wrap t rho (Xf (Kf (Mem 0 1) (tr A (rho2 rho))))
  | falle t A => wrap t rho (All (Imp (Df (Mem 0 1) (Eqv 0 1)) (tr A (rho2 rho))))
  | fexe t A => wrap t rho (Xf (Kf (Df (Mem 0 1) (Eqv 0 1)) (tr A (rho2 rho))))
  | fsome A => Xf (Kf (NatP 0) (tr A (scons 0 (shS rho))))
  end.
```

The formulas used in `wrap` are:

- **Numerals:** `Num 0 x` = Emp(x); `Num (n+1) x` = ∃y (Num n y ∧ Suc(x,y)).
- **`AddF`** (L2RFin.v) is sigma1's Add:
  ∃f [Fnc(f) ∧ ∀o (Emp(o) → App(f,o,x)) ∧ ∀i (i∈y → ∃a App(f,i,a)) ∧ ∀i j a b (i∈y ∧ Suc(j,i) ∧ App(f,i,a) ∧
  App(f,j,b) → Suc(b,a)) ∧ App(f,y,z)].
- **`MulF`** is sigma1's Mul: the same with App(f,o,o) at 0 and Add(a,x,b) in the step.
- **Symbols:** Emp 17, Suc 18, Opr 8, App 9, Fnc 10, Om 20, Nat 72. These are the registered definitions of Data.v.

### The Rocq `tr` is sigma1.rkt's translation: the check

- **`agree.rkt`** loads sigma1.rkt's own namespace, read only.
  - It takes every key `(Sent s)` in the three `.index.txt` listings and reads that theorem from the judged `.jdg`
    file with sigma1's `read-jdg-text` and `tof`. That gives 78 theorems, all closed (sig and hypotheses empty).
  - It writes `L2RCases.v`. Each case holds the sentence (normalized by sigma1, converted to `fm`), sigma1's truth
    value, and the statement as a `form`.
- **`L2RAgree.v`** checks by computation:
  - `all_agree`: for all 78 cases, `tr A sid` is the statement under `form_eqb`, or its negation when the sentence is
    false.
  - `bounded_cases_ok`: the 73 bounded cases are bounded and closed, and their truth value is `evb`'s.
    `evb_ok : bounded A -> (evb e A = true <-> sat e A)` connects `evb` to `sat`.
- **`L2RSigma1.v`** checks the 5 cases of 07: they are `pos`, closed, and true by `evw`. `evw` searches witnesses
  below 20; `evw_ok` proves it sound for `sat`.
- **`L2RAgreeMut.v`** shows the comparison discriminates. It rejects all 78 cases with the truth value flipped and all
  78 cases paired with the next case's sentence: 156 of 156 mutants rejected.
- This checks the translation on the 78 emitted sentences only. The Racket function is not formalized; the theorems
  are about the Rocq `tr`.

## The proof

| file | lines | lemmas | content |
|---|---:|---:|---|
| L2RLogic.v | 353 | 70 | Natural deduction over contexts: `D G f` = `prov Gam (cj G → f)`. Rules: hypothesis, mp, deduction theorem, ∀-intro under the shifted context, instantiation, ∃-intro, ∃-elim, Leibniz. Tautologies through `Kal.taut_prov`. 13 replay facts, the unfoldings of Emp1, Suc2, App3, Fnc1, and ∃x Emp(x) from Infinity. |
| L2RArith.v | 196 | 40 | NumEx, NumUq, MemChar (N_n(y) → (x∈y ↔ N_0(x) ∨ … ∨ N_(n−1)(x))), NumIn, NumNotIn, NumNe, NumDist, each for every n and k. |
| L2RFin.v | 531 | 64 | Add and Mul in one proof, with a parameter for the kind. FinVal gives the value at every i ≤ y, by induction on i. FinExt builds the finite function: it adjoins one pair (y′, z′) at a time with AddEx, OprEx, SucEx. Results: AddChar, N_a(x) ∧ N_b(y) → (Add(x,y,z) ↔ N_(a+b)(z)); MulChar, N_a(x) ∧ N_b(y) → (Mul(x,y,z) ↔ N_(b·a)(z)). |
| L2RSent.v | 426 | 22 | Syntax, `sat`, decidability of bounded truth, `tr`. WrapPos and WrapNeg: [t](K) is proved (refuted) once K is proved (refuted) for a fresh variable with N_(value of t). `main` by induction on A, then `bounded_complete`. |
| L2RCases.v | 322 | — | The 78 cases, written by agree.rkt. |
| L2RAgree.v | 131 | 10 | evb, boundedb, wfb and their soundness; the agreement; `sigma1_bounded_statements`. |
| L2RSigma1.v | 203 | 16 | NatNum (N_n(x) → Nat(x)) from OmEx, ZeroW, SucW; `pos`; `sigma1_complete`; `sigma1_all_statements`. |
| L2RAgreeMut.v | 23 | 3 | The 156 mutants. |
| agree.rkt | 94 | — | Racket, exact integers; writes L2RCases.v. |
| build-L2R.sh | 19 | — | coqc of the 8 files, Print Assumptions, coqchk. |

Total: 2,185 lines of Rocq in 8 files, 225 lemmas and theorems.

- **Replay facts used.** Each comes from `RpFinal.entry_is_prov` and is checked by `vm_compute` against the registry
  REGF of the verified replay. Registry indices:

  | fact | index | fact | index | fact | index |
  |---|---:|---|---:|---|---:|
  | OprEx | 712 | NoTwo | 732 | ZeroW | 740 |
  | Kur1 | 720 | SucUq | 733 | SucW | 741 |
  | Kur2 | 721 | SucInj | 734 | SucEx | 974 |
  | FncApp | 722 | MemApp | 737 | AddEx | 1062 |
  | NoSelf | 731 | EmpUq | 739 | OmEx | 1108 |

  Definitions enter through `Expand.defax_prov`; axiom 4 (Infinity) through `p_ax`.
- **Structure against sigma1.rkt.**
  - sigma1 works in the frame context Chain(N), where the variables v_0..v_N are the numerals, and removes the chain
    at the end.
  - Here every free variable carries its own hypothesis N_n(v) (`Env`). At each bounded quantifier and each term,
    NumEx introduces a fresh variable with N_k. There is no chain, so there is no chain elimination.
  - The lemma families are sigma1's, each quantified over n, k and the variables:
    - NumEx, NumUq, MemChar;
    - In as NumIn, NotIn as NumNotIn, Ne as NumNe;
    - FinEx as FinExt with AddExist/MulExist;
    - FinUq as FinVal with NumUq.

## Check output

- **coqc:** all 8 files compile; the times are in the next section.
- **Print Assumptions:** `bounded_complete`, `sigma1_complete`, `sigma1_bounded_statements` and
  `sigma1_all_statements` each give `Closed under the global context` (4 of 4).
- **coqchk** (`coqchk -silent -o -R …general Cohen -R …L2R L2R …`), three runs:

  | target | files covered | run | time | log | verdict |
  |---|---|---|---:|---|---|
  | L2R.L2RSent | L2RLogic, L2RArith, L2RFin, L2RSent, the Cohen chain through RpFinal | 18:13–18:23 | 9 min 44 s | `coqchk.log` | Axioms: \<none\>, exit 0 |
  | L2R.L2RSigma1 | all lane files except L2RAgreeMut | 18:18:37–18:28:36 | 9 min 59 s | `coqchk-all.log` | Axioms: \<none\>, exit 0 |
  | L2R.L2RSigma1 | the same, after the clean rebuild | in `build-run-1.log` | 575 s | `build-run-1.log` | Axioms: \<none\>, exit 0 |

  Every run reports: Set predicative, no rewrite rules, no type-in-type, no unsafe (co)fixpoints, no assumed
  positivity. L2RAgreeMut contains only computation checks and is compiled by coqc, not by coqchk.

## Files (sha256)

The `.vo` hashes are those of the clean rebuild (`build-run-1.log`, 18:28:56–18:39:11), the files its coqchk checked.

```
05cd24c699624645a7df33483805d879cac934520346dcb1ef6d012ed7eb5466  L2RLogic.v
58b823af2a411bd2ff5f5f0c5ebfe58690f016789e6d6c370d7306e65cbafe94  L2RArith.v
08ed2af474d547226e3a9e217462c986f87f3d4d378f7de36e1fa6887e276c40  L2RFin.v
4efa90a3fbb4dd1f4b9018c5d6a249acd04e57a373696058a8a74baad56ba11a  L2RSent.v
cedae7461ae0c5d680d3e8de4258015676c343fc56caf2a531f064f376787f87  L2RCases.v
2c76f360ebe79bad00d986ea8e35818d49bde21bdc15051abae38903acb3ea70  L2RAgree.v
40b3d2e6dc7d65dde6daca6ec089e10a86f628335129f0631d446210725b8afd  L2RSigma1.v
7f3bae575eb353793872a867cd6da1f475033a905ee53fc0874bb13205a6a756  L2RAgreeMut.v
01ed0ee85df351d6fc2132cff2857ad8bb868dd633eacd7014e762b9a7f57203  agree.rkt
1556566d5e263d0748c00e2102aa6996d49c237278e0ab79ddf91d7ba71d6de6  build-L2R.sh
a97580e2e400921ade55fd231612e68f869133d584083df9143a3a7b9c49295b  PrintAxAll.v
f341e7c2bfb72da90902311479c90d160a6d4cd054fcf2040b22c20a9ad7f84e  L2RLogic.vo
67d819723456a40aafbb951582acd1dd006164d7371ca585a630b1554c0430b2  L2RArith.vo
bcd0d511e4f1fb0b915827b033aa58799dc65cb2a25a4d17ca11d40d4d0d6b56  L2RFin.vo
d90a5135550516dfe8c3234091f071878f409d2b1b2674654f6eeea4cae44105  L2RSent.vo
0f5116648a162ce8f933dbc5436f759526b5d41abd924bb7d279ff9a0327feaa  L2RCases.vo
b08231dab86bfb477be5357ed8944d53428bad5fccc030c619360eb9ae18dfd3  L2RAgree.vo
7132dfb56d6104fe58c6780e13e7bd86bd0b6194e6e58bfaac27a06a977edd24  L2RSigma1.vo
cd4ee1af17071e56622e9a8a5b7e62a9d0d6e78ce8fcdc7becfdea176034501e  L2RAgreeMut.vo
```

## Times (`date`)

- **17:28:28** orders read.
- **17:39** L2RLogic.v first compiles.
- **18:02** L2RFin.v complete: AddChar, MulChar.
- **18:12** L2RSent.v complete: `bounded_complete`.
- **18:14:51** agree.rkt writes L2RCases.v (2.8 s).
- **18:17** L2RAgree.v and L2RSigma1.v complete.
- **Clean rebuild** (`build-run-1.log`), 18:28:56 to 18:39:11. coqc time per file:

  | L2RLogic | L2RArith | L2RFin | L2RSent | L2RCases | L2RAgree | L2RSigma1 | L2RAgreeMut |
  |---:|---:|---:|---:|---:|---:|---:|---:|
  | 2 s | 1 s | 6 s | 3 s | 2 s | 1 s | 1 s | 1 s |

  coqchk then took 575 s.

## Not done

- **False sentences with `some`:** not claimed. Their negations are Π₁.
- **Agreement with the Racket `tr`:** checked on the 78 emitted sentences, not proved for all sentences.
- **JDG1 output:** this lane produces none. The result is a Rocq theorem about `prov Gam`, not a posting for the
  judges.

## A mistake of this lane

- **What:** at 18:12 three files were written into `C:\ClaudeOutput\pompetzki\sigma1\out\`, a folder this lane does
  not touch:
  - `PrintAx.v` (93 bytes, three Rocq lines importing L2RSent);
  - `PrintAx.glob`;
  - `.PrintAx.aux`.
- **Cause:** two shell calls run in parallel shared a working directory.
- **State:** they are left where they are. sigma1's `.jdg`, `.index.txt` and `manifest.txt` there were not changed;
  their times are 16:36–16:37.
