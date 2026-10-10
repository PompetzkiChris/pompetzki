# Lane L2D: derived rules as JDG1 emitters — results, 2026-10-09

Written 20:45 (`date`). Everything here is Racket v9.3 [cs] with exact integers. All emitters are untrusted: each derivation counts only through the verdicts of the two judges, run from `C:\ClaudeOutput\pompetzki\judge\`:
- `pompetzki.exe judge-v3.pmp FILE`
- `racket racket\judge.rkt FILE`

The registry of every file is the first 677 entries of `replay-all.jdg` (`AX0 ++ DEF0` of `RpInit.v`), checked entry by entry against the Rocq source by sigma1's `check-registry` for every file; no entry carries hypotheses. Every theorem claims hypotheses `[]`, so by `Replay3.check_batch_ok` an accepted statement S has `prov Gam (tof S)`.

## Result

| format | emitter | statement derived | accepted files |
|---|---|---|---|
| LRAT | `lrat-v4.rkt` | the bounded sentence "all x1<2 … all xn<2 not (C1 and … and Cm)" in sigma1's language and translation | 11 (6 own, 5 AG5 cadical) |
| Smith normal form | `certs-v2.rkt` | A V = W, U W = D, U U' = I, V V' = I, d_i \| d_(i+1), as identities of binary numerals | 4 (3 own, 1 L8A) |
| rank–nullity over Q | `certs-v2.rkt`, `certs-v3.rkt` | M adj(M) = det(M) I, det(M) ≠ 0, A K = 0, K2 adj(K2) = det(K2) I, det(K2) ≠ 0 | 6 (5 own, 1 L8A) |
| Pratt | `certs-v2.rkt` | the arithmetic checks of the certificate (product chain for p − 1, modular powers with explicit quotients and residues, 1 < r < p) | 3 |
| Farkas | `farkas-v3.rkt` | the system A x ≤ b has no rational solution | 3 (f1-1d, f4-2d, G2 cyclic-k02); f3-2d and f2-2d: pmp LIMIT (memory block), Racket ACCEPT |

originals: 19 × pmp ACCEPT / Racket ACCEPT. Mutants: 186 × pmp REJECT / Racket REJECT; both judges name the same theorem and step in 186 of 186.

## What the theorems state

### LRAT (`lrat-v4.rkt`)
- Input: a DIMACS CNF F over x1..xn and an LRAT refutation (RUP steps; RAT hints are refused).
- Statement: S = all x1<2 … all xn<2 not (C1 and … and Cm), literal xi as (xi = 1), −xi as not (xi = 1), the conjunction parenthesised as a balanced tree. The translation is sigma1's `tr`; the theorem is [S].
- Derivation: one T step per LRAT hint. The clauses enter as opaque atoms: B_j = all z C'_j (vacuous), W = all z (B_1 & … & B_m), e_i = (p_i = v1). Every hint step proves W → (L or u) for the unit u it propagates, and W → L at the conflict. No truth table over the 2^n assignments is built. The empty clause gives W → not (0 = 0), then not (B_1 & … & B_m), then the conversion to the atoms [x_i = 1] of the translation, then the n bounded quantifiers (H, E with witness v2, NumEx(2)), then chain elimination.
- Length: linear in the number of hints, each step of size O(m) (the CNF in W).

### Integers: binary numerals over ω (`kernel*.rkt`, `bin-v6.rkt`)
- Frame of every arithmetic theorem: w, p, g, o with Ctx = Om(w) & Pr(p,w,w) & CapS(g,p,w) & Emp(o). g is the successor function on w (replay theorems 127–131), o is zero.
- Addition and multiplication come from the replay's recursion theorem (replay 95) and its uniqueness (replay 133):
  - Ad(x,y,z) := exists a (Rec(a,w,g,w,x) & App(a,y,z)), z = x + y;
  - Mu(x,y,z) := exists m exists a ((Rec(a,w,g,w,x) & Rec(m,w,a,w,o)) & App(m,y,z)), z = x · y, with x · S(y) = x + x · y.
- Numerals, one existential per bit:
  - Bin_0(x) := Emp(x), Bin_1(x) := Suc(x,o);
  - Bin_2m(x) := exists y (Bin_m(y) & Ad(y,y,x));
  - Bin_2m+1(x) := exists y (Bin_m(y) & exists t (Ad(y,y,t) & Suc(x,t))).
- General lemmas, proved once per file, by induction through replay 88 (`kernel-v6`, `kernel2-v2`, `kernel3-v4`, `kernel4-v5`):
  - existence, uniqueness and range of Ad and Mu;
  - x + 0 = x and x + S(y) = S(x + y); 0 + y = y and S(x) + y = S(x + y);
  - commutativity and associativity of +; x · 0 = 0, x · S(y) = x + x · y, 0 · z = 0;
  - x(y + z) = xy + xz and (a + b)z = az + bz; x(yz) = (xy)z;
  - (x + y) + (u + v) = (x + u) + (y + v); cancellation; Suc injective; a + b = 0 → a = 0; e ≥ 1, x ≠ 0 → e x ≠ 0.
- Numeral lemmas, generated per number: BinW, BinEx, BinUq, BinPos, BinInc, BinAdd (O(bits) lemmas), BinMul (O(bits²)), and the checks CAdd, CMul, CNZ.
- The kernel alone (`kernel-test/kernel-all-1.jdg`, 70 theorems, 2,331 steps): both judges ACCEPT (pmp 36.9 s, Racket 0.5 s).

### Certificate theorems (`cert-v1.rkt`, `certs-v2.rkt`)
- Each certificate theorem is closed: forall w p g o (Ctx → E_1 & … & E_M), a balanced conjunction of entries.
- An entry `(Lin terms c)` states the integer identity Σ s_k a_k b_k = c over binary numerals:
  - forall u_k v_k e (Bin hypotheses → exists products and partial sums (Mu(u_k,v_k,t_k) & … & Ad(…) & … & P = N));
  - P collects the positive products (and |c| if c < 0), N the negative ones (and c if c > 0); zero products are left out.
  - Entries `(CMul a b)`, `(CAdd a b)`, `(CNZ n)` are the numeral lemmas a·b = c, a + b = c, n ≠ 0.
- Smith: for U A V = D the entries are A V = W, U W = D, U U' = I, V V' = I (W, U', V' computed by the emitter and printed in the manifest), and d_(i+1) = d_i k_i.
- Rank: for rank A = r over Q, the minor M = A[I,J] with M adj(M) = det(M) I and det(M) ≠ 0 gives rank ≥ r. The kernel basis K with A K = 0 and an invertible (n−r)-minor K2 (K2 adj(K2) = det(K2) I, det(K2) ≠ 0) gives nullity ≥ n − r. That rank = r follows from these is the rank–nullity theorem, used outside ZF; the ZF theorem is the conjunction of the identities.
- Pratt: the theorem is the conjunction of the certificate's checks for p and recursively for every prime factor q > 2 of p − 1:
  - p − 1 = Π q^e as a chain of products, and 1 + (p − 1) = p;
  - a^(p−1) mod p = 1 and a^((p−1)/q) mod p = r with 1 + r' = r, r' ≠ 0, r + (p − r) = p, p − r ≠ 0. Each square and multiply is written as x·x = s, Q·p = t, t + x' = s, x' + (p − x') = p, p − x' ≠ 0.
  - "p is prime" follows from these by Lucas' theorem. Lucas' theorem (or Pocklington's) is not derived in ZF here, so primality itself is not a theorem of these files. The derivations do not divide by trial.

### Farkas (`farkas-v3.rkt`, `forms-v2.rkt`, `forms2-v2.rkt`)
- Input: an integer system A x ≤ b (m rows, n unknowns) and y ≥ 0 with yᵀA = 0, yᵀb < 0.
- Encoding: x_j = (u_j − v_j)/w with u_j, v_j, w ∈ ω, w ≠ 0. Row i times w, negative terms moved across: L_i(z) + d_i = R_i(z) with d_i ∈ ω, z = (u, v, w).
- Statement: forall w p g o (Ctx → forall coefficient numerals (Bin hypotheses → forall z (z ∈ w → not Emp(w_var) → not (Row_1 & … & Row_m)))). Here Row_i = exists l r d (FormV(L_i, z, l) & FormV(R_i, z, r) & d ∈ w & Ad(l, d, r)) and FormV is the full linear form Σ_j c_j z_j.
- Proof:
  - scale each row by y_i (FScale, distributivity) and add the rows (FAdd, KX4);
  - yᵀA = 0 makes the totals agree in every coefficient but w's, where the left exceeds the right by δ = −yᵀb ≥ 1;
  - FUnit, FAdd and FFun give Lt = Rt + δw;
  - with Lt + D = Rt, associativity, commutativity and cancellation give δw + D = 0, so Emp(δw) (KZeroSum), against KMulNZ.
- The linear-form lemmas are general in the coefficients (symbolic variables); only the coefficient arithmetic goes through the numeral lemmas.

## The pmp judge's nesting limit
- `pompetzki.asm` reserves `MAXRET equ 256` gosub frames, and judge-v3.pmp recurses once per formula level.
- Probe files (`probe/`, `tools/depth-probe-v1.rkt`):
  - nested quantifiers pass at 240 levels;
  - nested negations pass at 240 and fail at 320 ("gosub: too deep");
  - left-nested conjunctions pass at 120 and fail at 160 conjuncts.
- The first LRAT version (`lrat-v3.rkt`) nested the clause conjunction to the left. pmp stopped with "gosub: too deep" on php5-4, rand14-80 and rand20-120, while the Racket judge accepted them. `lrat-v4.rkt` uses balanced trees: its deepest formula is 201 levels, and pmp accepts all six files.
- `tools/maxdepth-v1.rkt` measures the depth of every file: the Farkas files reach 151 levels, Pratt 23 reaches 83.

## Judge results

### LRAT
| file | theorems | steps | bytes | pmp | pmp time | Racket | Racket time |
|---|---:|---:|---:|---|---:|---|---:|
| php5-4.jdg | 12 | 1645 | 1767850 | ACCEPT, exit 0 | 93.6 s | ACCEPT, exit 0 | 1.0 s |
| php3-2.jdg | 12 | 289 | 105712 | ACCEPT, exit 0 | 4.0 s | ACCEPT, exit 0 | 0.7 s |
| php4-3.jdg | 12 | 536 | 301261 | ACCEPT, exit 0 | 14.1 s | ACCEPT, exit 0 | 0.4 s |
| rand14-80.jdg | 12 | 883 | 1275284 | ACCEPT, exit 0 | 149.8 s | ACCEPT, exit 0 | 0.7 s |
| rand10-60.jdg | 12 | 699 | 763072 | ACCEPT, exit 0 | 77.6 s | ACCEPT, exit 0 | 0.7 s |
| rand20-120.jdg | 12 | 1467 | 3485854 | ACCEPT, exit 0 | 436.1 s | ACCEPT, exit 0 | 1.9 s |


Instances (`tools/lrat-gen-v2.rkt`, DPLL with decision-clause learning; seeds in the commands below):

| file | variables | clauses | LRAT steps | hints |
|---|---:|---:|---:|---:|
| php3-2 (pigeonhole 3→2) | 6 | 9 | 2 | 13 |
| php4-3 | 12 | 22 | 9 | 104 |
| php5-4 | 20 | 45 | 52 | 971 |
| rand10-60 (random 3-CNF) | 10 | 60 | 7 | 65 |
| rand14-80 | 14 | 80 | 8 | 77 |
| rand20-120 | 20 | 120 | 24 | 343 |

| mutant | pmp | Racket | pmp: theorem step | Racket: theorem step | same |
|---|---|---|---|---|---|
| php3-2-cnf-flip.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 162 | 11 162 | yes |
| php3-2-conflict-drop.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 32 | 11 32 | yes |
| php3-2-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 161 | 11 161 | yes |
| php3-2-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 5 | 5 5 | yes |
| php3-2-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 1 | 1 1 | yes |
| php3-2-input-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 2 | 11 2 | yes |
| php3-2-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 1 | 5 1 | yes |
| php3-2-mp-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 10 8 | 10 8 | yes |
| php3-2-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 162 | 11 162 | yes |
| php3-2-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 7 | 4 7 | yes |
| php3-2-rup-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 20 | 11 20 | yes |
| php3-2-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0 | 0 0 | yes |
| php3-2-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 162 | 11 162 | yes |
| php3-2-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 0 | 1 0 | yes |
| php4-3-cnf-flip.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 409 | 11 409 | yes |
| php4-3-conflict-drop.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 149 | 11 149 | yes |
| php4-3-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 408 | 11 408 | yes |
| php4-3-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 5 | 5 5 | yes |
| php4-3-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 1 | 1 1 | yes |
| php4-3-input-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 2 | 11 2 | yes |
| php4-3-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 1 | 5 1 | yes |
| php4-3-mp-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 10 8 | 10 8 | yes |
| php4-3-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 409 | 11 409 | yes |
| php4-3-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 7 | 4 7 | yes |
| php4-3-rup-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 46 | 11 46 | yes |
| php4-3-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0 | 0 0 | yes |
| php4-3-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 409 | 11 409 | yes |
| php4-3-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 0 | 1 0 | yes |
| php5-4-cnf-flip.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 1518 | 11 1518 | yes |
| php5-4-conflict-drop.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 1062 | 11 1062 | yes |
| php5-4-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 1517 | 11 1517 | yes |
| php5-4-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 5 | 5 5 | yes |
| php5-4-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 1 | 1 1 | yes |
| php5-4-input-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 2 | 11 2 | yes |
| php5-4-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 1 | 5 1 | yes |
| php5-4-mp-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 10 8 | 10 8 | yes |
| php5-4-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 1518 | 11 1518 | yes |
| php5-4-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 7 | 4 7 | yes |
| php5-4-rup-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 92 | 11 92 | yes |
| php5-4-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0 | 0 0 | yes |
| php5-4-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 1518 | 11 1518 | yes |
| php5-4-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 0 | 1 0 | yes |
| rand10-60-cnf-flip.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 572 | 11 572 | yes |
| rand10-60-conflict-drop.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 186 | 11 186 | yes |
| rand10-60-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 571 | 11 571 | yes |
| rand10-60-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 5 | 5 5 | yes |
| rand10-60-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 1 | 1 1 | yes |
| rand10-60-input-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 2 | 11 2 | yes |
| rand10-60-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 1 | 5 1 | yes |
| rand10-60-mp-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 10 8 | 10 8 | yes |
| rand10-60-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 572 | 11 572 | yes |
| rand10-60-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 7 | 4 7 | yes |
| rand10-60-rup-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 122 | 11 122 | yes |
| rand10-60-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0 | 0 0 | yes |
| rand10-60-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 572 | 11 572 | yes |
| rand10-60-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 0 | 1 0 | yes |
| rand14-80-cnf-flip.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 756 | 11 756 | yes |
| rand14-80-conflict-drop.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 238 | 11 238 | yes |
| rand14-80-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 755 | 11 755 | yes |
| rand14-80-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 5 | 5 5 | yes |
| rand14-80-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 1 | 1 1 | yes |
| rand14-80-input-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 2 | 11 2 | yes |
| rand14-80-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 1 | 5 1 | yes |
| rand14-80-mp-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 10 8 | 10 8 | yes |
| rand14-80-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 756 | 11 756 | yes |
| rand14-80-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 7 | 4 7 | yes |
| rand14-80-rup-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 162 | 11 162 | yes |
| rand14-80-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0 | 0 0 | yes |
| rand14-80-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 756 | 11 756 | yes |
| rand14-80-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 0 | 1 0 | yes |
| rand20-120-cnf-flip.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 1340 | 11 1340 | yes |
| rand20-120-conflict-drop.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 584 | 11 584 | yes |
| rand20-120-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 1339 | 11 1339 | yes |
| rand20-120-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 5 | 5 5 | yes |
| rand20-120-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 1 1 | 1 1 | yes |
| rand20-120-input-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 2 | 11 2 | yes |
| rand20-120-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 1 | 5 1 | yes |
| rand20-120-mp-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 10 8 | 10 8 | yes |


### Smith, rank, Pratt
| file | theorems | steps | bytes | pmp | pmp time | Racket | Racket time |
|---|---:|---:|---:|---|---:|---|---:|
| smith-2x2.jdg | 135 | 4764 | 1309264 | ACCEPT, exit 0 | 95.9 s | ACCEPT, exit 0 | 1.1 s |
| smith-2x3.jdg | 143 | 5311 | 1531037 | ACCEPT, exit 0 | 118.4 s | ACCEPT, exit 0 | 0.8 s |
| smith-3x3.jdg | 240 | 10029 | 4088896 | ACCEPT, exit 0 | 282.7 s | ACCEPT, exit 0 | 1.4 s |
| rank-3x3.jdg | 117 | 3926 | 901306 | ACCEPT, exit 0 | 69.0 s | ACCEPT, exit 0 | 0.8 s |
| rank-3x4.jdg | 98 | 3209 | 683079 | ACCEPT, exit 0 | 54.7 s | ACCEPT, exit 0 | 0.8 s |
| pratt-7.jdg | 174 | 6715 | 2201449 | ACCEPT, exit 0 | 152.6 s | ACCEPT, exit 0 | 1.1 s |
| pratt-13.jdg | 238 | 9666 | 4116583 | ACCEPT, exit 0 | 259.9 s | ACCEPT, exit 0 | 1.4 s |
| pratt-23.jdg | 418 | 18821 | 10569557 | ACCEPT, exit 0 | 655.1 s | ACCEPT, exit 0 | 2.6 s |
| rank-2x3.jdg | 120 | 4127 | 977952 | ACCEPT, exit 0 | 80.6 s | ACCEPT, exit 0 | 0.7 s |
| rank-4x4.jdg | 77 | 2028 | 262097 | ACCEPT, exit 0 | 18.5 s | ACCEPT, exit 0 | 0.5 s |
| rank-2x2.jdg | 113 | 3959 | 975471 | ACCEPT, exit 0 | 74.9 s | ACCEPT, exit 0 | 1.2 s |


Certificates (`certs/in/`, made by `tools/certgen-v1.rkt`; the entries are listed in each `.manifest.txt`):
- smith-2x2: A = ((2 4) (6 8)), D = diag(2, 4).
- smith-2x3: A = ((1 2 3) (4 5 6)), D = diag(1, 3).
- smith-3x3: A = ((2 4 4) (−6 6 12) (10 −4 −16)), D = diag(2, 6, 12).
- rank-3x3: A = ((1 2 3) (2 4 6) (1 0 1)), rank 2.
- rank-3x4: A = ((1 2 0 1) (0 1 1 0) (1 3 1 1)), rank 2.
- rank-2x3: A = ((2 4 6) (1 2 3)), rank 1; rank-4x4: A = ((1 1 0 0) (0 0 1 1) (1 1 1 1) (2 2 1 1)), rank 2; rank-2x2: A = ((2 1) (1 3)), full rank, no kernel vectors (`certs-v3.rkt`, files in `certs/out3/`).
- pratt-7, pratt-13, pratt-23 (with the certificates of 3, 11, 5).

| mutant | pmp | Racket | pmp: theorem step | Racket: theorem step | same |
|---|---|---|---|---|---|
| smith-2x2-cert-use-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 134 1 | 134 1 | yes |
| smith-2x2-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 134 44 | 134 44 | yes |
| smith-2x2-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 6 | 3 6 | yes |
| smith-2x2-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 3 | 3 3 | yes |
| smith-2x2-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 63 21 | 63 21 | yes |
| smith-2x2-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 134 45 | 134 45 | yes |
| smith-2x2-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 23 | 2 23 | yes |
| smith-2x2-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 1 | 3 1 | yes |
| smith-2x2-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 134 45 | 134 45 | yes |
| smith-2x2-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 0 | 3 0 | yes |
| smith-2x3-cert-use-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 142 1 | 142 1 | yes |
| smith-2x3-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 142 59 | 142 59 | yes |
| smith-2x3-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 6 | 3 6 | yes |
| smith-2x3-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 3 | 3 3 | yes |
| smith-2x3-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 59 21 | 59 21 | yes |
| smith-2x3-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 142 60 | 142 60 | yes |
| smith-2x3-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 23 | 2 23 | yes |
| smith-2x3-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 1 | 3 1 | yes |
| smith-2x3-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 142 60 | 142 60 | yes |
| smith-2x3-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 0 | 3 0 | yes |
| smith-3x3-cert-use-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 239 1 | 239 1 | yes |
| smith-3x3-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 239 92 | 239 92 | yes |
| smith-3x3-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 6 | 3 6 | yes |
| smith-3x3-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 3 | 3 3 | yes |
| smith-3x3-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 63 21 | 63 21 | yes |
| smith-3x3-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 239 93 | 239 93 | yes |
| smith-3x3-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 23 | 2 23 | yes |
| smith-3x3-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 1 | 3 1 | yes |
| smith-3x3-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 239 93 | 239 93 | yes |
| smith-3x3-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 0 | 3 0 | yes |
| pratt-13-cert-use-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 237 1 | 237 1 | yes |
| pratt-13-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 237 95 | 237 95 | yes |
| pratt-13-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 21 | 0 21 | yes |
| pratt-13-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 51 28 | 51 28 | yes |
| pratt-13-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 59 21 | 59 21 | yes |
| pratt-13-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 237 96 | 237 96 | yes |
| pratt-13-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 23 7 | 23 7 | yes |
| pratt-13-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0 | 0 0 | yes |
| pratt-13-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 237 96 | 237 96 | yes |
| pratt-13-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 4 | 0 4 | yes |
| pratt-7-cert-use-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 173 1 | 173 1 | yes |
| pratt-7-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 173 71 | 173 71 | yes |
| pratt-7-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 21 | 0 21 | yes |
| pratt-7-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 52 28 | 52 28 | yes |
| pratt-7-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 60 21 | 60 21 | yes |
| pratt-7-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 173 72 | 173 72 | yes |
| pratt-7-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 7 | 2 7 | yes |
| pratt-7-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0 | 0 0 | yes |
| pratt-7-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 173 72 | 173 72 | yes |
| pratt-7-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 4 | 0 4 | yes |
| rank-3x3-cert-use-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 116 1 | 116 1 | yes |
| rank-3x3-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 116 29 | 116 29 | yes |
| rank-3x3-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 6 | 3 6 | yes |
| rank-3x3-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 3 | 3 3 | yes |
| rank-3x3-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 63 21 | 63 21 | yes |
| rank-3x3-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 116 30 | 116 30 | yes |
| rank-3x3-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 23 | 2 23 | yes |
| rank-3x3-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 1 | 3 1 | yes |
| rank-3x3-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 116 30 | 116 30 | yes |
| rank-3x3-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 0 | 3 0 | yes |
| rank-3x4-cert-use-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 97 1 | 97 1 | yes |
| rank-3x4-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 97 38 | 97 38 | yes |
| rank-3x4-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 6 | 3 6 | yes |
| rank-3x4-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 3 | 3 3 | yes |
| rank-3x4-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 59 21 | 59 21 | yes |
| rank-3x4-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 97 39 | 97 39 | yes |
| rank-3x4-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 23 | 2 23 | yes |
| rank-3x4-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 1 | 3 1 | yes |
| rank-3x4-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 97 39 | 97 39 | yes |
| rank-3x4-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 0 | 3 0 | yes |
| pratt-23-cert-use-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 417 1 | 417 1 | yes |
| pratt-23-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 417 167 | 417 167 | yes |
| pratt-23-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 21 | 0 21 | yes |
| pratt-23-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 52 28 | 52 28 | yes |
| pratt-23-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 61 21 | 61 21 | yes |
| pratt-23-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 417 168 | 417 168 | yes |
| pratt-23-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 7 | 2 7 | yes |
| pratt-23-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 0 | 0 0 | yes |
| pratt-23-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 417 168 | 417 168 | yes |
| pratt-23-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 0 4 | 0 4 | yes |
| rank-2x2-cert-use-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 112 1 | 112 1 | yes |
| rank-2x2-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 112 17 | 112 17 | yes |
| rank-2x2-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 6 | 3 6 | yes |
| rank-2x2-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 3 | 3 3 | yes |
| rank-2x2-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 65 21 | 65 21 | yes |
| rank-2x2-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 112 18 | 112 18 | yes |
| rank-2x2-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 23 | 2 23 | yes |
| rank-2x2-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 1 | 3 1 | yes |
| rank-2x2-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 112 18 | 112 18 | yes |
| rank-2x2-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 0 | 3 0 | yes |
| rank-2x3-cert-use-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 119 1 | 119 1 | yes |
| rank-2x3-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 119 29 | 119 29 | yes |
| rank-2x3-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 6 | 3 6 | yes |
| rank-2x3-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 3 | 3 3 | yes |
| rank-2x3-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 63 21 | 63 21 | yes |
| rank-2x3-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 119 30 | 119 30 | yes |
| rank-2x3-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 23 | 2 23 | yes |
| rank-2x3-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 1 | 3 1 | yes |
| rank-2x3-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 119 30 | 119 30 | yes |
| rank-2x3-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 0 | 3 0 | yes |
| rank-4x4-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 76 38 | 76 38 | yes |
| rank-4x4-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 6 | 3 6 | yes |
| rank-4x4-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 3 | 3 3 | yes |


### Farkas
| file | theorems | steps | bytes | pmp | pmp time | Racket | Racket time |
|---|---:|---:|---:|---|---:|---|---:|
| f1-1d.jdg | 106 | 5069 | 4445723 | ACCEPT, exit 0 | 344.5 s | ACCEPT, exit 0 | 1.3 s |
| f4-2d.jdg | 117 | 6162 | 10989088 | ACCEPT, exit 0 | 825.4 s | ACCEPT, exit 0 | 3.2 s |


Systems (`farkas/in/`):
- f1-1d: x ≤ 1, −x ≤ −2; y = (1, 1).
- f4-2d: 3x − 2y ≤ 1, −3x + 2y ≤ −2; y = (1, 1).
- f3-2d: x + y ≤ 1, −x ≤ −1, −y ≤ −1; y = (1, 1, 1).
- f2-2d: 2x + y ≤ 3, −x ≤ −1, −y ≤ −2; y = (1, 2, 1).

| mutant | pmp | Racket | pmp: theorem step | Racket: theorem step | same |
|---|---|---|---|---|---|
| f1-1d-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 105 809 | 105 809 | yes |
| f1-1d-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 5 21 | 5 21 | yes |
| f1-1d-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 52 28 | 52 28 | yes |
| f1-1d-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 59 21 | 59 21 | yes |
| f1-1d-main-last-taut-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 105 803 | 105 803 | yes |


## Mutants
- core-v1's generic mutants (sigma1's set):
  - the final statement negated or replaced by a false twin;
  - a T goal negated;
  - M premises swapped;
  - a U index shifted;
  - Leibniz's equation reversed;
  - an E witness or L variable shifted;
  - the last step dropped;
  - the registry's Suc definition altered.
- LRAT also gets:
  - input-goal-neg and rup-goal-neg: a hint step claims the negation;
  - conflict-drop: the empty-clause step loses a premise;
  - cnf-flip: the statement's CNF has one literal negated.
- Certificates also get cert-use-swap: the certificate theorem cites the wrong entry lemma.
- Farkas also gets main-last-taut-neg and main-mid-taut-drop, in the main theorem.

## Size and length
- LRAT: steps = 101 (prelude) + 4n + 6m + hints + O(n); the bytes grow with hints × m, from W in every hint step.
- Numerals: one multiplication check (CMul a b) costs, beyond the kernel:
  - 1,745 steps for 13·11;
  - 2,655 steps for 100·97;
  - 11,456 steps and 14 MB for 1000·999.
  - The length is O(bits²), but the formulas carry the numerals in every context, so the certificates here use small numbers.
- Farkas: O(m) row operations, each O(N) lemma applications with N = 2n + 1; the files are 4–18 MB.

## Not done
- **Pratt.** Primality is not derived; the files derive the certificate's checks. Missing: Lucas' (or Pocklington's) theorem in ZF, which needs divisibility, orders and Fermat's little theorem on ω.
- **Two definitions of + and ·.** The kernel's Ad/Mu (recursion theorem) and sigma1's Add/Mul (finite functions) are not yet proved equivalent. Lane L7 proved the laws for sigma1's definitions. The LRAT statement uses sigma1's language directly; the arithmetic statements use Ad/Mu.
- **Rank of full rank.** `certs-v2.rkt` stopped on a matrix of full column rank (transpose of an empty kernel basis); `certs-v3.rkt` handles it (rank-2x2).
- **LRAT RAT steps** are refused.
- **Scale.** Large numerals make files of tens of MB for pmp; the certificates here have entries below 2^7.

## Reproduce
```
racket tools/lrat-gen-v2.rkt php 2 lrat/inst/php3-2         (also php 3, php 4; rand 10 60 20261009; rand 14 80 777; rand 20 120 4242)
racket lrat-v4.rkt emit lrat/inst/NAME.cnf lrat/inst/NAME.lrat lrat/out4/NAME.jdg
racket tools/certgen-v1.rkt smith "((2 4) (6 8))" certs/in/smith-2x2.sexp          (rank ..., pratt P ...)
racket certs-v2.rkt emit certs/in/NAME.sexp certs/out2/NAME.jdg
racket farkas-v3.rkt emit farkas/in/NAME.sexp farkas/out/NAME.jdg
racket lrat-v4.rkt judge FILE... -- RUN.txt                  (both judges on each file, one row per file)
```

## After the 19:30 power outage (runs of 20:18 on, folder r4\)
- Inputs from other lanes: AG5 cadical CNF/LRAT, L8A consumer samples (Smith 4x4, rank 6x6), G2 corpus system cyclic-k02. Their SHA-256 are in r4\inputs-sha256-r4.txt.
- f3-2d and f2-2d: pmp prints "LIMIT a memory block is full" (exit 1) at theorem 105 step 1357 and theorem 130 step 1317; Racket ACCEPTs. This is a resource stop of the interpreter, not a REJECT.
- r4\judge-mut-r4.txt has one row "pmp OTHER exit -1" (f1-1d-neg-final): a process I stopped, not a verdict.
- Handoff files: HANDOFF-R4.md (20:30) and HANDOFF-R4-FINAL.md (20:45).

originals: 8 × pmp ACCEPT / Racket ACCEPT, 2 × pmp LIMIT / Racket ACCEPT. Mutants: 1 × pmp ? / Racket REJECT, 30 × pmp REJECT / Racket REJECT; both judges name the same theorem and step in 30 of 31.

| file | theorems | steps | bytes | pmp | pmp time | Racket | Racket time |
|---|---:|---:|---:|---|---:|---|---:|
| f3-2d.jdg | 106 | 6180 | 17698633 | LIMIT, exit 1 | 1369.7 s | ACCEPT, exit 0 | 4.3 s |
| f2-2d.jdg | 131 | 7216 | 18220929 | LIMIT, exit 1 | 1398.4 s | ACCEPT, exit 0 | 4.2 s |
| cyclic-k02.jdg | 110 | 5797 | 10792096 | ACCEPT, exit 0 | 888.9 s | ACCEPT, exit 0 | 2.4 s |
| php-5-4.jdg | 12 | 1054 | 1076019 | ACCEPT, exit 0 | 62.9 s | ACCEPT, exit 0 | 1.0 s |
| rand3-v20-s201.jdg | 12 | 1115 | 2113905 | ACCEPT, exit 0 | 299.5 s | ACCEPT, exit 0 | 1.0 s |
| tseitin-cube.jdg | 12 | 705 | 617216 | ACCEPT, exit 0 | 32.5 s | ACCEPT, exit 0 | 0.4 s |
| tseitin-k33.jdg | 12 | 539 | 365164 | ACCEPT, exit 0 | 17.3 s | ACCEPT, exit 0 | 0.6 s |
| tseitin-petersen.jdg | 12 | 1097 | 1235594 | ACCEPT, exit 0 | 65.0 s | ACCEPT, exit 0 | 0.7 s |
| l8a-rank.jdg | 69 | 1823 | 225902 | ACCEPT, exit 0 | 25.1 s | ACCEPT, exit 0 | 4.2 s |
| l8a-smith.jdg | 240 | 9818 | 4077811 | ACCEPT, exit 0 | 339.0 s | ACCEPT, exit 0 | 3.0 s |


| mutant | pmp | Racket | pmp: theorem step | Racket: theorem step | same |
|---|---|---|---|---|---|
| cyclic-k02-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 23 | 2 23 | yes |
| cyclic-k02-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 1 | 3 1 | yes |
| cyclic-k02-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 6 | 3 6 | yes |
| php-5-4-rup-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 92 | 11 92 | yes |
| php-5-4-conflict-drop.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 471 | 11 471 | yes |
| php-5-4-input-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 2 | 11 2 | yes |
| tseitin-petersen-rup-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 82 | 11 82 | yes |
| tseitin-petersen-conflict-drop.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 599 | 11 599 | yes |
| tseitin-petersen-input-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 2 | 11 2 | yes |
| tseitin-k33-rup-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 50 | 11 50 | yes |
| tseitin-k33-conflict-drop.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 183 | 11 183 | yes |
| tseitin-k33-input-goal-neg.jdg | REJECT, exit 1 | REJECT, exit 1 | 11 2 | 11 2 | yes |
| l8a-rank-cert-use-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 68 1 | 68 1 | yes |
| l8a-rank-drop-step.jdg | REJECT, exit 1 | REJECT, exit 1 | 68 53 | 68 53 | yes |
| l8a-rank-exel-var.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 6 | 3 6 | yes |
| l8a-rank-exi-witness.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 3 | 3 3 | yes |
| l8a-rank-leib-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 59 21 | 59 21 | yes |
| l8a-rank-neg-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 68 54 | 68 54 | yes |
| l8a-rank-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 23 | 2 23 | yes |
| l8a-rank-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 1 | 3 1 | yes |
| l8a-rank-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 68 54 | 68 54 | yes |
| l8a-rank-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 0 | 3 0 | yes |
| l8a-smith-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 3 1 | 3 1 | yes |
| l8a-smith-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 23 | 2 23 | yes |
| l8a-smith-cert-use-swap.jdg | REJECT, exit 1 | REJECT, exit 1 | 239 1 | 239 1 | yes |
| f1-1d-main-mid-taut-drop.jdg | REJECT, exit 1 | REJECT, exit 1 | 105 403 | 105 403 | yes |
| f1-1d-neg-final.jdg | ?, exit -1 | REJECT, exit 1 | — | 105 810 | no |
| f1-1d-registry-suc.jdg | REJECT, exit 1 | REJECT, exit 1 | 2 7 | 2 7 | yes |
| f1-1d-taut-goal.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 2 | 4 2 | yes |
| f1-1d-twin-final.jdg | REJECT, exit 1 | REJECT, exit 1 | 105 810 | 105 810 | yes |
| f1-1d-use-shift.jdg | REJECT, exit 1 | REJECT, exit 1 | 4 2 | 4 2 | yes |

