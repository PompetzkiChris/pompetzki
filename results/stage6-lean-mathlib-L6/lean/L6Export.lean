/-
L6Export.lean -- lane L6 (Stage 6), 2026-10-09. Untrusted exporter: reads the environment of `import Mathlib`
(Mathlib v4.28.0 as built in C:\ClaudeOutput\abschluss\lean\AbschlussCore, Lean v4.28.0) and writes the
statement (the type) of every theorem whose type uses only the constants of the first slice: the natural numbers
with =, ≠, ≤, <, +, *, succ, numerals, and the connectives ¬ ∧ ∨ ↔ → ∀ ∃. One line per theorem:
  (thm "NAME" "MODULE" TYPE)
TYPE as an s-expression of Lean.Expr: (bvar i) (const "c") (app F A) (pi "x" BI DOM BODY) (lam "x" BI DOM BODY)
(lit N) (sort) — mdata is dropped. Run from the project directory:  lake env lean <this file>
The output file is the input of the translator lean2zf.rkt. Lean's kernel is not the judge here: the statements
are candidates only; each becomes a ZF theorem only when both pmp judges accept its derivation.
-/
import Mathlib

open Lean Meta

namespace L6

def esc (s : String) : String :=
  s.foldl (fun acc c => if c == '"' || c == '\\' then acc.push '\\' |>.push c else acc.push c) ""

def bi (b : BinderInfo) : String :=
  match b with
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

partial def ser : Expr → String
  | .bvar i => s!"(bvar {i})"
  | .fvar _ => "(fvar)"
  | .mvar _ => "(mvar)"
  | .sort _ => "(sort)"
  | .const n _ => s!"(const \"{esc n.toString}\")"
  | .app f a => s!"(app {ser f} {ser a})"
  | .lam n t b i => s!"(lam \"{esc n.toString}\" {bi i} {ser t} {ser b})"
  | .forallE n t b i => s!"(pi \"{esc n.toString}\" {bi i} {ser t} {ser b})"
  | .letE n t v b _ => s!"(let \"{esc n.toString}\" {ser t} {ser v} {ser b})"
  | .lit (.natVal k) => s!"(lit {k})"
  | .lit (.strVal s) => s!"(str \"{esc s}\")"
  | .mdata _ e => ser e
  | .proj s i e => s!"(proj \"{esc s.toString}\" {i} {ser e})"

/-- the constants a first-slice statement may use -/
def allowed : List Name :=
  [``Nat, ``Eq, ``Ne, ``Not, ``And, ``Or, ``Iff, ``Exists, ``True, ``False,
   ``HAdd.hAdd, ``instHAdd, ``instAddNat, ``HMul.hMul, ``instHMul, ``instMulNat,
   ``LE.le, ``instLENat, ``LT.lt, ``instLTNat, ``Nat.succ, ``OfNat.ofNat, ``instOfNatNat,
   ``GE.ge, ``GT.gt]

def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => "?"

end L6

open L6 in
run_meta do
  let env ← getEnv
  let mut out : Array String := #[]
  let mut nThm := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo t =>
      nThm := nThm + 1
      if n.isInternal then continue
      let ty := t.type
      let used := ty.getUsedConstants
      if used.all (fun c => allowed.contains c) && used.contains ``Nat then
        out := out.push s!"(thm \"{esc n.toString}\" \"{modOf env n}\" {ser ty})"
    | _ => pure ()
  let path := "C:/ClaudeOutput/pompetzki/lanes/L6/lean/export-nat.sexp"
  IO.FS.writeFile path (String.intercalate "\n" out.toList ++ "\n")
  logInfo m!"theorems in the environment: {nThm}; first-slice statements written: {out.size} to {path}"
