/-
L6Export2.lean -- lane L6, round 2 (2026-10-09 evening). Untrusted exporter, run once from the AbschlussCore project:
  lake env lean <this file>
Writes three files next to this one:
  export-queue.sexp   for every name of lanes\AG2\queue.tsv:  (decl "NAME" "MODULE" KIND TYPE)  or  (absent "NAME")
  export-int.sexp     every theorem whose type uses only the constants of the Int/Nat slice:  (thm "NAME" "MODULE" TYPE)
  export-proofs.sexp  the proof terms (values) of the names in proofs-wanted.txt, up to 200,000 characters:
                      (proof "NAME" VALUE)  or  (proof-too-large "NAME" CHARS)
Same s-expression form as L6Export.lean: (bvar i) (const "c") (app F A) (pi "x" BI DOM BODY) (lam "x" BI DOM BODY) (lit N)
(sort) (let ...) (proj "S" i E) (str "s"). Lean's kernel is not the judge; these are candidates only.
-/
import Mathlib

open Lean Meta

namespace L6b

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

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def baseAllowed : List Name :=
  [`Nat, `Int, `Eq, `Ne, `Not, `And, `Or, `Iff, `Exists, `HAdd.hAdd, `instHAdd, `HMul.hMul, `instHMul,
   `HSub.hSub, `instHSub, `Neg.neg, `LE.le, `LT.lt, `GE.ge, `GT.gt, `OfNat.ofNat, `NatCast.natCast, `Nat.cast,
   `IntCast.intCast, `Int.cast]

/-- the Int slice: basic constants, anything in the namespaces Int and Nat, and instances -/
def intOk (c : Name) : Bool :=
  baseAllowed.contains c || c.getRoot == `Int || c.getRoot == `Nat || (c.toString.startsWith "inst")

def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => "?"

end L6b

open L6b in
run_meta do
  let env ← getEnv
  let dir := "C:/ClaudeOutput/pompetzki/lanes/L6/lean/"
  -- the name table: string -> Name
  let mut table : Std.HashMap String Name := {}
  for (n, _) in env.constants.toList do
    table := table.insert n.toString n
  -- 1. the AG2 queue
  let lines ← IO.FS.lines "C:/ClaudeOutput/pompetzki/lanes/AG2/queue.tsv"
  let mut out : Array String := #[]
  let mut found := 0
  for ln in lines.toList.drop 1 do
    let nm := (ln.splitOn "\t").headD ""
    if nm == "" then continue
    match table.get? nm with
    | some n =>
      match env.find? n with
      | some ci =>
        found := found + 1
        out := out.push s!"(decl \"{esc nm}\" \"{modOf env n}\" {kind ci} {ser ci.type})"
      | none => out := out.push s!"(absent \"{esc nm}\")"
    | none => out := out.push s!"(absent \"{esc nm}\")"
  IO.FS.writeFile (dir ++ "export-queue.sexp") (String.intercalate "\n" out.toList ++ "\n")
  -- 2. the Int slice of the whole environment
  let mut iout : Array String := #[]
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo t =>
      if n.isInternal then continue
      let used := t.type.getUsedConstants
      if used.all intOk && used.contains `Int then
        iout := iout.push s!"(thm \"{esc n.toString}\" \"{modOf env n}\" {ser t.type})"
    | _ => pure ()
  IO.FS.writeFile (dir ++ "export-int.sexp") (String.intercalate "\n" iout.toList ++ "\n")
  -- 3. proof terms of the wanted names
  let wanted ← IO.FS.lines (dir ++ "proofs-wanted.txt")
  let mut pout : Array String := #[]
  for nm in wanted.toList do
    if nm == "" then continue
    match table.get? nm with
    | some n =>
      match env.find? n with
      | some (.thmInfo t) =>
        let s := ser t.value
        if s.length ≤ 200000 then pout := pout.push s!"(proof \"{esc nm}\" {s})"
        else pout := pout.push s!"(proof-too-large \"{esc nm}\" {s.length})"
      | _ => pout := pout.push s!"(no-proof \"{esc nm}\")"
    | none => pout := pout.push s!"(no-proof \"{esc nm}\")"
  IO.FS.writeFile (dir ++ "export-proofs.sexp") (String.intercalate "\n" pout.toList ++ "\n")
  logInfo m!"queue lines {lines.size - 1}, found {found}; Int slice {iout.size}; proofs {pout.size}"
