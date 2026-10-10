/-
L6Export3.lean -- lane L6 round 2 (2026-10-09 evening). Untrusted exporter, run once from AbschlussCore:
  lake env lean <this file>
For every theorem of lanes\AG2\queue.tsv whose type starts with exactly one Sort binder (a type variable), the statement
at the type ℤ and at the type ℕ: the type variable is replaced, every instance binder that follows directly is filled by
type-class synthesis, and every +, *, −, unary −, ≤, <, 0, 1, numeral and ↑ whose instance is definitionally equal to
the canonical one (instHAdd ℤ Int.instAdd, …) gets the canonical instance. The rest of the statement is left as it is.
Writes export-inst.sexp:  (inst "NAME" "MODULE" "Int"|"Nat" TYPE)  or  (inst-fail "NAME" "Int"|"Nat" "REASON").
These are instances of the Mathlib statements, not the statements themselves; candidates only.
-/
import Mathlib

open Lean Meta

namespace L6c

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
def modOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => "?"

/-- canonical instances for the type T (ℤ or ℕ) -/
def canon (isInt : Bool) (h : Name) : Option Expr :=
  let T := if isInt then mkConst ``Int else mkConst ``Nat
  match h with
  | ``HAdd.hAdd => some (mkApp2 (mkConst ``instHAdd [0]) T (mkConst (if isInt then `Int.instAdd else ``instAddNat)))
  | ``HMul.hMul => some (mkApp2 (mkConst ``instHMul [0]) T (mkConst (if isInt then `Int.instMul else ``instMulNat)))
  | ``HSub.hSub => if isInt then some (mkApp2 (mkConst ``instHSub [0]) T (mkConst `Int.instSub)) else none
  | ``Neg.neg => if isInt then some (mkConst `Int.instNegInt) else none
  | ``LE.le => some (mkConst (if isInt then `Int.instLEInt else ``instLENat))
  | ``LT.lt => some (mkConst (if isInt then `Int.instLTInt else ``instLTNat))
  | _ => none

/-- replace instance arguments by the canonical ones where Lean finds them definitionally equal -/
partial def normInst (isInt : Bool) (e : Expr) : MetaM Expr := do
  let T := if isInt then mkConst ``Int else mkConst ``Nat
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args ← e.getAppArgs.mapM (normInst isInt)
    if let .const h _ := f then
      -- binary/unary operators and relations: the instance is the argument after the type arguments
      let pos : Option Nat := match h with
        | ``HAdd.hAdd | ``HMul.hMul | ``HSub.hSub => some 3
        | ``Neg.neg | ``LE.le | ``LT.lt => some 1
        | _ => none
      if let some p := pos then
        if args.size > p && !args[0]!.hasLooseBVars && !args[p]!.hasLooseBVars && (← isDefEq args[0]! T) then
          if let some c := canon isInt h then
            if (← withTransparency .instances (isDefEq args[p]! c)) then
              return mkAppN f (args.set! p c)
      -- numerals 0, 1, n
      if h == ``OfNat.ofNat && args.size == 3 && !args[0]!.hasLooseBVars && !args[2]!.hasLooseBVars && (← isDefEq args[0]! T) then
        if let .lit (.natVal n) := args[1]! then
          let c := if isInt then mkApp (mkConst `instOfNat) (mkRawNatLit n) else mkApp (mkConst ``instOfNatNat) (mkRawNatLit n)
          if (← withTransparency .instances (isDefEq args[2]! c)) then
            return mkAppN f (args.set! 2 c)
      if h == ``Zero.zero && args.size == 2 && !args[0]!.hasLooseBVars && (← isDefEq args[0]! T) then
        let c := if isInt then mkApp (mkConst `instOfNat) (mkRawNatLit 0) else mkApp (mkConst ``instOfNatNat) (mkRawNatLit 0)
        return mkApp3 (mkConst ``OfNat.ofNat [0]) T (mkRawNatLit 0) c
      if h == ``One.one && args.size == 2 && !args[0]!.hasLooseBVars && (← isDefEq args[0]! T) then
        let c := if isInt then mkApp (mkConst `instOfNat) (mkRawNatLit 1) else mkApp (mkConst ``instOfNatNat) (mkRawNatLit 1)
        return mkApp3 (mkConst ``OfNat.ofNat [0]) T (mkRawNatLit 1) c
    return mkAppN f args
  | .forallE n d b i =>
    return .forallE n (← normInst isInt d) (← normInst isInt b) i
  | .lam n d b i =>
    return .lam n (← normInst isInt d) (← normInst isInt b) i
  | _ => return e

/-- instantiate the leading Sort binder by T and the instance binders that follow by synthesis -/
partial def specialize (T : Expr) (ty : Expr) (seenSort : Bool) : MetaM (Except String Expr) := do
  match ty with
  | .forallE _ d b bi =>
    if d.isSort then
      if seenSort then return .error "a second type variable"
      specialize T (b.instantiate1 T) true
    else if bi.isInstImplicit then
      if !seenSort then return .error "an instance binder before the type variable"
      match ← (try? (synthInstance d)) with
      | some inst => specialize T (b.instantiate1 inst) true
      | none => return .error s!"no instance of {← ppExpr d}"
    else
      if !seenSort then return .error "a binder before the type variable"
      return .ok ty
  | _ => if seenSort then return .ok ty else return .error "no type variable"

end L6c

open L6c in
run_meta do
  let env ← getEnv
  let mut table : Std.HashMap String Name := {}
  for (n, _) in env.constants.toList do
    table := table.insert n.toString n
  let lines ← IO.FS.lines "C:/ClaudeOutput/pompetzki/lanes/AG2/queue.tsv"
  let mut out : Array String := #[]
  let mut nInst := 0
  for ln in lines.toList.drop 1 do
    let nm := (ln.splitOn "\t").headD ""
    let some n := table.get? nm | continue
    let some ci := env.find? n | continue
    let .thmInfo t := ci | continue
    -- only the declarations that start with a Sort binder (possibly after implicit universe-only binders)
    match t.type with
    | .forallE _ d _ _ =>
      if !d.isSort then continue
    | _ => continue
    for (isInt, tname) in [(true, "Int"), (false, "Nat")] do
      let T := if isInt then mkConst ``Int else mkConst ``Nat
      let ty ← instantiateMVars (← instantiateTypeLevelParams ci (ci.levelParams.map fun _ => levelZero))
      let r ← try specialize T ty false catch ex => pure (.error s!"exception: {← ex.toMessageData.toString}")
      match r with
      | .ok sty =>
        let sty' ← try normInst isInt sty catch _ => pure sty
        nInst := nInst + 1
        out := out.push s!"(inst \"{esc nm}\" \"{modOf env n}\" \"{tname}\" {ser sty'})"
      | .error why =>
        out := out.push s!"(inst-fail \"{esc nm}\" \"{tname}\" \"{esc why}\")"
  IO.FS.writeFile "C:/ClaudeOutput/pompetzki/lanes/L6/lean/export-inst.sexp" (String.intercalate "\n" out.toList ++ "\n")
  logInfo m!"instances written: {nInst}; lines {out.size}"
