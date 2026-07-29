module

/-
  A downstream `module` that builds its own tactic on top of `Smt.smt`, the way a hammer-style
  tactic would.

  A plain `import Smt` is enough to *invoke* `smt` (see `Test/ModuleSystem.lean`), but a
  metaprogram that refers to `lean-smt`'s own declarations additionally needs `meta import` —
  metaprograms may only refer to declarations that are available for compile-time execution. See
  the documentation of `meta` in Lean's module system.
-/

public import Smt
meta import Smt

open Lean Elab Tactic Meta

/-- A minimal `smt`-based tactic: hand the main goal and every hypothesis to `Smt.smt`, and close
the goal with the reconstructed proof. -/
meta def mySmt : TacticM Unit := withMainContext do
  let mv ← getMainGoal
  let hs ← (← getLCtx).foldlM (init := #[]) fun hs decl => do
    if decl.isImplementationDetail || !(← isProof decl.toExpr) then return hs
    return hs.push decl.toExpr
  match ← Smt.smt {} mv hs with
  | .unsat mvs _ => replaceMainGoal mvs
  | .sat _ => throwError "my_smt: the goal is falsifiable"
  | .unknown reason => throwError "my_smt: {reason}"

elab "my_smt" : tactic => mySmt

example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  my_smt

example (x y : Int) (h : x < y) : x + 1 ≤ y := by
  my_smt

-- `lean-smt`'s translation layer is reachable from a `meta` definition too.
meta def sortName : Smt.Term → String
  | .symbolT s => s
  | _ => "?"

/-- info: "Int" -/
#guard_msgs in
#eval sortName (Smt.Term.symbolT "Int")
