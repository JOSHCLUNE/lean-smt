# Lean-SMT

This project provides Lean tactics to discharge goals into SMT solvers.
It is under active development and is currently in a beta phase. While it is
usable, it is important to note that there are still some rough edges and
ongoing improvements being made.

## Supported Theories
`lean-smt` currently supports the theories of Uninterpreted Functions and Linear
Integer/Real Arithmetic with quantifiers. Mathlib is required for Real
Arithmetic. Support for the theory of Bitvectors is at an experimental stage.
Support for additional theories is in progress.

## Setup
To use `lean-smt` in your project, add the following lines to your list of
dependencies in `lakefile.toml`:
```toml
[[require]]
name = "smt"
scope = "ufmg-smite"
rev = "main"
```
If your build configuration is in `lakefile.lean`, add the following line to
your dependencies:
```lean
require smt from git "https://github.com/ufmg-smite/lean-smt.git" @ "main"
```

Alternatively, `lean-smt` has an experimental `no_mathlib` branch which can
be accessed by replacing `main` with `no_mathlib` in your `lakefile.toml`
or `lakefile.lean` file.

## Usage
`lean-smt` comes with one main tactic, `smt`, that translates the current goal
into an SMT query, sends the query to cvc5, and (if the solver returns `unsat`)
replays cvc5's proof in Lean. cvc5's proofs may contain holes, returned as Lean
goals. You can fill these holes manually or with other tactics. To use the `smt`
tactic, you just need to import the `Smt` library:
```lean
import Smt

example [Nonempty U] {f : U → U → U} {a b c d : U}
  (h0 : a = b) (h1 : c = d) (h2 : p1 ∧ True) (h3 : (¬ p1) ∨ (p2 ∧ p3))
  (h4 : (¬ p3) ∨ (¬ (f a c = f b d))) : False := by
  smt [h0, h1, h2, h3, h4]
```
To use the `smt` tactic on Real arithmetic goals, import `Smt.Real`:
```lean
import Smt
import Smt.Real

example (ε : Real) (h1 : ε > 0) : ε / 2 + ε / 3 + ε / 7 < ε := by
  smt [h1]
```
`lean-smt` utilizes
[`lean-auto`](https://github.com/leanprover-community/lean-auto) to monomorphize
goals in dependent type theory and higher-order logic into first-order logic.
Enable auto's monomorphization procedure via `smt +mono`:
```lean
import Smt

variable [Group G]

theorem inverse : ∀ (a : G), a * a⁻¹ = 1 := by
  smt +mono [mul_assoc, one_mul, inv_mul_cancel]

theorem identity : ∀ (a : G), a * 1 = a := by
  smt +mono [mul_assoc, one_mul, inv_mul_cancel, inverse]

theorem unique_identity : ∀ (e : G), (∀ a, e * a = a) ↔ e = 1 := by
  smt +mono [mul_assoc, one_mul, inv_mul_cancel]
```

## Lean's Module System
`lean-smt` uses [Lean's module system](https://lean-lang.org/doc/reference/latest/), so it can be
used both from ordinary Lean files and from files that begin with `module`. Files that do not opt
into the module system are unaffected: a plain `import Smt` keeps working exactly as before.
* To *invoke* `smt` (or any other tactic `lean-smt` exports) from a `module`, a plain `import Smt` is
  all that is needed. See `Test/ModuleSystem.lean`.
  ```lean
  module

  import Smt

  theorem modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := by
    smt [hp, hpq]
  ```
* To write a *metaprogram* that refers to `lean-smt`'s own declarations — e.g. a hammer-style tactic
  that calls `Smt.smt` — a `module` additionally needs `meta import Smt`, because metaprograms may
  only refer to declarations that are available for compile-time execution. See
  `Test/ModuleSystemDownstream.lean`.
  ```lean
  module

  public import Smt
  meta import Smt

  open Lean Elab Tactic in
  meta def mySmt : TacticM Unit := withMainContext do
    match ← Smt.smt {} (← getMainGoal) #[] with
    | .unsat mvs _ => replaceMainGoal mvs
    | _ => throwError "my_smt failed"

  elab "my_smt" : tactic => mySmt
  ```

The modules that already did not build against the current Mathlib — most of
`Smt/Reconstruct/Arith/` and `Smt/Reconstruct/Certified/`, plus `Smt/Arith.lean`,
`Smt/Reconstruct/Timed.lean`, and `Smt/Tactic/Concretize.lean` — are left as non-`module` files,
since there is no way to compile them and check that a migration did not break them. This mixture
is fine: a non-`module` file may import `module` files (only the reverse is disallowed).
