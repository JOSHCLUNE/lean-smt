module

/-
  `lean-smt` is migrated to Lean's module system, so the `smt` tactic can be used from files that
  begin with `module`.

  Merely *invoking* `smt` needs nothing beyond a plain `import`; see `Test/ModuleSystemDownstream.lean`
  for the additional `meta import` a downstream *metaprogram* needs.

  The examples below deliberately span the theories `smt` reconstructs proofs for, because a proof
  term that mentions a declaration `lean-smt` failed to make `public` would only fail here, in the
  importing module, and not while building `lean-smt` itself.
-/

-- `Smt.Rat` and `Smt.Real` cannot be imported together (they already conflicted before this
-- migration), so this file covers `Real`; `Test/Rat/` covers `Rat`.
import Smt
import Smt.Real

-- Propositional reasoning and resolution.
theorem modus_ponens (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [hp, hpq]

example (p q r : Prop) : (p ∨ q) → (¬p ∨ r) → (q ∨ r) := by
  smt

-- `Bool`, which is embedded into `Prop` during preprocessing.
theorem addition (p q : Bool) : p → p || q := by
  smt

theorem cong_bool (p q : Bool) (f : Bool → Bool) : p == q → f p == f q := by
  smt

-- `if then else`, which goes through `Smt.Preprocess.Embedding.IteCongrSimproc`.
example (c : Prop) [Decidable c] (x y : Int) : (if c then x else y) = x ∨ (if c then x else y) = y := by
  smt

-- `Nat`, which is embedded into `Int` during preprocessing.
theorem nat_zero_sub (x : Nat) : x = 0 → 0 - x = 0 := by
  smt

example (x y : Nat) : x ≤ y → x + 1 ≤ y + 1 := by
  smt

-- `Int`.
theorem cong_int (x y : Int) (f : Int → Int) : x = y → f x = f y := by
  smt

example (x y : Int) : x < y → x + 1 ≤ y := by
  smt

-- `Real`.
example (x y : Real) : x < y → x ≤ y := by
  smt

-- Uninterpreted functions and congruence.
example [Nonempty U] {f : U → U → U} {a b c d : U} (h₀ : a = b) (h₁ : c = d) :
    f a c = f b d := by
  smt [h₀, h₁]

-- Quantifiers.
example {U : Type} [Nonempty U] {p : U → Prop} :
    (∀ x y z, p x ∧ p y ∧ p z) = ((∀ x, p x) ∧ (∀ y, p y) ∧ (∀ z, p z)) := by
  smt

-- `smt` options and hints parse the same way from a `module`.
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  smt [*]

-- Declarations `lean-smt` exports are visible to a plain `import`, and `@[expose]`d definitions
-- still reduce here (they would be opaque without `@[expose]`).
example (p q : Prop) : orN [p, q] = (p ∨ q) := rfl
example (p q : Prop) : andN [p, q] = (p ∧ q) := rfl
