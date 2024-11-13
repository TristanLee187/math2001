import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust

math2001_init

open Function

example : Injective (fun (x : ℝ) ↦ 3) := by
  sorry

example : ¬ Injective (fun (x : ℝ) ↦ 3) := by
  dsimp [Injective]
  push_neg
  use 0, 1
  constructor
  . numbers
  . numbers

example : Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  dsimp [Injective]
  intros a b hab
  have hab : 3*a = 3*b := by addarith [hab]
  cancel 3 at hab

example : ¬ Injective (fun (x : ℤ) ↦ 3 * x - 1) := by
  sorry

example (f : X → Y) : Injective f ↔ ∀ x1 x2 : X, x1 ≠ x2 → f x1 ≠ f x2 := by
  constructor
  . intros injf x1 x2 hx12
    dsimp [Injective] at injf
    intro contra
    have this := injf contra
    contradiction
  . intros H
    dsimp [Injective]
    intros a b hab
    by_cases h : a=b
    . exact h
    . have contra := H a b h
      contradiction

example : Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  constructor
  . dsimp [Injective]
    intros a b hab
    have hab : -3*a = -3*b := by addarith [hab]
    cancel -3 at hab
  . dsimp [Surjective]
    intros b
    use (4-b)/3
    ring

example : ¬ Bijective (fun (x : ℝ) ↦ 4 - 3 * x) := by
  sorry


example : Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  sorry

example : ¬ Bijective (fun (x : ℝ) ↦ x ^ 2 + 2 * x) := by
  dsimp [Bijective]
  push_neg
  left
  dsimp [Injective]
  push_neg
  use -2, 0
  constructor
  . numbers
  . numbers

inductive Element
  | fire
  | water
  | earth
  | air
  deriving DecidableEq

open Element

def e : Element → Element
  | fire => earth
  | water => air
  | earth => fire
  | air => water

example : Bijective e := by
  constructor
  . dsimp [Injective]
    intros a b hab
    cases a <;> cases b <;> exhaust
  . dsimp [Surjective]
    intros b
    cases b
    . use earth; dsimp [e]
    . use air; dsimp [e]
    . use fire; dsimp [e]
    . use water; dsimp [e]


example : ¬ Bijective e := by
  sorry
