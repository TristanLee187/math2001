import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Theory.InjectiveSurjective
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

open Function

/-# Exercise 3-/

--Exercise 8.3.10.2

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := sorry

example : Inverse u v := by
  sorry

--Exercise 8.3.10.3

example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  sorry

--Exercise 8.3.10.4

example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  sorry

/-# Exercise 4-/

--Exercise 8.4.10.1

example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  sorry

--Exercise 8.4.10.2.1

example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  sorry

--Exercise 8.4.10.2.2

example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  sorry

/-# Problem 2-/

--Exercise 8.3.10.5

example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  sorry

--Exercise 8.3.10.7

example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  sorry
