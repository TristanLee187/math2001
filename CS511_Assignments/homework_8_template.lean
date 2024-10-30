import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import Library.Tactic.ModEq
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

--# Exercise 3

--Slides 18, Page 25

example (h : ∃x : Type, ∀y : Type, (x = y)) : (∀x : Type, ∀y : Type, (x = y)) := by
  sorry

--Slides 29 Part III, Page 8

example : (∃x : Type, ∀y : Type, (x = y)) → (∀v : Type, ∀w : Type, (v = w)) := by
  sorry

--# Exercise 4

--Exercise 5.3.6.9

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  sorry

--Example 6.1.2

example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    sorry
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · sorry
    · sorry

--Example 6.1.6

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    sorry
  · -- inductive step
    sorry

--# Problem 2

--Exercise 5.3.6.12

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  sorry

--Exercise 6.1.7.2

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  sorry

--Exercise 6.1.7.3

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  sorry
