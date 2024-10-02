import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

--Exists examples
example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 2, 9
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -0.1
  constructor
  numbers
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x+1/2
  have h : (x+1/2)^2 = x^2+x+1/4 := by ring
  rw [h]
  have h2 : x^2+1/4 > 0 := by extra
  addarith [h2]

example {p q : ℤ} (hp : Odd p) (hq : Even q) : Odd (p - q - 4) := by
  dsimp [Odd] at *
  dsimp [Even] at *
  obtain ⟨x, hx⟩ := hp
  obtain ⟨y, hy⟩ := hq
  use x-y-2
  rw [hx, hy]
  ring

--For All example
example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  use 0
  intro m
  extra

--Needs real numbers, but automatically gives integers
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use -4
  intros x y h
  sorry

--Divisibility examples
example : (11 : ℕ) ∣ 88 := by
  dsimp [(.∣.)]
  use 8
  numbers

example : (-2 : ℤ) ∣ 6 := by
  dsimp [(.∣.)]
  use -3
  numbers

example {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a := by
  dsimp [(.∣.)] at hab
  obtain ⟨c, hc⟩ := hab
  rw [hc] at hb
  cancel c at hb
