import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- # Exercise 3

/-2 points-/
theorem exercise2_3_6_2 {x : ℝ} (h : x = 1 ∨ x = 2) : x ^ 2 - 3 * x + 2 = 0 := by
  obtain h1 | h2 := h
  calc
    x^2-3*x+2 = 1^2-3*1+2 := by rw [h1]
    _ = 0 := by ring
  calc
    x^2-3*x+2 = 2^2-3*2+2 := by rw [h2]
    _ = 0 := by ring

/-2 points-/
theorem exercise2_3_6_3 {t : ℚ} (h : t = -2 ∨ t = 3) : t ^ 2 - t - 6 = 0 := by
  obtain h1 | h2 := h
  calc
    t^2-t-6 = (-2)^2-(-2)-6 := by rw [h1]
    _ = 0 := by ring
  calc
    t^2-t-6 = (3)^2-(3)-6 := by rw [h2]
    _ = 0 := by ring

/-2 points-/
theorem exercise2_3_6_4 {x y : ℝ} (h : x = 2 ∨ y = -2) : x * y + 2 * x = 2 * y + 4 := by
  obtain hx | hy := h
  calc
    x*y+2*x = 2*y + 2*2 := by rw [hx]
    _ = 2*y + 4 := by ring
  calc
    x*y+2*x = x*(-2) + 2*x := by rw [hy]
    _ = 2*(-2) + 4 := by ring
    _ = 2*y + 4 := by rw [hy]

-- # Exercise 4

/-2 points-/
theorem exercise2_3_6_12 {x : ℤ} : 2 * x ≠ 3 := by
  have hz := le_or_succ_le x 1
  obtain hz | hz := hz
  apply ne_of_lt
  calc
    2*x ≤ 2*1 := by rel [hz]
    _ = 2 := by ring
    _ < 3 := by numbers
  apply ne_of_gt
  calc
    2*x ≥ 2*(2) := by rel [hz]
    _ = 4 := by ring
    _ > 3 := by numbers

/-2 points-/
theorem exercise2_4_5_1 {a b : ℚ} (H : a ≤ 1 ∧ a + b ≤ 3) : 2 * a + b ≤ 4 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2*a+b = a + (a+b) := by ring
    _ ≤ 1 + (a+b) := by rel [h1]
    _ ≤ 1+3 := by rel [h2]
    _ = 4 := by numbers

/-2 points-/
theorem exercise2_4_5_6 {x y : ℚ} (h : x + y = 5 ∧ x + 2 * y = 7) : x = 3 ∧ y = 2 := by
  obtain ⟨h1, h2⟩ := h
  constructor
  . calc
    x = 2*(x+y) - (x+2*y) := by ring
    _ = 2*5 - 7 := by rw [h1, h2]
    _ = 3 := by numbers
  . calc
    y = (x+2*y) - (x+y) := by ring
    _ = 7 - 5 := by rw [h1, h2]
    _ = 2 := by numbers

-- # Problem 2

/-2 points-/
theorem exercise2_3_6_10 {t : ℝ} (ht : t ^ 3 = t ^ 2) : t = 1 ∨ t = 0 := by
  have h1 :=
    calc
      t*(t*(t-1)) = t^3 - t^2 := by ring
      _ = 0 := by addarith [ht]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h3 | h4 := h2
  right
  rw [h3]
  have h5 := eq_zero_or_eq_zero_of_mul_eq_zero h4
  obtain h6 | h7 := h5
  right
  rw [h6]
  left
  addarith [h7]

/-2 points-/
theorem exercise2_3_6_14 {m : ℕ} : m ^ 2 + 4 * m ≠ 46 := by
  have hz := le_or_succ_le m 5
  obtain h1 | h2 := hz
  apply ne_of_lt
  calc
    m^2+4*m ≤ 5^2+4*5 := by rel [h1]
    _ = 45 := by ring
    _ < 46 := by numbers

  apply ne_of_gt
  calc
    46 < 60 := by numbers
    _ = 6^2+4*6 := by ring
    _ ≤ m^2+4*m := by rel [h2]

/-2 points-/
theorem exercise2_4_5_7 {a b : ℝ} (h1 : a * b = a) (h2 : a * b = b) : a = 0 ∧ b = 0 ∨ a = 1 ∧ b = 1 := by
  have h0 :=
    calc
      a*(b-1) = a*b-a := by ring
      _ = 0 := by addarith [h1]
  have h0 := eq_zero_or_eq_zero_of_mul_eq_zero h0
  obtain hl | hr := h0
  left
  constructor
  rw [hl]
  calc
    b = a*b := by rw [h2]
    _ = 0*b := by rw [hl]
    _ = 0 := by ring
  right
  constructor
  calc
    a=a*b := by rw [h1]
    _ = b := by rw [h2]
    _ = (b-1)+1 := by ring
    _ = 0+1 := by rw [hr]
    _ = 1 := by numbers
  addarith [hr]
