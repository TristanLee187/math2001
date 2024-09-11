import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # CS 511 Lab 2
# September 11, 2024 -/

/- # Potential problems to solve together in lab.  Solve as many as you like. -/

/- # Exercises 1.3.1 through 1.3.6 -/

example {x y : ℝ} (h1 : x = 3) (h2 : y = 4 * x - 3) : y = 9 := by
  calc
    y = 4 * x - 3 := by rw [h2]
    _ = 4*3-3 := by rw [h1]
    _ = 9 := by ring

example {a b : ℤ} (h : a - b = 0) : a = b := by
  calc
    a = (a - b) + b := by ring
    _ = 0 + b := by rw [h]
    _ = b := by ring

example {x y : ℤ} (h1 : x - 3 * y = 5) (h2 : y = 3) : x = 14 := by
  calc
    x = (x-3*y)+3*y := by ring
    _ = 5+3*3 := by rw [h1, h2]
    _ = 14 := by ring

example {p q : ℚ} (h1 : p - 2 * q = 1) (h2 : q = -1) : p = -1 := by
  calc
    p = (p-2*q) + 2*q := by ring
    _ = 1 + 2*(-1) := by rw [h1, h2]
    _ = -1 := by ring

example {x y : ℚ} (h1 : y + 1 = 3) (h2 : x + 2 * y = 3) : x = -1 := by
  calc
    x = (x+2*y) - 2*(y+1) + 2 := by ring
    _ = 3 - 2*(3) + 2 := by rw [h1, h2]
    _ = -1 := by ring

example {p q : ℤ} (h1 : p + 4 * q = 1) (h2 : q - 1 = 2) : p = -11 := by
  calc
    p = (p+4*q) - 4*(q-1) - 4 := by ring
    _ = 1 - 4*2 - 4 := by rw [h1, h2]
    _ = -11 := by ring

/- # Examples from Section 1.4 -/

-- Example 1.4.1
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by numbers

-- Example 1.4.3
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  calc
    x+y ≤ x+(x+5) := by rel [h1]
    _ = 2*x+5 := by ring
    _ ≤ 2*(-2)+5 := by rel [h2]
    _ < 2 := by numbers


-- Example 1.4.4
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by rel [h5, h4]
    _ ≤ A * B + A * B + A * v := by rel [h8, h9]
    _ ≤ A * B + A * B + 1 * v := by rel [h2]
    _ ≤ A * B + A * B + B * v := by rel [h3]
    _ < A * B + A * B + B * A := by rel [h9]
    _ = 3 * A * B := by ring

-- Example 1.4.5
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by ring
    _ ≥ 10 * t - 3 * t - 17 := by rel [ht]
    _ = 7 * t - 17 := by ring
    _ ≥ 7 * 10 - 17 := by rel [ht]
    _ ≥ 5 := by numbers

-- Example 1.4.6
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc
    n^2 = n*n := by ring
    _ ≥ 5*n := by rel [hn]
    _ = 2*n + 3*n := by ring
    _ ≥ 2*n + 3*5 := by rel [hn]
    _ = 2*n + 11 + 4 := by ring
    _ > 2*n + 11 := by extra

-- Example 1.4.7
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 :=
  calc
    n ≤ m ^ 2 + n := by extra
    _ ≤ 2 := by rel [h]

-- Example 1.4.8
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 1 := by rel [h]
    _ < 3 := by numbers

-- Example 1.4.9
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by extra
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring
    _ ≤ 2 * (8 * b) + 8 * a + a := by rel [h3]
    _ = 7 * b + 9 * (a + b) := by ring
    _ ≤ 7 * b + 9 * 8 := by rel [h3]
    _ = 7 * b + 72 := by ring

/- # Work through first Lean 4 exercise together? -/

example {w : ℚ} (h1 : 3 * w + 1 = 4) : w = 1 := by
  calc
    w = ((3*w+1)-1)/3 := by ring
    _ = (4-1)/3 := by rw [h1]
    _ = 1 := by ring
