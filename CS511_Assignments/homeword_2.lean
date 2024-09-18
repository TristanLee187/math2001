import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Homework 2 -/

/- # Exercise 3 -/

-- Example 1.4.6
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 := by
  have hp : 15 > 11 := by numbers
  calc
    n^2 = n*n := by ring
    _ ≥ 5*n := by rel[hn]
    _ = 2*n + 3*n := by ring
    _ ≥ 2*n + 3*5 := by rel[hn]
    _ = 2*n + 11 + 4 := by ring
    _ > 2*n + 11 := by extra

-- Example 2.1.3
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 := by
  have h3 : r ≤ 3 + s := by addarith[h1] -- justify with one tactic
  have h4 : r ≤ 3 - s := by addarith[h2] -- justify with one tactic
  calc
    r = (r + r) / 2 := by ring -- justify with one tactic
    _ ≤ (3 - s + (3 + s)) / 2 := by rel[h3, h4] -- justify with one tactic
    _ = 3 := by ring -- justify with one tactic

-- Example 2.1.7
example (a b : ℝ) (h1 : -b ≤ a) (h2 : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  have h3 : 0 ≤ a+b := by addarith[h1]
  have h4 : 0 ≤ b-a := by addarith[h2]
  calc
    a^2 ≤ a^2 + 0*0 := by extra
    _ ≤ a^2 + (a+b)*(b-a) := by rel[h3, h4]
    _ = b^2 := by ring

/- # Exercise 4 -/

-- Exercise 2.1.9 (1)
example {x : ℚ} (h1 : x ^ 2 = 4) (h2 : 1 < x) : x = 2 := by
  have h3 : x*(x+2) = 2*(x+2) := by
    calc
      x*(x+2) = x^2 + 2*x := by ring
      _ = 4 + 2*x := by rw[h1]
      _ = 2*(x+2) := by ring
  cancel (x+2) at h3

-- Exercise 2.1.9 (3)
example (x y : ℚ) (h : x * y = 1) (h2 : x ≥ 1) : y ≤ 1 := by sorry

--Exercise 2.2.4 (1)
example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by sorry

/- # Problem 2 -/

-- Example 2.1.8
example (a b : ℝ) (h : a ≤ b) : a ^ 3 ≤ b ^ 3 := by sorry

-- Exercise 2.1.9 (2)
example {n : ℤ} (hn : n ^ 2 + 4 = 4 * n) : n = 2 := by sorry

-- Exercise 2.2.4 (2)
example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by sorry
