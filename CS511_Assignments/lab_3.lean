import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-
# New tactics and techniques
# Section 1.4
rel [R]
numbers
extra
# Section 1.5
addarith [H]
# Section 2.1
have
cancel
# Section 2.2
apply
-/

-- Example 1.4.3
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 := by
  calc
    x + y ≤ x + (x+5) := by rel[h1]
    _ = 2*x+5 := by ring
    _ ≤ 2*(-2)+5 := by rel[h2]
    _ < 2 := by numbers

-- Example 1.4.4
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
        u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by rel[h5, h4]
    _ ≤ A * B + A * B + A * v := by rel[h8, h9]
    _ ≤ A * B + A * B + 1 * v := by rel[h2]
    _ ≤ A * B + A * B + B * v := by rel[h3]
    _ < A * B + A * B + B * A := by rel[h9]
    _ = 3 * A * B := by ring

-- Example 1.4.5
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
        t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by ring
    _ ≥ 10 * t - 3 * t - 17 := by rel[ht]
    _ = 7 * t - 17 := by ring
    _ ≥ 7 * 10 - 17 := by rel[ht]
    _ ≥ 5 := by numbers

-- Example 2.1.6
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  have hz : x ≤ -1 := by addarith[hx]
  calc
    y ≥ 3 - 2*x := by addarith[hy]
    _ ≥ 3 - 2*(-1) := by rel[hz]
    _ > 3 := by numbers

/- # Important Lemmas (no need to prove) -/

-- Not Equal of Less Than
lemma ne_of_lt' {a b : ℚ} (h : a < b) : a ≠ b := by sorry

lemma ne_of_gt' {a b : ℝ} (h : a > b) : a ≠ b := by sorry

lemma le_antisymm' {a b : ℝ} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by sorry

-- Example 2.2.2
example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt'
  calc
    y^2+1 ≥ 1 := by extra
    _ > 0 := by numbers
