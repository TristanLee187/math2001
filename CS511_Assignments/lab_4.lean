import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/- # Lab 4 -/

/-
Or:
  In the context:  split the premise into cases
    E.g., obtain h1 | h2 := h
  In the goal:  choose which case you want to prove
    using the tactics left and right
And:
  In the context:  split the premise into 2 separate premises
    E.g., obtain ⟨h1,h2⟩ := h
  In the goal:  use the tactic constructor to split the proof into cases;
    one for each clause of the ∧
-/

/- If we have an implication f : p -> q,
in Lean 4, it works essentially like a function.
That is, if we have x : p, then if we write f x, its type is q.
In other words, if we apply a proof of p to a proof that p -> q,
we get a proof of q. -/

--Example 2.3.4
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 :=
    calc
    (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
    _ = 0 := by rw [hx]
  have h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  obtain h3 | h4 := h2
  left
  addarith [h3]
  right
  addarith [h4]

--Exercise 2.3.6.1
example {x : ℚ} (h : x = 4 ∨ x = -4) : x ^ 2 + 1 = 17 := by
  obtain h | h := h
  calc
    x^2+1 = 4^2+1 := by rw [h]
    _ = 17 := by ring
  calc
    x^2+1 = (-4)^2+1 := by rw [h]
    _ = 17 := by ring

--Exercise 2.3.6.7
example {x y : ℝ} (h : y = 2 * x + 1) : x < y / 2 ∨ x > y / 2 := by
  left
  have h : x=(y-1)/2 := by addarith [h]
  calc
    x < x + 1/2 := by extra
    _ = (y-1)/2 + 1/2 := by rw [h]
    _ = y/2 := by ring

--Exercise 2.4.5.2
example {r s : ℝ} (H : r + s ≤ 1 ∧ r - s ≤ 5) : 2 * r ≤ 6 := by
  obtain ⟨h1, h2⟩ := H
  calc
    2*r = (r+s) + (r-s) := by ring
    _ ≤ 1+5 := by rel [h1, h2]
    _ = 6 := by numbers

--Exercise 2.4.5.3
example {m n : ℤ} (H : n ≤ 8 ∧ m + 5 ≤ n) : m ≤ 3 := by
  obtain ⟨h1, h2⟩ := H
  calc
    m ≤ n-5 := by addarith [h2]
    _ ≤ 8-5 := by rel [h1]
    _ = 3 := by numbers

--Exercise 2.4.5.4
example {p : ℤ} (hp : p + 2 ≥ 9) : p ^ 2 ≥ 49 ∧ 7 ≤ p := by
  have hp : p ≥ 7 := by addarith [hp]
  constructor
  calc
    p^2 ≥ 7^2 := by rel [hp]
    _ = 49 := by numbers
  addarith [hp]

--Exercise 2.4.5.5
example {a : ℚ} (h : a - 1 ≥ 5) : a ≥ 6 ∧ 3 * a ≥ 10 := by
  have h : a ≥ 6 := by addarith [h]
  constructor
  apply h
  calc
    3*a ≥ 3*6 := by rel [h]
    _ ≥ 10 := by numbers
