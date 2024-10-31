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
  intros x y
  obtain ⟨k, hk⟩ := h
  have hx : k=x := by apply hk
  have hy : k=y := by apply hk
  rw [hx] at hy
  exact hy

--Slides 29 Part III, Page 8

example : (∃x : Type, ∀y : Type, (x = y)) → (∀v : Type, ∀w : Type, (v = w)) := by
  intros h
  intros x y
  obtain ⟨k, hk⟩ := h
  have hx : k=x := by apply hk
  have hy : k=y := by apply hk
  rw [hx] at hy
  exact hy

--# Exercise 4

--Exercise 5.3.6.9

example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  intros t
  have ht : ¬ (4 ≥ t ∧ t ≥ 5) := by
    intros contra
    obtain ⟨a, b⟩ := contra
    have contra :=
      calc
        4 ≥ t := by apply a
        _ ≥ 5 := by apply b
    numbers at contra
  push_neg at ht
  exact ht

--Example 6.1.2

example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    left
    use 0
    numbers
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · right
      use x
      rw [hx]
      ring
    · left
      use x+1
      rw [hx]
      ring

--Example 6.1.6

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc
      2^(k+1) = 2*2^k := by ring
      _ ≥ 2*k^2 := by rel [IH]
      _ = k^2 + k*k := by ring
      _ ≥ k^2 + 4*k := by rel [hk]
      _ = k^2 + 2*k + 2*k := by ring
      _ ≥ k^2 + 2*k + 2*4 := by rel [hk]
      _ = (k+1)^2 + 7 := by ring
      _ ≥ (k+1)^2 := by extra


--# Problem 2

--Exercise 5.3.6.12

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by
  push_neg
  intros a
  use a^3
  have h := le_or_succ_le a 0
  obtain n | p := h
  . calc
      2*a^3 = 2*a*a^2 := by ring
      _ ≤ 2*0*a^2 := by rel [n]
      _ = 0 := by ring
      _ < 7 := by numbers
      _ ≤ a^4 + 7 := by extra
      _ = a^3*a+7 := by ring
  . have h2 := le_or_succ_le a 1
    obtain l | r := h2
    . calc
        2*a^3 ≤ 2*1^3 := by rel [l]
        _ = 2 := by numbers
        _ < a^4 + 5 + 2 := by extra
        _ = a^3*a + 7 := by ring
    . calc
        2 * a^3 ≤ a*a^3 := by rel [r]
        _ < a*a^3+7 := by extra
        _ = a^3*a+7 := by ring


--Exercise 6.1.7.2

example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  simple_induction n with x IH
  . calc
      (1+a)^0 = 1 := by ring
      _ = 1 + 0*a := by ring
      _ ≥ 1+0*a := by rfl
  . have pa : 1+a ≥ 0 := by addarith [ha]
    calc
      (1+a) ^ (x+1) = (1+a) * (1+a)^x := by ring
      _ ≥ (1+a)*(1+x*a) := by rel [IH]
      _ = 1 + (x+1)*a + a^2*x := by ring
      _ ≥ 1+(x+1)*a := by extra


--Exercise 6.1.7.3

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by
  simple_induction n with k IH
  . left
    use 0
    numbers
  . obtain l | r := IH
    . right
      obtain ⟨x, hx⟩ := l
      have hx : 5^k = 8*x+1 := by addarith [hx]
      use 5*x
      conv => lhs; ring
      rw [hx]
      ring
    . left
      obtain ⟨x, hx⟩ := r
      have hx : 5^k = 8*x + 5 := by addarith [hx]
      use 5*x+3
      conv => lhs; ring
      rw [hx]
      ring
