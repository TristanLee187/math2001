import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Tactic.ModEq

math2001_init

/-# Exercise 3-/

--Exercise 10.1.5.4

section
local infix:50 "∼" => fun (x y : ℤ) ↦ y ≡ x + 1 [ZMOD 5]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp
  dsimp [Reflexive] at *
  push_neg
  use 0
  intros add
  numbers at add

example : Symmetric (· ∼ ·) := by
  sorry

example : ¬ Symmetric (· ∼ ·) := by
  dsimp
  dsimp [Symmetric] at *
  push_neg
  use 0, 1
  constructor <;> numbers

example : AntiSymmetric (· ∼ ·) := by
  dsimp
  dsimp [AntiSymmetric] at *
  intros x y h1 h2
  dsimp [Int.ModEq] at *
  have contra1 : Int.ofNat 5 ∣ Int.ofNat 2 := by
    dsimp [Int.ofNat] at *
    obtain ⟨k, hk⟩ := h1
    obtain ⟨q, hq⟩ := h2
    use -(k+q)
    calc
      2=-(y-(x+1) + (x-(y+1))) := by ring
      _ = -(5*k + (x-(y+1))) := by rw [hk]
      _ = -(5*k + (5*q)) := by rw [hq]
      _ = 5 * -(k+q) := by ring
  have two : 0 < (Int.ofNat 2) := by extra
  have contra2 : Int.ofNat 5 ≤ 2 := by
    apply Int.le_of_dvd two contra1
  numbers at contra2

example : ¬ AntiSymmetric (· ∼ ·) := by
  sorry

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp
  dsimp [Transitive] at *
  push_neg
  use 0, 1, 2
  constructor
  . numbers
  . constructor <;> numbers

end

/-# Exercise 4-/

--Exercise 10.1.5.5

section
local infix:50 "∼" => fun (x y : ℤ) ↦ x + y ≡ 0 [ZMOD 3]

example : Reflexive (· ∼ ·) := by
  sorry

example : ¬ Reflexive (· ∼ ·) := by
  dsimp
  dsimp [Reflexive] at *
  push_neg
  use 1
  numbers

example : Symmetric (· ∼ ·) := by
  dsimp
  dsimp [Symmetric] at *
  intros x y hxy
  calc
    y+x = x+y := by ring
    _ ≡ 0 [ZMOD 3] := by rel [hxy]

example : ¬ Symmetric (· ∼ ·) := by
  sorry

example : AntiSymmetric (· ∼ ·) := by
  sorry

example : ¬ AntiSymmetric (· ∼ ·) := by
  dsimp
  dsimp [AntiSymmetric] at *
  push_neg
  use 1, 2
  constructor
  . calc
      1+2 = 3 := by numbers
      _ ≡ 0 [ZMOD 3] := by use 1; numbers
  . constructor
    . calc
        2+1 = 3 := by numbers
        _ ≡ 0 [ZMOD 3] := by use 1; numbers
    . numbers

example : Transitive (· ∼ ·) := by
  sorry

example : ¬ Transitive (· ∼ ·) := by
  dsimp
  dsimp [Transitive] at *
  push_neg
  use 1, 2, 1
  constructor
  . calc
      1+2 = 3 := by numbers
      _ ≡ 0 [ZMOD 3] := by use 1; numbers
  . constructor
    . calc
        2+1 = 3 := by numbers
        _ ≡ 0 [ZMOD 3] := by use 1; numbers
    . numbers

end

/-# Problem 2-/

--Exercise 10.1.5.6

example : Reflexive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Reflexive]
  dsimp [Set.subset_def] at *
  intros x x1 hx
  exact hx

example : ¬ Reflexive ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Symmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : ¬ Symmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [Symmetric]
  push_neg
  use {}, {1}
  constructor
  . dsimp [Set.subset_def]
    intros x f
    contradiction
  . dsimp [Set.subset_def]
    push_neg
    use 1
    trivial

example : AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  dsimp [AntiSymmetric]
  intros x y hxy hyx
  dsimp [Set.subset_def] at *
  ext n
  constructor
  . intros hn
    apply hxy n
    exact hn
  . intros hn
    apply hyx n
    exact hn

example : ¬ AntiSymmetric ((· : Set ℕ) ⊆ ·) := by
  sorry

example : Transitive ((· : Set ℕ) ⊆ ·) := by
  dsimp [Transitive]
  intros x y z hxy hyz
  dsimp [Set.subset_def] at *
  intros a ha
  have := hxy a ha
  apply hyz a
  exact this

example : ¬ Transitive ((· : Set ℕ) ⊆ ·) := by
  sorry
