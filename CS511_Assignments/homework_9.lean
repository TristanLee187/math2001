import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

--# Exercise 3

--Exercise 6.2.7.1
def c : ℕ → ℤ
  | 0 => 7
  | n + 1 => 3 * c n - 10

example (n : ℕ) : Odd (c n) := by
  simple_induction n with k ih
  . dsimp [c]
    use 3
    numbers
  . dsimp [Odd] at *
    obtain ⟨q, hq⟩ := ih
    dsimp [c] at *
    use 3*q-4
    rw [hq]; ring

--Exercise 6.2.7.2
example (n : ℕ) : c n = 2 * 3 ^ n + 5 := by
  simple_induction n with k ih
  . dsimp [c]
    numbers
  . dsimp [c] at *
    rw [ih]
    ring

--Exercise 6.2.7.3
def y : ℕ → ℕ
  | 0 => 2
  | n + 1 => (y n) ^ 2

example (n : ℕ) : y n = 2 ^ (2 ^ n) := by
  simple_induction n with k ih
  . dsimp [y]
    numbers
  . dsimp [y]
    rw [ih]
    ring

--# Exercise 4

--Exercise 6.3.6.1
def b : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => 5 * b (n + 1) - 6 * b n

example (n : ℕ) : b n = 3 ^ n - 2 ^ n := by
  two_step_induction n with k ih1 ih2
  . dsimp [b]
    numbers
  . dsimp [b]
    numbers
  . dsimp [b]
    rw [ih1, ih2]
    ring

--Exercise 6.3.6.2
def c' : ℕ → ℤ
  | 0 => 3
  | 1 => 2
  | n + 2 => 4 * c' n

example (n : ℕ) : c' n = 2 * 2 ^ n + (-2) ^ n := by
  two_step_induction n with k ih1 ih2
  . dsimp [c']
    numbers
  . dsimp [c']
    numbers
  . dsimp [c']
    rw [ih1]
    ring

--Exercise 6.3.6.3
def t : ℕ → ℤ
  | 0 => 5
  | 1 => 7
  | n + 2 => 2 * t (n + 1) - t n

example (n : ℕ) : t n = 2 * n + 5 := by
  two_step_induction n with k ih1 ih2
  . dsimp [t]
    numbers
  . dsimp [t]
    numbers
  . dsimp [t]
    rw [ih1, ih2]
    ring

--# Problem 2

--Exercise 6.3.6.5
def s : ℕ → ℤ
  | 0 => 2
  | 1 => 3
  | n + 2 => 2 * s (n + 1) + 3 * s n

example (m : ℕ) : s m ≡ 2 [ZMOD 5] ∨ s m ≡ 3 [ZMOD 5] := by
  have ss : (s m ≡ 2 [ZMOD 5] ∧ s (m+1) ≡ 3 [ZMOD 5]) ∨
    (s m ≡ 3 [ZMOD 5] ∧ s (m+1) ≡ 2 [ZMOD 5]) := by
      two_step_induction m with k ih1 ih2
      . dsimp [s]
        left
        constructor
        . use 0; numbers
        . use 0; numbers
      . dsimp [s]
        right
        . constructor
          . use 0; numbers
          . use 2; numbers
      . obtain ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩ := ih1
        . left
          constructor
          . dsimp [s]
            calc
              2 * s (k + 1) + 3 * s k ≡ 2 * 3 + 3 * 2 [ZMOD 5] := by rel [ih1, ih2]
              _ = 2+2*5 := by numbers
              _ ≡ 2 [ZMOD 5] := by extra
          . dsimp [s]
            calc
              2 * (2 * s (k + 1) + 3 * s k) + 3 * s (k + 1) ≡ 2*(2*3+3*2)+3*3 [ZMOD 5] := by rel [ih1, ih2]
              _ = 3 + 6*5 := by numbers
              _ ≡ 3 [ZMOD 5] := by extra
        . right
          constructor
          . dsimp [s]
            calc
              2 * s (k + 1) + 3 * s k ≡ 2 * 2 + 3 * 3 [ZMOD 5] := by rel [ih1, ih2]
              _ = 3+2*5 := by numbers
              _ ≡ 3 [ZMOD 5] := by extra
          . dsimp [s]
            calc
              2 * (2 * s (k + 1) + 3 * s k) + 3 * s (k + 1) ≡ 2*(2*2+3*3)+3*2 [ZMOD 5] := by rel [ih1, ih2]
              _ = 2 + 6*5 := by numbers
              _ ≡ 2 [ZMOD 5] := by extra
  obtain ⟨a, b⟩ | ⟨c, d⟩ := ss
  . left; exact a
  . right; exact c


--Exercise 6.3.6.7
def r : ℕ → ℤ
  | 0 => 2
  | 1 => 0
  | n + 2 => 2 * r (n + 1) + r n

example : forall_sufficiently_large n : ℕ, r n ≥ 2 ^ n := by
  use 10
  intros x hx
  two_step_induction_from_starting_point x, hx with k ih1 ih2 ih3
  . dsimp [r]; numbers
  . dsimp [r]; numbers
  . dsimp [r]
    calc
      2 * r (k + 1) + r k ≥ 2 * (2^(k+1)) + 2^k := by rel [ih2, ih3]
      _ ≥ 2 * (2^(k+1)) := by extra
      _ = 2^(k+1+1) := by ring
