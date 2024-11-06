import Mathlib.Tactic.GCongr
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Int

def B : ℕ → ℚ
  | 0 => 0
  | n + 1 => B n + (n + 1 : ℚ) ^ 2

example (n : ℕ) : B n = n * (n + 1) * (2 * n + 1) / 6 := by
  simple_induction n with k IH
  . rw [B]
    numbers
  . rw [B, IH]
    ring

def S : ℕ → ℚ
  | 0 => 1
  | n + 1 => S n + 1 / 2 ^ (n + 1)

example (n : ℕ) : S n = 2 - 1 / 2 ^ n := by
  simple_induction n with k IH
  . rw [S]
    numbers
  . rw [S, IH]
    ring

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

example (n : ℕ) : 0 < n ! := by
  simple_induction n with k IH
  . rw [factorial]; numbers
  . rw [factorial]; extra

example {n : ℕ} (hn : 2 ≤ n) : Nat.Even (n !) := by
  induction_from_starting_point n, hn with k hk IH
  . dsimp [factorial]
    use 1
    numbers
  . dsimp [Nat.Even, factorial] at *
    obtain ⟨q, hq⟩ := IH
    rw [hq]
    use q * (k+1)
    ring

def q : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * q (n + 1) - q n + 6 * n + 6

example (n : ℕ) : q n = (n:ℤ) ^ 3 + 1 := by
  two_step_induction n with k ih1 ih2
  . dsimp [q]; numbers
  . dsimp [q]; numbers
  . dsimp [q] at *
    rw [ih1, ih2]
    ring

def a : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | n + 2 => a (n + 1) + 2 * a n

example {m : ℕ} (hm : 1 ≤ m) : a m ≡ 1 [ZMOD 6] ∨ a m ≡ 5 [ZMOD 6] := by
  have H : ∀ n : ℕ, 1 ≤ n →
      (a n ≡ 1 [ZMOD 6] ∧ a (n+1) ≡ 5 [ZMOD 6])
    ∨ (a n ≡ 5 [ZMOD 6] ∧ a (n+1) ≡ 1 [ZMOD 6]) := by
    . intros n hn
      induction_from_starting_point n, hn with k hk ih
      . left
        dsimp [a]
        constructor
        . use 0; numbers
        . use 0; numbers
      . obtain ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩ := ih
        . right
          constructor
          . exact ih2
          . calc
              a (k+1+1) = a (k+1)+2*a k := by rw [a]
              _ ≡ 5+2*1 [ZMOD 6] := by rel [ih1, ih2]
              _ = 6*1+1 := by ring
              _ ≡ 1 [ZMOD 6] := by extra
        . left
          constructor
          . exact ih2
          . calc
              a (k+1+1) = a (k+1)+2*a k := by rw [a]
              _ ≡ 1 + 2*5 [ZMOD 6] := by rel [ih1, ih2]
              _ = 5 + 1 * 6 := by numbers
              _ ≡ 5 [ZMOD 6] := by extra
  obtain ⟨ih1, ih2⟩ | ⟨ih1, ih2⟩ := H m hm
  . left
    exact ih1
  . right
    exact ih1
