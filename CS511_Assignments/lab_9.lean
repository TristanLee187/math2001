import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

namespace Nat

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  simple_induction n with k IH
  . apply Int.ModEq.pow; exact h
  . apply Int.ModEq.pow; exact h

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  simple_induction n with k IH
  . left
    dsimp [Int.ModEq]
    use 0
    numbers
  . dsimp [Int.ModEq] at *
    obtain ih1 | ih2 := IH
    . right
      obtain ⟨m, hm⟩ := ih1
      use 6*m
      calc
        6^(k+1)-6 = 6*(6^k - 1) := by ring
        _ = 6*(7*m) := by rw [hm]
        _ = 7*(6*m) := by ring
    . left
      obtain ⟨m, hm⟩ := ih2
      have hm' : 6^k=7*m+6 := by addarith [hm]
      use 6*m+5
      calc
        6^(k+1)-1 = 6*6^k - 1 := by ring
        _ = 6*(7*m+6)-1 := by rw [hm']
        _ = 7*(6*m+5) := by ring


example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by
  simple_induction n with k IH
  . left
    use 0
    numbers
  . obtain ih1 | ih2 | ih3 := IH
    . right; right
      obtain ⟨m, hm⟩ := ih1
      have hm' : 4^k = 7*m+1 := by addarith [hm]
      conv => lhs; ring
      rw [hm']
      use 4*m
      ring
    . left
      obtain ⟨m, hm⟩ := ih2
      have hm' : 4^k = 7*m+2 := by addarith [hm]
      conv => lhs; ring
      rw [hm']
      use 4*m+1
      ring
    . right; left
      obtain ⟨m, hm⟩ := ih3
      have hm' : 4^k = 7*m+4 := by addarith [hm]
      conv => lhs; ring
      rw [hm']
      use 4*m+2
      ring


theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by
  simple_induction n with k ih
  . dsimp [Odd] at *
    obtain ⟨m, hm⟩ := ha
    use 0
    numbers
  . dsimp [Odd] at *
    obtain ⟨m, hm⟩ := ha
    obtain ⟨p, hp⟩ := ih
    use m*2*p+m+p
    conv => lhs; ring; rw [hp, hm]
    ring

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by
  dsimp
  use 5
  intros x hx
  induction_from_starting_point x, hx with k hk ih
  . numbers
  . sorry

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  sorry
