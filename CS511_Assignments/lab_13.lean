import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust
import Mathlib.Tactic.GCongr

math2001_init

open Set Function Nat

def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

theorem F_bound (n : ℕ) : F n ≤ 2 ^ n := by
  match n with
  | 0 =>
    calc
      F 0 = 1 := by rw [F]
      _ ≤ 2^0 := by numbers
  | 1 =>
    calc
      F 1 = 1 := by rw [F]
      _ ≤ 2^1 := by numbers
  | k+2 =>
    have ih1 := F_bound k
    have ih2 := F_bound (k+1)
    calc
      F (k+2) = F (k+1) + F k := by rw [F]
      _ ≤ 2^(k+1) + 2^k := by rel [ih1, ih2]
      _ ≤ 2^(k+1) + 2^k + 2^k := by extra
      _ = 2^(k+2) := by ring

namespace Nat
theorem exists_prime_factor {n : ℕ} (hn2 : 2 ≤ n) : ∃ p : ℕ, Prime p ∧ p ∣ n := by
  by_cases hn : Prime n
  . use n
    constructor
    . exact hn
    . use 1; ring
  . obtain ⟨m, hmn, _, ⟨x, hx⟩⟩ := exists_factor_of_not_prime hn hn2
    have ih : ∃ p, Prime p ∧ p ∣ m := exists_prime_factor hmn
    obtain ⟨p, hp, y, hy⟩ := ih
    use p
    constructor
    . exact hp
    . use y*x
      calc
        n = m*x := by rw [hx]
        _ = (p*y)*x := by rw [hy]
        _ = p*(y*x) := by ring

end Nat

example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  constructor
  · intro h
    obtain (h | h) | (h | h) := h
    · left
      apply h
    · right
      left
      apply h
  -- and much, much more
    · right; left; apply h
    · right; right; apply h
  · intro h
    obtain h | h | h := h
    · left; left; apply h
    · left; right; apply h
    · right; right; apply h

example : {1, 2} ∪ {2, 4} = {1, 2, 4} := by
  ext n
  dsimp
  exhaust

example : {-2, 3} ∩ {x : ℚ | x ^ 2 = 9} ⊆ {a : ℚ | 0 < a} := by
  dsimp [Set.subset_def]
  intros t h
  obtain ⟨⟨h1 | h1⟩, h2⟩ := h
  . have :=
    calc
      4 = (-2) ^ 2 := by numbers
      _ = 9 := by sorry
    numbers at this
  . sorry


example : {n : ℕ | 4 ≤ n} ∩ {n : ℕ | n < 7} ⊆ {4, 5, 6} := by
  dsimp [Set.subset_def]
  intros n h
  obtain ⟨h1, h2⟩ := h
  interval_cases n <;> exhaust

namespace Int
example : {n : ℤ | Even n}ᶜ = {n : ℤ | Odd n} := by
  ext n
  dsimp
  rw [odd_iff_not_even]
end Int

example (x : ℤ) : x ∉ ∅ := by
  dsimp
  exhaust

example (U : Set ℤ) : ∅ ⊆ U := by
  dsimp [Set.subset_def]
  intros x f
  contradiction

example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  constructor
  . intro hx
    obtain ⟨l, r⟩ := hx
    have :=
    calc
      1 ≡ x [ZMOD 5] := by rel [l]
      _ ≡ 2 [ZMOD 5] := by rel [r]
    numbers at this
  . intros hx
    contradiction

example : {n : ℤ | n ≡ 1 [ZMOD 5]} ∩ {n : ℤ | n ≡ 2 [ZMOD 5]} = ∅ := by
  ext x
  dsimp
  suffices ¬(x ≡ 1 [ZMOD 5] ∧ x ≡ 2 [ZMOD 5]) by exhaust
  intro hx
  obtain ⟨l, r⟩ := hx
  have :=
  calc
    1 ≡ x [ZMOD 5] := by rel [l]
    _ ≡ 2 [ZMOD 5] := by rel [r]
  numbers at this
