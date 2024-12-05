import Library.Basic
import Library.Tactic.ModEq
import Library.Tactic.Exhaust

math2001_init

open Set Function Nat

/-# Exercise 4-/

--Exercise 6.4.3.1

theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by
  obtain ne|no := even_or_odd n
  . dsimp [Even] at ne
    obtain ⟨k, hk⟩ := ne
    have ih := extract_pow_two k
    rw [hk] at hn
    cancel 2 at hn
    apply ih at hn
    obtain ⟨a, x, hax⟩ := hn
    obtain ⟨xo, hax⟩ := hax
    use a+1, x
    constructor
    . exact xo
    . calc
        n = 2*k := hk
        _ = 2*(2^a*x) := by rw [hax]
        _ = 2^(a+1)*x := by ring
  . use 0, n
    constructor
    . exact no
    . ring

/-# Exercise 5-/

------------------------------------------------------------------------------------
--Exercise 9.1.10.1

example : 4 ∈ {a : ℚ | a < 3} := by
  sorry

example : 4 ∉ {a : ℚ | a < 3} := by
  dsimp
  numbers

------------------------------------------------------------------------------------
--Exercise 9.1.10.2

example : 6 ∈ {n : ℕ | n ∣ 42} := by
  dsimp
  use 7
  numbers

example : 6 ∉ {n : ℕ | n ∣ 42} := by
  sorry

------------------------------------------------------------------------------------
--Exercise 9.1.10.3

example : 8 ∈ {k : ℤ | 5 ∣ k} := by
  sorry

example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  dsimp
  apply Int.not_dvd_of_exists_lt_and_lt
  use 1
  constructor <;> numbers


/-# Exercise 6-/
------------------------------------------------------------------------------------
--Exercise 9.1.10.6

example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by
  dsimp [Set.subset_def]
  intros x hx
  dsimp [(.∣.)] at hx
  obtain ⟨c, hc⟩ := hx
  use 4*c
  rw [hc]
  ring

example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
  sorry

------------------------------------------------------------------------------------
--Exercise 9.1.10.7

example : {a : ℕ | 5 ∣ a} ⊆ {x : ℕ | 20 ∣ x} := by
  sorry

example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  dsimp [Set.subset_def]
  push_neg
  use 5
  constructor
  . use 1; numbers
  . apply Nat.not_dvd_of_exists_lt_and_lt
    use 0
    constructor <;> numbers

------------------------------------------------------------------------------------
--Exercise 9.2.8.5

example : {r : ℤ | r ≡ 7 [ZMOD 10] }
    ⊆ {s : ℤ | s ≡ 1 [ZMOD 2]} ∩ {t : ℤ | t ≡ 2 [ZMOD 5]} := by
  dsimp [Set.subset_def]
  intros x hx
  dsimp [Int.ModEq] at *
  dsimp [(.∣.)] at hx
  obtain ⟨c, hc⟩ := hx
  constructor
  . use 5*c+3
    calc
      x-1 = x-7+6 := by ring
      _ = (10*c) + 6 := by rw [hc]
      _ = 2*(5*c+3) := by ring
  . use 2*c+1
    calc
      x-2 = x-7+5 := by ring
      _ = (10*c) + 5 := by rw [hc]
      _ = 5*(2*c+1) := by ring

/-# Problem 2-/

--Exercise 9.2.8.6

-- Gauss's lemma
theorem gauss_lemma {d a b : ℤ} (h1 : d ∣ a * b) (h2 : Int.gcd a d = 1) : d ∣ b := by
  sorry

example : {n : ℤ | 5 ∣ n} ∩ {n : ℤ | 8 ∣ n} ⊆ {n : ℤ | 40 ∣ n} := by
  dsimp [Set.subset_def]
  intros x hx
  obtain ⟨hx5, hx8⟩ := hx
  dsimp [(.∣.)] at *
  obtain ⟨a, ha⟩ := hx5
  obtain ⟨b, hb⟩ := hx8
  have five_div_8b : 5 ∣ 8*b := by
    have ab :=
      calc
        5*a = x := by rw [ha]
        _ = 8*b := by rw [hb]
    use a
    rw [ab]
  have gcd58 : Int.gcd 5 8 = 1 := by
    exhaust
  have five_div_b : 5∣b := by
    apply gauss_lemma
    . exact five_div_8b
    . exact gcd58
  dsimp [(.∣.)] at five_div_b
  obtain ⟨c, hc⟩ := five_div_b
  use c
  rw [hc] at hb
  calc
    x = 8*(5*c) := hb
    _ = 40*c := by ring


--Exercise 9.3.6.1

def r (s : Set ℕ) : Set ℕ := s ∪ {3}

example : ¬ Injective r := by
  dsimp [Injective]
  push_neg
  use ∅, {3}
  dsimp [r]
  constructor
  . ext n
    dsimp
    exhaust
  . push_neg
    dsimp [Set.Nonempty]
    use 3
    numbers
