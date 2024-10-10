import Library.Basic
import Library.Theory.ModEq.Defs
import AutograderLib

math2001_init

/- # The first three are theorems provided in MoP Section 3.3 -/

theorem Int.ModEq.add {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x + y
  calc
    a + c - (b + d) = a - b + (c - d) := by ring
    _ = n * x + n * y := by rw [hx, hy]
    _ = n * (x + y) := by ring

theorem Int.ModEq.mul {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use x * c + b * y
  calc
    a * c - b * d = (a - b) * c + b * (c - d) := by ring
    _ = n * x * c + b * (n * y) := by rw [hx, hy]
    _ = n * (x * c + b * y) := by ring

theorem Int.ModEq.refl (a : ℤ) : a ≡ a [ZMOD n] := by
  use 0
  ring

@[autograded 2]
theorem Int.ModEq.sub {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a - c ≡ b - d [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  use k-l
  calc
    a-c-(b-d) = a-b-(c-d) := by ring
    _ = n*k - n*l := by rw [hk, hl]
    _ = n*(k-l) := by ring

@[autograded 2]
theorem Int.ModEq.neg {n a b : ℤ} (h1 : a ≡ b [ZMOD n]) : -a ≡ -b [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨k, hk⟩ := h1
  use -k
  calc
    -a - -b = -(a-b) := by ring
    _ = -(n*k) := by rw [hk]
    _ = n*-k := by ring

@[autograded 2]
theorem Int.ModEq.symm (h : a ≡ b [ZMOD n]) : b ≡ a [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨k, hk⟩ := h
  use -k
  calc
    b-a = -(a-b) := by ring
    _ = -(n*k) := by rw [hk]
    _ = n*-k := by ring

@[autograded 2]
theorem Int.ModEq.trans (h1 : a ≡ b [ZMOD n]) (h2 : b ≡ c [ZMOD n]) :
    a ≡ c [ZMOD n] := by
  dsimp [Int.ModEq] at *
  obtain ⟨k, hk⟩ := h1
  obtain ⟨l, hl⟩ := h2
  use k+l
  calc
    a-c = a-b+(b-c) := by ring
    _ = n*k+n*l := by rw [hk, hl]
    _ = n*(k+l) := by ring

/- # You may use any of the Int.ModEq Lemmas if you wish on this problem. -/

@[autograded 2]
theorem exercise_3_3_12_6 {a b : ℤ} (h : a ≡ b [ZMOD 5]) : 2 * a + 3 ≡ 2 * b + 3 [ZMOD 5] := by
  apply Int.ModEq.add
  apply Int.ModEq.mul
  apply Int.ModEq.refl
  apply h
  apply Int.ModEq.refl

@[autograded 2]
theorem exercise_4_3_5_2 : ∃! n : ℕ, ∀ a, n ≤ a := by
  use 0
  dsimp
  constructor
  . intro m
    extra
  . intro m hm
    apply le_antisymm
    apply hm
    extra

@[autograded 6]
theorem unique_inv {G : Type*} [Group G] (e : G)
(hId : ∀ a : G, e * a = a ∧ a * e = a)
(hInv : ∀ a : G, ∃ b : G, a * b = e ∧ b * a = e)
(hAssoc : ∀ a : G, ∀ b : G, ∀ c : G, (a * b) * c = a * (b * c))
: ∀ a : G, ∃! b : G, a * b = e ∧ b * a = e := by
  intro a
  have ainv : ∃ b : G, a * b = e ∧ b * a = e := by apply hInv
  obtain ⟨ai, hai⟩ := ainv
  obtain ⟨hai1, hai2⟩ := hai
  use ai
  dsimp
  constructor
  . constructor
    . apply hai1
    . apply hai2
  . intro y hyi
    obtain ⟨hyi1, hyi2⟩ := hyi
    have yId : e * y = y ∧ y * e = y := by apply hId
    obtain ⟨yleft, yright⟩ := yId
    have yaai : (y*a)*ai = y*(a*ai) := by apply hAssoc
    have aiId : e * ai = ai ∧ ai * e = ai := by apply hId
    obtain ⟨aileft, airight⟩ := aiId
    calc
      y = y*e := by rw [yright]
      _ = y*(a*ai) := by rw [hai1]
      _ = (y*a)*ai := by rw [yaai]
      _ = e*ai := by rw [hyi2]
      _ = ai := by rw [aileft]
