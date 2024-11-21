import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Exhaust
import Library.Theory.InjectiveSurjective
import Library.Tactic.ModEq

math2001_init
set_option pp.funBinderTypes true

open Function

/-# Exercise 3-/

--Exercise 8.3.10.2

def u (x : ℝ) : ℝ := 5 * x + 1

noncomputable def v (x : ℝ) : ℝ := (x-1)/5

example : Inverse u v := by
  dsimp [Inverse]
  constructor <;>
  . ext x
    dsimp
    rw [u, v]
    ring

--Exercise 8.3.10.3

example {f : X → Y} (hf : Injective f) {g : Y → Z} (hg : Injective g) :
    Injective (g ∘ f) := by
  dsimp [Injective] at *
  intros a b gof
  apply hg at gof
  apply hf at gof
  exact gof

--Exercise 8.3.10.4

example {f : X → Y} (hf : Surjective f) {g : Y → Z} (hg : Surjective g) :
    Surjective (g ∘ f) := by
  dsimp [Surjective] at *
  intros z
  have gy := by apply hg z
  obtain ⟨y, gy⟩ := gy
  have fx := by apply hf y
  obtain ⟨x, fx⟩ := fx
  use x
  rw [fx, gy]


/-# Exercise 4-/

--Exercise 8.4.10.1

example : Bijective (fun ((r, s) : ℚ × ℚ) ↦ (s, r - s)) := by
  rw [bijective_iff_exists_inverse]
  use fun (a,b) ↦ (a+b, a)
  dsimp [Inverse]
  constructor <;>
  . ext ⟨r, s⟩
    dsimp
    ring

--Exercise 8.4.10.2.1

example : ¬ Injective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Injective]
  push_neg
  use (0,0)
  use (2,1)
  constructor <;> numbers

--Exercise 8.4.10.2.2

example : Surjective (fun ((x, y) : ℤ × ℤ) ↦ x - 2 * y - 1) := by
  dsimp [Surjective]
  intros b
  use (3*b+1, b)
  ring

/-# Problem 2-/

--Exercise 8.3.10.5

example {f : X → Y} (hf : Surjective f) : ∃ g : Y → X, f ∘ g = id := by
  dsimp [Surjective] at hf
  choose g hg using hf
  use g
  ext b
  dsimp
  rw [hg]

--Exercise 8.3.10.7

example {f : X → Y} {g1 g2 : Y → X} (h1 : Inverse f g1) (h2 : Inverse f g2) :
    g1 = g2 := by
  dsimp [Inverse] at *
  ext y
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  calc
    g1 y = id (g1 y) := by rfl
    _ = (g2 ∘ f) (g1 y) := by rw [h2l]
    _ = g2 ((f ∘ g1) y) := by rfl
    _ = g2 (id y) := by rw [h1r]
    _ = g2 y := by rfl
