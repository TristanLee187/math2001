import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

/-# Extra Problems from Chapter 5-/

example {P Q : Prop} (h : P ∧ Q) : P ∨ Q := by
  obtain ⟨hp, hq⟩ := h
  left
  exact hp

example {P Q R : Prop} (h1 : P → Q) (h2 : P → R) (h3 : P) : Q ∧ R := by
  constructor
  . apply h1 h3
  . apply h2 h3

example (P : Prop) : ¬(P ∧ ¬ P) := by
  intros hp
  obtain ⟨p, np⟩ := hp
  contradiction

example {P Q : Prop} (h1 : P ↔ ¬ Q) (h2 : Q) : ¬ P := by
  obtain ⟨f, b⟩ := h1
  intros hp
  apply f hp
  exact h2

example {P Q : Prop} (h1 : P ∨ Q) (h2 : Q → P) : P := by
  obtain hp | hq := h1
  . exact hp
  . apply h2 hq

example {P Q : α → Prop} (h1 : ∀ x, P x → Q x) (h2 : ∀ x, P x) : ∀ x, Q x := by
  intros x
  apply h1 x
  apply h2 x

/-# Problems from Homework 5-/

theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (Classical.em p)
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

example {x y : ℕ} (h : y = 0 ∧ y = x) : 0 = x := by
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2
  exact h2

example {t1 t2 t : ℕ} (h : t1 = t2) : (t + t1) = (t + t2) := by
  have h1 : (t+t1) = (t+t1) := by rfl
  conv =>
    lhs
    rw [h]

example {S : Prop} {Q : Type → Prop} (h : ∃x, (S → Q x)) : S → ∃x , Q x := by
  obtain ⟨x, hx⟩ := h
  intro a
  use x
  apply hx a

example {x : Type} {S : Prop} {P : Type → Prop} (h : ∀x, P x → S) : ∃x, (P x → S) := by
  have h' : P x → S := h x
  use x
  exact h'

/-# Problems from Homework 7-/

example {P : Type → Type → Prop} (h1 : ∀x, ∀y, ∀z, P x y ∧ P y z → P x z)
  (h2 : ∀x, ∀y, P x y → P y x) : ∀x, ∀y, ∀z, P x y ∧ P z y → P x z := by
  intros x y z h
  obtain ⟨hxy, hzy⟩ := h
  apply h2 at hzy
  apply h1 x y z ⟨hxy, hzy⟩

example {Q : Type → Type → Type → Prop} {s : Type → Type} {a : Type} (h1 : ∀x, Q a x x)
  (h2 : ∀x, ∀y, ∀z, Q x y z → Q x (s y) (s z)) (h3 : ∀x, ∀y, ∀z, Q x y z → Q y x z)
  : ∃x : Type, Q (s (s a)) (s (s (s a))) x := by
  use s (s (s (s (s a))))
  have h4 := h1 a
  have h5 := h2 a a a h4
  have h6 := h2 a (s a) (s a) h5
  have h7 := h3 a (s (s a)) (s (s a)) h6
  have h8 := h2 (s (s a)) a (s (s a)) h7
  have h9 := h2 (s (s a)) (s a) (s (s (s a))) h8
  have h10 := h2 (s (s a)) (s (s a)) (s (s (s (s a)))) h9
  exact h10
