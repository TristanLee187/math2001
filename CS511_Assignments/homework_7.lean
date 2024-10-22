import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel
import AutograderLib

math2001_init
set_option pp.funBinderTypes true

--Exercise 5.1.7.6

@[autograded 2]
example {P Q R : Prop} (h : P ↔ Q) : (P ∧ R) ↔ (Q ∧ R) := by
  obtain ⟨pq, qp⟩ := h
  constructor
  . intros par
    obtain ⟨p, r⟩ := par
    constructor
    . apply pq p
    . exact r
  . intros qar
    obtain ⟨q, r⟩ := qar
    constructor
    . apply qp q
    . exact r

--Exercise 5.1.7.8

@[autograded 2]
example (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  . intros poq
    obtain p | q := poq
    . right; exact p
    . left; exact q
  . intros qop
    obtain q | p := qop
    . right; exact q
    . left; exact p

--Exercise 5.1.7.9

@[autograded 2]
example (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  . intros npoq
    constructor
    . intros p
      have poq : P ∨ Q := by left; exact p
      contradiction
    . intros q
      have poq : P ∨ Q := by right; exact q
      contradiction
  . intros npanq poq
    obtain ⟨np, nq⟩ := npanq
    obtain p | q := poq
    . contradiction
    . contradiction

--Exercise 5.1.7.11

@[autograded 2]
example {P Q : α → Prop} (h : ∀ x, P x ↔ Q x) : (∃ x, P x) ↔ (∃ x, Q x) := by
  constructor
  . intros epx
    obtain ⟨x, px⟩ := epx
    have piffq : P x ↔ Q x := by apply h x
    use x
    obtain ⟨pq, qp⟩ := piffq
    apply pq px
  . intros eqx
    obtain ⟨x, qx⟩ := eqx
    have piffq : P x ↔ Q x := by apply h x
    use x
    obtain ⟨pq, qp⟩ := piffq
    apply qp qx

--Exercise 5.1.7.12

@[autograded 2]
example (P : α → β → Prop) : (∃ x y, P x y) ↔ ∃ y x, P x y := by
  constructor
  . intros pxy
    obtain ⟨x, y, pxy⟩ := pxy
    use y
    use x
    exact pxy
  . intros pyx
    obtain ⟨y, x, pyx⟩ := pyx
    use x
    use y
    exact pyx

--Exercise 5.1.7.13

@[autograded 2]
example (P : α → β → Prop) : (∀ x y, P x y) ↔ ∀ y x, P x y := by
  constructor
  . intros pxy
    intros y x
    apply pxy x y
  . intros pyx
    intros x y
    apply pyx y x

--Exercise 5.1.7.14

@[autograded 3]
example (P : α → Prop) (Q : Prop) : ((∃ x, P x) ∧ Q) ↔ ∃ x, (P x ∧ Q) := by
  constructor
  . intros px
    obtain ⟨px, q⟩ := px
    obtain ⟨x, px⟩ := px
    use x
    constructor
    . exact px
    . exact q
  . intros px
    obtain ⟨x, px, q⟩ := px
    constructor
    . use x
      exact px
    . exact q

--Exercise 5.2.7.2

@[autograded 3]
example (P Q : Prop) : (¬P → ¬Q) ↔ (Q → P) := by
  constructor
  . intros npnq q
    by_cases pnp : P
    . exact pnp
    . have nq : ¬ Q := by apply npnq pnp
      contradiction
  . intros qp np
    by_cases qnq : Q
    . have p : P := by apply qp qnq
      contradiction
    . exact qnq
