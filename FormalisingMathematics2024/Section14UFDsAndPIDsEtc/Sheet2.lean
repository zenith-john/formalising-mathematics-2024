/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Algebra.EuclideanDomain.Instances
import Mathlib.Data.Polynomial.FieldDivision
-- polynomial rings over a field are EDs

/-

# Euclidean Domains

Lean's definition of a Euclidean domain is more general than the usual one presented
to undergraduates. First things first: here's how to say "let R be a Euclidean domain"

-/

section Section14Sheet2

variable (R : Type) [EuclideanDomain R]

/-

And there's various theorems (all known by the typeclass inference system) about
Euclidean domains:

-/

example : EuclideanDomain ℤ := by infer_instance

open scoped Polynomial

-- I neither know nor care why it's noncomputable, but it doesn't matter to mathematicians
noncomputable example (k : Type) [Field k] : EuclideanDomain k[X] :=
  inferInstance

-- Euclidean domains are PIDs
example (R : Type) [EuclideanDomain R] : IsPrincipalIdealRing R :=
  inferInstance

example (R : Type) [EuclideanDomain R] : IsDomain R :=
  inferInstance

/-

Internally the definition of a Euclidean domain is this. It's a ring with the following
structure/axioms:

1) You have a "quotient" function `quotient r s` and a remainder function `remainder r s`,
both of type `R → R → R` (i.e. functions from `R²` to `R`)

2) You have an axiom saying `∀ a b, a = b * quotient a b + remainder a b`

3) You have a binary relation `≺` on the ring such that `remainder a b ≺ b`

4) You have an axiom saying that `≺` is well-founded, i.e., there are no infinite decreasing
sequences.

The point is that these axioms are enough to get Euclid's algorithm to work.

In usual maths you have a function from `R` to `ℕ` sending an element `b` to its "size",
and an axiom saying that the remainder when you divide something by `b` is sent to a smaller
natural number. In Lean the natural numbers are not involved; all that we guarantee is
that you can't keep taking remainders infinitely often, which turns out to be a very slightly
weaker statement. Let's prove that any "normal" Euclidean domain is a mathlib Euclidean domain.

-/

noncomputable example (R : Type) [CommRing R] [IsDomain R] (φ : R → ℕ)
    (h : ∀ a b : R, b ≠ 0 → ∃ q r : R, a = b * q + r ∧ (r = 0 ∨ φ r < φ b))
    (h0 : ∀ a b : R, a ≠ 0 → b ≠ 0 → φ a ≤ φ (a * b)) :
    EuclideanDomain R := by
  classical
  let φ' : R → ℕ := fun r => if r = 0 then 0 else 1 + φ r
  have h' (a b : R) : ∃ q r : R,
    a = b * q + r ∧ (b = 0 ∧ q = 0 ∧ r = a ∨ b ≠ 0 ∧ φ' r < φ' b)
  · by_cases hb: b ≠ 0
    have hb2:= hb
    specialize h a b
    apply h at hb
    obtain ⟨q,r,hr⟩ := hb
    use q
    use r
    constructor
    exact hr.1
    right
    refine ⟨hb2, ?_⟩
    cases' hr.2 with hl hR
    · specialize h0 b q hb2
      rw[hl]
      have hp: φ' 0 = 0 := by exact if_pos rfl
      rw[hp]
      have hp: φ' b = 1 + φ b := by exact if_neg hb2
      rw[hp]
      simp
    · have hp: φ' b = 1 + φ b := by exact if_neg hb2
      rw[hp]
      by_cases hr:r=0
      have hp: φ' r = 0 := by exact if_pos hr
      rw[hp]
      simp
      have hp: φ' r = 1 + φ r := by exact if_neg hr
      rw[hp]
      simp
      exact hR
    · have hb:b=0 := by by_contra hp; apply hb;exact hp
      use 0
      use a
      constructor
      norm_num
      left
      exact ⟨hb, rfl, rfl⟩

  choose quot rem h'' using h'
  exact
    { quotient := quot
      quotient_zero := by
        intro a
        specialize h'' a 0
        obtain ⟨_, hc⟩ := h''
        cases' hc with hd he
        exact hd.2.1
        by_contra
        obtain ⟨hf, _⟩ := he
        exact hf rfl
      remainder := rem
      quotient_mul_add_remainder_eq := by
        intro a b
        specialize h'' a b
        have h1: a = b * quot a b + rem a b := by exact h''.left
        rw[← h1]

      r := fun a b => φ' a < φ' b
      r_wellFounded := by refine WellFounded.onFun ?_; exact wellFounded_lt
      remainder_lt := by
        intro a b hb
        specialize h'' a b
        obtain ⟨_, hc⟩ := h''
        cases' hc with hd he
        obtain ⟨hf, _, _⟩ := hd
        by_contra
        apply hb
        exact hf
        exact he.2
      mul_left_not_lt := by
        intro a b hb
        specialize h0 a b
        by_contra hp
        by_cases ha:a=0
        rw[ha] at hp
        rw[zero_mul] at hp
        exact LT.lt.false hp

        have hr: φ' a = 1 + φ a := by exact if_neg ha
        have hq: φ' (a * b) = 1 + φ (a * b) := by
          have hab: (a * b) ≠ 0 := by exact mul_ne_zero ha hb
          exact if_neg hab
        apply h0 at ha
        apply ha at hb
        rw[hr, hq] at hp
        simp at hp
        have hphi: φ a < φ a := by
          calc
            φ a ≤ φ (a * b) := by exact hb
            _ < φ a := by exact hp
        exact LT.lt.false hphi
      }

end Section14Sheet2
