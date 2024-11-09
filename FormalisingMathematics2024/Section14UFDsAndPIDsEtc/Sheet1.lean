/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.RingTheory.PrincipalIdealDomain
-- theory of PIDs

/-!

# Principal Ideal Domains

First let's showcase what mathlib has.

Let `R` be a commutative ring.
-/
variable (R : Type) [CommRing R]

-- We say `R` is a *principal ideal ring* if all ideals are principal.
-- We say `R` is a *domain* if it's an integral domain.
-- We say `R` is a *principal ideal domain* if it's both.
-- So here's how to say "Assume `R` is a PID":
variable [IsPrincipalIdealRing R] [IsDomain R]

-- Note that both of these are typeclasses, so various things should
-- be automatic.
example : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
  intro a b
  apply eq_zero_or_eq_zero_of_mul_eq_zero

-- typeclass inference
-- magically extracts the assumption from `IsDomain`
example : (0 : R) ≠ 1 := by exact zero_ne_one

example (I : Ideal R) : I.IsPrincipal := by exact IsPrincipalIdealRing.principal I

example (I : Ideal R) : ∃ j, I = Ideal.span {j} := by
  have hp: I.IsPrincipal := by apply IsPrincipalIdealRing.principal I
  exact (Submodule.isPrincipal_iff I).mp hp

-- product of two PIDs isn't a PID, but only becuase it's not a domain
example (A B : Type) [CommRing A] [CommRing B]
    [IsPrincipalIdealRing A] [IsPrincipalIdealRing B] :
    IsPrincipalIdealRing (A × B) where
  principal I := by
    obtain ⟨a, ha: _ = Ideal.span _⟩
      := IsPrincipalIdealRing.principal (I.map (RingHom.fst A B))
    obtain ⟨b, hb: _ = Ideal.span _⟩
      := IsPrincipalIdealRing.principal (I.map (RingHom.snd A B))
    rw[Submodule.isPrincipal_iff]
    use (a, b)
    ext i
    rw[← Ideal.span, Ideal.mem_span_singleton]
    constructor
    · intro hi
      have hp: (RingHom.fst A B) i ∈ I.map (RingHom.fst A B) :=
        by exact Ideal.mem_map_of_mem (RingHom.fst A B) hi
      rw[ha] at hp
      rw[Ideal.mem_span_singleton] at hp
      rcases hp with ⟨q, hq⟩
      have hp: (RingHom.snd A B) i ∈ I.map (RingHom.snd A B) :=
        by exact Ideal.mem_map_of_mem _ hi
      rw[hb] at hp
      rw[Ideal.mem_span_singleton] at hp
      rcases hp with ⟨r, hr⟩
      use (q, r)
      change i = (a * q, b * r)
      rw[← hq, ← hr]
      rfl
    · intro hab
      rcases hab with ⟨x, hx⟩
      rw[CommRing.mul_comm] at hx
      rw[hx]
      apply Ideal.mul_mem_left
      have hp: a ∈ Ideal.span {a} := by exact Ideal.mem_span_singleton_self a
      rw[← ha] at hp
      have hq: b ∈ Ideal.span {b} := by exact Ideal.mem_span_singleton_self b
      rw[← hb] at hq
      rw [Ideal.mem_map_iff_of_surjective] at hp hq
      rcases hp with ⟨⟨x1, x2⟩, hx, h1⟩
      rcases hq with ⟨⟨y1, y2⟩, hy, h2⟩
      convert I.add_mem (I.mul_mem_left (1, 0) hx) (I.mul_mem_left (0, 1) hy) <;> simp

      rw[← h1]
      rfl
      rw[← h2]
      rfl

      intro b; use (0, b); rfl
      intro a; use (a, 0); rfl
    done
