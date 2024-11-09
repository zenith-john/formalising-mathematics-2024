/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/


open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : x ∉ A → x ∈ A → False := by
  intro hx
  exact hx

example : x ∈ A → x ∉ A → False := by
  intro hx
  by_contra ha
  apply ha
  exact hx

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro hab
  intro hb
  by_contra ha
  specialize hab ha
  apply hb
  exact hab

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by
  by_contra hx
  cases hx

example : x ∈ Aᶜ → x ∉ A := by
  simp

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor
  · intro hx
    by_contra h2
    cases' h2 with x1 h3
    specialize hx x1
    apply h3
    exact hx
  · intro hn x
    by_contra hp
    apply hn
    use x
    exact hp

example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  constructor
  · intro hx
    by_contra ha
    obtain ⟨x, hxa⟩ := hx
    specialize ha x
    apply ha
    exact hxa
  · intro hn
    by_contra hp
    apply hn
    intro x
    by_contra hq
    apply hp
    use x
    exact not_not_mem.mp hq
