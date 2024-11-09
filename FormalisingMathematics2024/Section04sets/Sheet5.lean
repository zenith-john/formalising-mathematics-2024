/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext x
  constructor
  intro hx
  cases' hx with h1 h2
  exact h1
  exact h2
  intro hx
  constructor; exact hx

example : A ∩ A = A := by
  ext x
  constructor
  intro hx
  cases' hx with h1 h2
  exact h1
  intro hx
  constructor <;> exact hx

example : A ∩ ∅ = ∅ := by
  ext x
  constructor
  intro ⟨_, hq⟩
  exact hq
  intro hp
  by_contra
  cases' hp

example : A ∪ univ = univ := by
  ext x
  constructor
  rintro (hp | hq) <;> triv
  intro _
  right
  triv

example : A ⊆ B → B ⊆ A → A = B := by
  intro hab hba
  ext a
  constructor
  intro hp
  apply hab at hp
  exact hp

  intro hb
  apply hba at hb
  exact hb

example : A ∩ B = B ∩ A := by
  ext h
  constructor <;>
  rintro ⟨hp, hq⟩ <;>
  constructor <;>
  assumption

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext h
  constructor
  · rintro ⟨_, ⟨_, _⟩⟩
    constructor <;> (try constructor) <;> assumption
  · rintro ⟨⟨_, _⟩, _⟩
    refine ⟨?_, ⟨?_, ?_⟩⟩
    <;> assumption

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext h
  constructor
  · rintro (ha | (hb | hc))
    · left; left; assumption
    · left; right; assumption
    · right; assumption
  · rintro ((ha | hb) | hc)
    · left; assumption
    · right; left; assumption
    · right; right; assumption

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  exact union_distrib_left A B C

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  exact inter_distrib_left A B C
