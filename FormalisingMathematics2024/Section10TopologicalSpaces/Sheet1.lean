/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang, Kevin Buzzard
-/
import Mathlib.Tactic

namespace Section10sheet1

noncomputable section

/-!

# Topological Spaces in Lean

For any `X : Type`, the type `TopologicalSpace X` is the type of topologies on `X`.
`TopologicalSpace` is a structure; its four fields are one data field `IsOpen : Set X → Prop` (the
predicate on subsets of `X` saying whether or not they're open) and then three proof fields
(`isOpen_univ` saying the whole space is open, `isOpen_inter` saying the intersection of two
opens is open, and `isOpen_sUnion` saying an arbitrary union of opens is open).

Here is a simple example: let's make the discrete topology on a type.
-/

open TopologicalSpace

variable (X : Type)

set_option linter.unusedVariables false -- please stop moaning about unused variables

example : TopologicalSpace X where
  IsOpen (s : Set X) := True -- "Is `s` open? Yes, always"
  isOpen_univ := by
    -- is the whole space open? The goal is `True`
    triv
  isOpen_inter := by
    -- let s and t be two sets
    intros s t
    -- assume they're open
    intros hs ht
    -- Is their intersection open?
    -- By definition, this means "can you prove `True`"?
    triv
  isOpen_sUnion := by
    -- say F is a family of sets
    intro F
    -- say they're all open
    intro hF
    -- Is their union open?
    triv

/-
A much more fiddly challenge is to formalise the indiscrete topology. You will be constantly
splitting into cases in this proof.
-/

example : TopologicalSpace X where
  IsOpen (s : Set X) := s = ∅ ∨ s = Set.univ -- empty set or whole thing
  isOpen_univ := by
   -- use `dsimp`
    dsimp
    right
    rfl
  isOpen_inter := by
    -- use `cases'`
    intro s t
    intro hs ht
    cases' hs with he hu <;> cases' ht with pe pu
    left
    rw[he,pe]
    exact Set.empty_inter ∅
    left
    rw[he,pu]
    exact Set.empty_inter Set.univ
    left
    rw[hu,pe]
    exact Set.univ_inter ∅
    right
    rw[hu,pu]
    exact Set.univ_inter Set.univ
  isOpen_sUnion := by
    intro F
    -- do cases on whether Set.univ ∈ F
    by_cases hp:Set.univ ∈ F
    intro h
    right
    have hq: ⋃₀F = Set.univ := by
      have hf: Set.univ ⊆ ⋃₀F := by
        exact Set.subset_sUnion_of_mem hp
      exact Set.univ_subset_iff.mp hf
    exact hq

    intro h
    simp at h
    have hq: ∀t ∈ F, t = ∅ := by
      intro t
      intro ht
      specialize h t ht
      cases' h with h1 h2
      exact h1
      by_contra
      apply hp
      rw[← h2]
      exact ht
    left
    exact Set.sUnion_eq_empty.mpr hq


-- `isOpen_empty` is the theorem that in a topological space, the empty set is open.
-- Can you prove it yourself? Hint: arbitrary unions are open

example (X : Type) [TopologicalSpace X] : IsOpen (∅ : Set X) := by
  have hq: ∀x ∈ (∅: Set (Set X)), IsOpen x := by intro x hx; cases' hx;
  apply isOpen_sUnion at hq
  have hp: ⋃₀(∅:Set (Set X)) = ∅ := by exact Set.sUnion_empty
  rw[← hp]
  exact hq

-- The reals are a topological space. Let's check Lean knows this already
#synth TopologicalSpace ℝ

-- Let's make it from first principles.

def Real.IsOpen (s : Set ℝ) : Prop :=
  -- every element of `s` has a neighbourhood (x - δ, x + δ) such that all y in this
  -- neighbourhood are in `s`
  ∀ x ∈ s, ∃ δ > 0, ∀ y : ℝ, x - δ < y ∧ y < x + δ → y ∈ s

-- Now let's prove the axioms
lemma Real.isOpen_univ : Real.IsOpen (Set.univ : Set ℝ) := by
  intro x hx
  use 1
  constructor
  linarith
  intro y hy
  triv

lemma Real.isOpen_inter (s t : Set ℝ) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ∩ t) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  specialize hs x hx1
  obtain ⟨ε1, ⟨he, hp1⟩⟩ := hs
  specialize ht x hx2
  obtain ⟨ε2, ⟨he2, hp2⟩⟩ := ht
  use (min ε1 ε2)
  constructor
  exact lt_min he he2
  intro y ⟨hy1, hy2⟩
  have hq: ε1 ≥ min ε1 ε2 := by exact min_le_left ε1 ε2
  have hq2: ε2 ≥ min ε1 ε2 := by exact min_le_right ε1 ε2
  have hz: x - ε1 < y ∧ y < x + ε1 := by constructor <;> linarith
  have hw: x - ε2 < y ∧ y < x + ε2:= by constructor <;> linarith
  specialize hp1 y
  apply hp1 at hz
  specialize hp2 y
  apply hp2 at hw
  exact Set.mem_inter hz hw

lemma Real.isOpen_sUnion (F : Set (Set ℝ)) (hF : ∀ s ∈ F, IsOpen s) : IsOpen (⋃₀ F) := by
  intro x hx
  obtain ⟨f, ⟨hf, hxf⟩⟩ := hx
  specialize hF f hf
  obtain ⟨ε, ⟨hε, hy⟩⟩ := hF x hxf
  use ε
  constructor
  exact hε
  intro z hz
  specialize hy z hz
  exact Set.mem_sUnion_of_mem hy hf

-- now we put everything together using the notation for making a structure
example : TopologicalSpace ℝ where
  IsOpen := Real.IsOpen
  isOpen_univ := Real.isOpen_univ
  isOpen_inter := Real.isOpen_inter
  isOpen_sUnion := Real.isOpen_sUnion
