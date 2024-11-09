/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
forward along `f` to make a subset `f(S) : Set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `Set X`.
In Lean we use the notation `f '' S` for this. This is notation
for `Set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : Set Y` of `Y` we can
pull it back along `f` to make a subset `f⁻¹(T) : Set X` of `X`. The
definition of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `Inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type: the notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)

example : S ⊆ f ⁻¹' (f '' S) := by
  intro x hs
  simp
  use x

example : f '' (f ⁻¹' T) ⊆ T := by
  intro x hx
  simp at hx
  obtain ⟨p, hp⟩ := hx
  cases' hp with ha hb
  rw [hb] at ha
  exact ha

-- `library_search` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  intro hp
  intro x hx
  simp at hp
  specialize hp hx
  exact hp

  intro hs
  intro x hx
  obtain ⟨q, ⟨hq, hq2⟩⟩ := hx
  specialize hs hq
  have hp: f q ∈ T := by
    exact hs
  rw [hq2] at hp
  exact hp

-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by
  ext x
  constructor
  · intro hx
    exact hx
  · intro hx
    exact hx

-- pushforward is a little trickier. You might have to `ext x, split`.
example : id '' S = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, ⟨hy, hy2⟩⟩ := hx
    have hp: y = id y := by triv
    rwa [← hy2, ← hp]
  · intro hx
    use x
    have hp: x = id x := by triv
    exact ⟨hx, hp⟩

-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  ext x
  triv

-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by
  ext x
  constructor
  intro h
  obtain ⟨y, ⟨hy1, hy2⟩⟩ := h
  have hp: f y ∈ f '' S := by
    exact Set.mem_image_of_mem f hy1
  use (f y)
  constructor <;> assumption

  intro hx
  obtain ⟨y, ⟨hy1, hy2⟩⟩ := hx
  obtain ⟨z, ⟨hz1, hz2⟩⟩ := hy1
  use z
  constructor
  exact hz1
  simp
  rwa [hz2]
