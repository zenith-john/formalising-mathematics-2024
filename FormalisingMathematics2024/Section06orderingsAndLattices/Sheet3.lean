/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-

# A harder question about lattices

I learnt this fact when preparing sheet 2.

With sets we have `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`, and `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.
In sheet 2 we saw an explicit example (the lattice of subspaces of a 2-d vector space)
of a lattice where neither `A ⊓ (B ⊔ C) = (A ⊔ B) ⊓ (A ⊔ C)` nor `A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C)`
held. But it turns out that in a general lattice, one of these equalities holds if and only if the
other one does! This was quite surprising to me.

The challenge is to prove it in Lean. My strategy would be to prove it on paper first
and then formalise the proof. If you're not in to puzzles like this, then feel free to skip
this question.

-/

example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  constructor
  intro hp
  intro a b c
  apply le_antisymm
  · have h: a ⊓ b ⊔ a ⊓ c = (a ⊔ a) ⊓ (a ⊔ b) ⊓ (c ⊔ a) ⊓ (c ⊔ b) := by
      calc
        a ⊓ b ⊔ a ⊓ c = (a ⊓ b ⊔ a) ⊓ (a ⊓ b ⊔ c) := by rw[hp]
        _ = ((a ⊔ a) ⊓ (a ⊔ b)) ⊓ ((c ⊔ a) ⊓ (c ⊔ b)) := by
          rw[sup_comm]
          rw[hp]
          have hc: a ⊓ b ⊔ c = (c ⊔ a) ⊓ (c ⊔ b) := by rw[sup_comm, hp];
          rw[hc]
        _ = (a ⊔ a) ⊓ (a ⊔ b) ⊓ (c ⊔ a) ⊓ (c ⊔ b) := by
          simp
          rw[← inf_assoc]
          simp
    rw[h]
    simp
    rw[sup_comm]
    exact inf_le_right
  · exact le_inf_sup

  intro hp
  intro a b c
  apply le_antisymm
  · exact sup_inf_le
  · rw[hp]
    rw[inf_comm]
    rw[hp]
    have hc: (a ⊔ b) ⊓ c = (c ⊓ a) ⊔ (c ⊓ b) := by
      rw[inf_comm, hp]
    rw[hc]
    simp
    constructor
    · trans a
      exact inf_le_right
      exact le_sup_left
    · rw[inf_comm]
      exact le_sup_right
