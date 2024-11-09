/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro hpq
  rw [hpq]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro hpq
  rw [hpq]
  intro hqp
  rw [hqp]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq
  intro hqr
  rw [hpq, hqr]
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  intro hpq
  cases' hpq with hp hq
  constructor
  exact hq
  exact hp
  intro hqp
  cases' hqp with hq hp
  constructor
  exact hp
  exact hq
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro hpqr
    cases' hpqr with hpq hr
    cases' hpq with hp hq
    constructor
    exact hp
    constructor
    exact hq
    exact hr
  · rintro ⟨ hp, hq, hr⟩
    exact ⟨⟨ hp, hq⟩ ,hr⟩
  done

example : P ↔ P ∧ True := by
  constructor
  · intro hp
    constructor
    exact hp
    triv
  · intro hpt
    cases' hpt with hp t
    exact hp
  done

example : False ↔ P ∧ False := by
  constructor
  · exfalso
  · intro hpf
    cases' hpf with hp hf
    exact hf
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hpq
  intro hrs
  rw [hpq]
  rw [hrs]
  done

example : ¬(P ↔ ¬P) := by
  by_contra h1
  cases' h1 with hpnp hnpp
  by_cases h:P
  apply hpnp at h
  apply h
  apply hnpp
  exact h
  apply h
  apply hnpp
  exact h
  done
