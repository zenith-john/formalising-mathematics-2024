/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hp
  left
  exact hp
  done

example : Q → P ∨ Q := by
  intro hq
  right
  exact hq
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hpq hpr hqr
  cases' hpq with hp hq
  apply hpr
  exact hp
  apply hqr
  exact hq
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hpq
  cases' hpq with hp hq
  right
  exact hp
  left
  exact hq
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · intro hpqr
    cases' hpqr with hpq hr
    cases' hpq with hp hq
    left
    exact hp
    right
    left
    exact hq
    right
    right
    exact hr
  · intro hpqr
    cases' hpqr with hp hqr
    left
    left
    exact hp
    cases' hqr with hq hr
    left
    right
    exact hq
    right
    exact hr
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hpr hqs
  rintro (hp | hq)
  left
  apply hpr
  exact hp
  right
  apply hqs
  exact hq
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hpq
  rintro (hp | hr)
  · left; apply hpq
    exact hp
  · right; exact hr
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hpr hqs
  rw [hpr]
  rw [hqs]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro hpq
    constructor
    · by_contra hp
      apply hpq
      left
      exact hp
    · by_contra hq
      apply hpq
      right
      exact hq
  · rintro ⟨ hnp, hnq⟩
    by_contra hpq
    cases' hpq with hp hq
    apply hnp
    exact hp
    apply hnq
    exact hq
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro hpq
    by_cases hp: P
    · right
      by_contra hq
      apply hpq
      constructor
      exact hp
      exact hq
    · left; exact hp
  · rintro (hnp | hnq)
    by_contra hpq
    cases' hpq with hp hq
    apply hnp
    exact hp
    by_contra hpq
    cases' hpq with hp hq
    apply hnq
    exact hq
  done
