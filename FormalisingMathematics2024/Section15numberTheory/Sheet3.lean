/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

namespace Section15Sheet3
/-

# Prove that there exists infinitely many positive integers n such that
# 4n² + 1 is divisible both by 5 and 13.

This is the third question in Sierpinski's book "250 elementary problems
in number theory".

Maths proof: if n=4 then 4n^2+1=65 is divisible by both 5 and 13
so if n is congruent to 4 mod 5 and mod 13 (i.e if n=4+65*t)
then this will work.

There are various ways to formalise the statement that some set
of naturals is infinite. We suggest two here (although proving
they're the same is fiddly)

-/

-- The number-theoretic heart of the argument.
-- Note that "divides" is `\|` not `|`
theorem divides_of_cong_four (t : ℕ) :
    5 ∣ 4 * (65 * t + 4) ^ 2 + 1 ∧ 13 ∣ 4 * (65 * t + 4) ^ 2 + 1 := by
        constructor
        ring_nf
        have h1: 5 ∣ t * 2080 := by
            have h: 5 ∣ 2080 := by exact Fin.nat_cast_eq_zero.mp rfl
            exact Dvd.dvd.mul_left h t
            done
        have h2: 5 ∣ t^2 * 16900 := by
            have h: 5 ∣ 16900 := by exact Fin.nat_cast_eq_zero.mp rfl
            exact Dvd.dvd.mul_left h (t^2)
        have h: 5 ∣ 65 := by exact Fin.nat_cast_eq_zero.mp rfl
        have h3: 5 ∣ 65 + t * 2080 := by exact Nat.dvd_add h h1
        exact Nat.dvd_add h3 h2

        ring_nf
        have h1: 13 ∣ t * 2080 := by
            have h: 13 ∣ 2080 := by exact Fin.nat_cast_eq_zero.mp rfl
            exact Dvd.dvd.mul_left h t
            done
        have h2: 13 ∣ t^2 * 16900 := by
            have h: 13 ∣ 16900 := by exact Fin.nat_cast_eq_zero.mp rfl
            exact Dvd.dvd.mul_left h (t^2)
        have h: 13 ∣ 65 := by exact Fin.nat_cast_eq_zero.mp rfl
        exact Nat.dvd_add (Nat.dvd_add h h1) h2



-- There are arbitrarily large solutions to `5 ∣ 4*n²+1 ∧ 13 ∣ 4*n²+1`
theorem arb_large_soln :
    ∀ N : ℕ, ∃ n > N, 5 ∣ 4 * n ^ 2 + 1 ∧ 13 ∣ 4 * n ^ 2 + 1 := by
        intro N
        use (65 * N + 4)
        constructor
        have h1: 65 * N ≥ N := by refine Nat.le_mul_of_pos_left ?_; norm_num
        calc
            65 * N + 4 ≥ N + 4 := by exact Nat.add_le_add_right h1 4
            _ > N := by simp

        exact divides_of_cong_four N

#check Set.Infinite

-- This is not number theory any more, it's switching between two
-- interpretations of "this set of naturals is infinite"
theorem infinite_iff_arb_large (S : Set ℕ) :
    S.Infinite ↔ ∀ N, ∃ n > N, n ∈ S := by
        constructor
        intro hs
        intro N
        by_contra hn
        rw[Set.Infinite] at hs
        apply hs
        have hf: Set.Finite {x:ℕ | x ≤ N} := by exact Set.finite_le_nat N
        have h: S ⊆ {x:ℕ | x ≤ N} := by
            intro a hs
            by_contra hp
            have h1: a > N := by exact Nat.not_le.mp hp
            apply hn
            use a
        exact Set.Finite.subset hf h

        intro hN
        by_contra hp
        rw[Set.Infinite, not_not] at hp
        have hq: ∃ N:ℕ, ∀ a ∈ S, a ≤ N := by exact S.exists_upper_bound_image (fun a => a) hp
        obtain ⟨N, hn⟩ := hq
        specialize hN N
        obtain ⟨n, hns⟩ := hN
        specialize hn n hns.2
        have hf: n > n := by
            calc
                n > N := by exact hns.1
                _ ≥ n := by exact hn
        exact LT.lt.false hf

-- Another way of stating the question (note different "|" symbols:
-- there's `|` for "such that" in set theory and `\|` for "divides" in number theory)
theorem infinite_setOf_solutions :
    {n : ℕ | 5 ∣ 4 * n ^ 2 + 1 ∧ 13 ∣ 4 * n ^ 2 + 1}.Infinite := by
  rw [infinite_iff_arb_large]
  exact arb_large_soln

end Section15Sheet3
