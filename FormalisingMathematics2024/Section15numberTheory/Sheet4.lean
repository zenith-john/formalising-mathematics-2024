/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

section Section15Sheet4
/-

# Prove that for all positive integers n we have that
# 169 | 3³ⁿ⁺³-26n-27

This is the fourth question in Sierpinski's book "250 elementary problems
in number theory".

Proof: note that n=0 also works :-) In general use induction on n.

Base case n=0 works fine.

Inductive step: we assume `169 ∣ 3³ⁿ⁺³-26d-27`
So it divides 27 times this
which is `3³⁽ᵈ⁺¹⁾⁺³-26*27*d-27*27`
and we want it to divide `3³⁽ᵈ⁺¹⁾⁺³-26(d+1)-27`

so we're done if it divides the difference, which is
`-26d-26-27+26*27d+27*27`
which is `26*26n+26*26 = 13*13*something`
-/

-- The statement has subtraction in, so we use integers.
example (n : ℕ) (hn : 0 < n) : -- remark; not going to use hn
    (169 : ℤ) ∣ 3 ^ (3 * n + 3) - 26 * n - 27 := by
  clear hn
  -- told you
  induction' n with d hd
  · simp;norm_num
  · have hg: (27:ℤ) * (3 ^ (3 * d + 3) - 26 * d - 27) + 26 * 26 * d + 26 * 26= (3 ^ (3 * Nat.succ d + 3) - 26 * (Nat.succ d) - 27) := by
      have hq:Nat.succ d = d + 1 := by rfl
      rw[hq]
      have h1: (3:ℤ)^(3 * (d + 1) + 3) = 27 * 3^(3 * d + 3) := by
        calc
          (3:ℤ)^(3 * (d + 1) + 3) = 3^(3 + 3 * d + 3) := by simp;ring_nf
          _ = (3^3) * 3^(3 * d + 3) := by rw[pow_add];ring_nf
          _ = 27 * 3^(3 * d + 3) := by norm_num
      rw[h1]
      rw[mul_sub, mul_sub]
      have hq: - (27:ℤ) * (26 * d) - 27 * 27 + 26 * 26 * d + 26 * 26 = - 26 * (d + 1) - 27 := by
        ring_nf
      calc
        27 * 3 ^ (3 * d + 3) - 27 * (26 * d) - 27 * 27 + 26 * 26 * d + 26 * 26 = 27 * 3 ^ (3 * d + 3) + (- (27:ℤ) * (26 * d) - 27 * 27 + 26 * 26 * ↑d + 26 * 26) := by ring_nf
        _ = 27 * 3 ^ (3 * d + 3) + (- 26 * (d + 1) - 27) := by rw[hq]
        _ = 27 * 3 ^ (3 * d + 3) - 26 * (d + 1) - 27 := by ring_nf
    have h1: (169:ℤ) ∣ 27 * (3 ^ (3 * d + 3) - 26 * d - 27) := by exact Dvd.dvd.mul_left hd 27
    have h2: (169:ℤ) ∣ 26 * 26 * d + 26 * 26 := by
      have h3: (169:ℤ) ∣ 26 * 26 := by exact Int.dvd_of_mod_eq_zero rfl
      have h4: (169:ℤ) ∣ 26 * 26 * d := by exact Dvd.dvd.mul_right h3 d
      exact Int.dvd_add h4 h3
    rw[← hg]
    rw[add_assoc]
    exact Int.dvd_add h1 h2



end Section15Sheet4
