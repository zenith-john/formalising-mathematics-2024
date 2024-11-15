/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic


/-

# Basic Number Theory

Lean has enough machinery to make number theory a feasible topic for
a final project. In this section I will work through a bunch of examples,
taken from Sierpinski's old book "250 elementary problems in number theory".

## Switching between naturals and integers

Sometimes when doing number theory in Lean you find yourself having to switch
between naturals, integers and rationals. For example, if you want to do `a ^ n`
with `a` an integer, then `n` had better be a natural number, because in general
you can't raise an integer to the power of an integer. However subtraction is
"broken" on naturals:

-/

example : (2 : ℕ) - 3 = 0 :=
  rfl

-- subtraction on naturals "rounds up to 0" as it must return a natural
example : (2 : ℤ) - 3 = -1 :=
  rfl

-- subtraction on integers works correctly
/-

so sometimes you need to dance between the two. There are coercions between
all of these objects:

-/
example (n : ℕ) : ℤ :=
  n

-- works fine
example (n : ℕ) : ℤ :=
  ↑n

-- what it does under the hood
example (n : ℕ) (z : ℤ) : ℚ :=
  n + z
-- gets translated to ↑n + ↑z where the two ↑s
-- represent different functions (ℕ → ℚ and ℤ → ℚ)

/-
The big problem with this is that you end up with goals and hypotheses with `↑` in
which you want to "cancel". The `norm_cast` tactic does this.
-/
example (a b : ℕ) (h : a + b = 37) : (a : ℤ) + b = 37 :=
  by
  /-
    a b : ℕ
    h : a + b = 37
    ⊢ ↑a + ↑b = 37

    exact `h` fails, because of the coercions (the goal is about the integer 37,
    not the natural 37)
    -/
  norm_cast

-- There are several shortcuts you can take here, for example
example (a b : ℕ) (h : a + b = 37) : (a : ℤ) + b = 37 := by exact_mod_cast h

-- `h` is "correct modulo coercions"
example (a b : ℕ) (h : a + b = 37) : (a : ℤ) + b = 37 := by assumption_mod_cast

-- "it's an assumption, modulo coercions"
-- The `ring` tactic can't deal with the `↑`s here (it's not its job)
example (a b : ℕ) : ((a + b : ℕ) : ℤ) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  norm_cast
  -- all the ↑s are gone now
  ring

-- Another approach:
example (a b : ℕ) : ((a + b : ℕ) : ℤ) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
  by
  push_cast
  -- does the "opposite" to `norm_cast`. The `norm_cast` tactic
  -- tries to pull `↑`s out as much as possible (so it changes `↑a + ↑b`
  -- to `↑(a + b)`), and then tries to cancel them. `push_cast` pushes
  -- the ↑s "inwards", i.e. as tightly up to the variables as it can.
  -- Goal is now
  -- ⊢ (↑a + ↑b) ^ 2 = ↑a ^ 2 + 2 * ↑a * ↑b + ↑b ^ 2
  ring
  -- works fine, with variables ↑a and ↑b.

/-

These `cast` tactics do not quite solve all your problems, however.
Sometimes you have statements about naturals, and you would rather
they were about integers (for example because you want to start
using subtraction). You can use the `zify` tactic to change statements
about naturals to statements about integers, and the `lift` tactic to
change statements about integers to statements about naturals. Check
out the Lean 4 documentation for these tactics if you want to know
more (I didn't cover them in the course notes):
- [`zify`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Zify.html#Mathlib.Tactic.Zify.zify)
- [`lift`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Lift.html#Mathlib.Tactic.lift)

## For which positive integers n does n+1 divide n²+1?

This is the first question in Sierpinski's book.

Hint: n+1 divides n^2-1.

-/
example (n : ℕ) (hn : 0 < n) : n + 1 ∣ n ^ 2 + 1 ↔ n = 1 := by
  have hr:(n + 1)^2 - 2 * n = n^2 + 1 := by ring_nf; refine tsub_eq_of_eq_add_rev ?h; ring
  rw[← hr]
  have hr: (n + 1 ∣  (n + 1)^2 - 2 * n) ↔ n + 1 ∣  2 * n := by
    zify
    have hp:∀k:ℤ, (k + 1 ∣ (k + 1)^2) := by intro k; exact Dvd.intro_left (Int.pow (k + 1) 1) rfl
    have hr:∀k m n:ℤ, k + 1 ∣ m → (k + 1 ∣ m - n ↔ k + 1 ∣  - n) := by
      intro k m n;
      intro hkm;
      apply dvd_iff_dvd_of_dvd_sub
      simp
      exact hkm
    have hs:∀k m:ℤ, (k + 1 ∣ -m) ↔ k + 1 ∣ m := by exact fun k m ↦ Int.dvd_neg
    specialize hr n ((n + 1)^2) (2 * n)
    specialize hs n (2 * n)
    specialize hp n
    apply hr at hp
    rw[hs] at hp
    ring_nf at hp ⊢
    norm_cast at hp ⊢
    have h: 1 + n * 2 + n^2 - n * 2 = 1 + n^2 := by
      calc
        1 + n * 2 + n^2 - n * 2 = 1 + n^2 + n * 2 - n * 2 := by ring_nf
        _ = 1 + n^2 := by simp
    rw[h]
    exact hp

  rw[hr]
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    rcases lt_trichotomy a 1 with (h1 | h2 | h3)
    · have h4: a = 0 := by exact Nat.lt_one_iff.mp h1
      rw[h4] at ha
      simp at ha
      rw[ha] at hn
      exfalso
      exact LT.lt.false hn
    · rw[h2] at ha
      simp at ha
      linarith
    · have h4: a ≥ 2 := by exact h3
      have h5:(n + 1) * a ≥ 2 * (n + 1) := by
        rw[mul_comm];
        exact Nat.mul_le_mul_right (n + 1) h3
      have h6: 2 * n > 2 * n := by
        calc
          2 * n = (n + 1) * a := by exact ha
          _ ≥ 2 * (n + 1) := by exact h5
          _ = 2 * n + 2 := by exact rfl
          _ > 2 * n := by linarith
      exfalso
      exact LT.lt.false h6
    done
  · intro hn
    rw[hn]
