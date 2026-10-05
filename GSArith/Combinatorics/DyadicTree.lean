/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import GSArith.Ledger

/-!
# The dyadic blow-up tree: counts and the Artin–Schreier identity

The oracle-free content of Propositions 3.13 and 3.14 of Dérickx–Gillibert–Keller–Pagano,
*Golod–Shafarevich for arithmetic surfaces*.

* **Component count.**  The depth-`k` components of the dyadic model `𝒫₂` correspond to the
  residue classes mod `2^k`, each non-terminal one having two children; stopping at depth
  `m - 2` gives `n₂ = ∑_{k=0}^{m-2} 2^k = 2^(m-1) - 1`, and `n₂ ≤ 1 + N (m - 2) ≤ 2 g m` with
  `g = 2^m - 1`, `N = 2g + 2`.
* **The residual Artin–Schreier equation.**  At the generic point of a depth-`(m-2)` component
  the reduction of `A` is `Ā = -(1/X + 1/(X-1) + 1/(X-2) + 1/(X-3))`, which vanishes in
  `𝔽₂(X)`; hence the residual equation is `w² + w = 0`, the normalization splits into two
  components with the same residue field as the base, and the total normalization genus is
  zero.  The identity is a formal identity in any field of characteristic two and is stated
  as such.
* **The Kummer unit form** of Proposition 3.14, equation (9):
  `u_i / ((x - i)/(x - g))² = 1 + 4 A_i` with `A_i = -2^(m-2)/(x - i)`, again a formal identity
  in any field.

The geometry (which blow-ups occur, and that the normalization is finite flat of degree two)
is Tier C and lives in the oracle interface.
-/

@[expose] public section

namespace GSArith.Combinatorics

open Finset

/-! ### Component counts -/

/-- `∑_{k=0}^{m-2} 2^k = 2^(m-1) - 1`: the number of geometric special-fibre components of the
dyadic model. -/
theorem dyadic_component_count (m : ℕ) :
    ∑ k ∈ range (m - 1), 2 ^ k = 2 ^ (m - 1) - 1 := by
  have h := geom_sum_mul_add (1 : ℕ) (m - 1)
  norm_num at h
  generalize ∑ i ∈ range (m - 1), 2 ^ i = S at h ⊢
  generalize 2 ^ (m - 1) = P at h ⊢
  omega

/-- The two upper bounds of Proposition 3.13: with `g = 2^m - 1` and `N = 2g + 2`,
`2^(m-1) - 1 ≤ 1 + N (m - 2) ≤ 2 g m` for `m ≥ 4`. -/
theorem dyadic_component_le (m : ℕ) (hm : 4 ≤ m) :
    2 ^ (m - 1) - 1 ≤ 1 + (2 * (2 ^ m - 1) + 2) * (m - 2) ∧
      1 + (2 * (2 ^ m - 1) + 2) * (m - 2) ≤ 2 * (2 ^ m - 1) * m := by
  obtain ⟨Q, hQ, hQ'⟩ : ∃ Q, 2 ^ m = 2 * Q ∧ 2 ^ (m - 1) = Q :=
    ⟨2 ^ (m - 1), by rw [← pow_succ']; congr 1; omega, rfl⟩
  have hlt : m < 2 * Q := hQ ▸ Nat.lt_two_pow_self
  have hQ8 : 8 ≤ Q := by
    have : 2 ^ 3 ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [hQ, hQ']
  constructor
  · have h1 : 1 ≤ 2 * Q := by omega
    zify [h1, (by omega : 1 ≤ Q), (by omega : 2 ≤ m)]
    nlinarith
  · have h1 : 1 ≤ 2 * Q := by omega
    zify [h1, (by omega : 2 ≤ m)]
    nlinarith

/-! ### The Artin–Schreier identity -/

/-- In a field of characteristic two, `1/x + 1/(x-1) + 1/(x-2) + 1/(x-3) = 0`: the reduction
`Ā` of Proposition 3.13 vanishes, so the residual Artin–Schreier equation is `w² + w = 0`. -/
theorem four_term_identity {K : Type*} [Field K] [CharP K 2] (x : K) :
    x⁻¹ + (x - 1)⁻¹ + (x - 2)⁻¹ + (x - 3)⁻¹ = 0 := by
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  have h3 : (3 : K) = 1 := by
    rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
  rw [h2, h3, sub_zero]
  have : x⁻¹ + (x - 1)⁻¹ + x⁻¹ + (x - 1)⁻¹ = 2 * (x⁻¹ + (x - 1)⁻¹) := by ring
  rw [this, h2, zero_mul]

/-! ### The Kummer unit form, Proposition 3.14 (9) -/

/-- `u_i / ((x - i)/(x - g))² = 1 + 4 A_i` with `u_i = (x - i)(x - i - 2^m)/(x - g)²` and
`A_i = -2^(m-2)/(x - i)`, as a formal identity in any field. -/
theorem kummer_unit_form {K : Type*} [Field K] (m : ℕ) (hm : 2 ≤ m) (x i g : K)
    (hxi : x - i ≠ 0) (hxg : x - g ≠ 0) :
    ((x - i) * (x - i - 2 ^ m) / (x - g) ^ 2) / ((x - i) / (x - g)) ^ 2 =
      1 + 4 * (-(2 ^ (m - 2)) / (x - i)) := by
  have h4 : (2 : K) ^ m = 4 * 2 ^ (m - 2) := by
    rw [show (4 : K) = 2 ^ 2 by norm_num, ← pow_add]
    congr 1
    omega
  rw [h4]
  field_simp
  ring

end GSArith.Combinatorics

end
