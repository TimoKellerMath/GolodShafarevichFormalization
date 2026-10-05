/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import GSArith.Ledger

/-!
# Arithmetic of the tower

The bookkeeping identities used when assembling Theorem 3.18 and Corollary 3.24 of
Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic surfaces*, isolated as pure
arithmetic so that the geometric assembly has nothing left to compute.

* Proposition 2.17 gives `g(D) - 1 = d (g(C) - 1)` for a degree-`d` étale cover.  Along a tower
  of degree-two covers starting from a curve of genus `g₀` this yields
  `g(C_n) - 1 = 2^n (g₀ - 1)`, and with `g₀ - 1 = 2^g (g - 1)` (Proposition 3.1) the formula
  `g(C_n) - 1 = 2^(g+n) (g - 1)` of Theorem 1.2.  For `g ≥ 2` the genus tends to infinity.
* Corollary 3.24 sums local conductor exponents `a_p(C_n) ≤ 2 (1 + B_p) g(C_n)` into
  `log 𝔑(C_n) ≤ (2 ∑_p (1 + B_p) log p) · g(C_n)`.

Everything here is stated over `ℤ` or `ℝ` to avoid truncated subtraction.
-/

@[expose] public section

namespace GSArith.Numeric

open Filter

/-- Along a tower in which every step satisfies `g(C_{n+1}) - 1 = 2 (g(C_n) - 1)`
(Proposition 2.17 for a degree-two cover), `g(C_n) - 1 = 2^n (g(C_0) - 1)`. -/
theorem genus_tower (gen : ℕ → ℤ) (hstep : ∀ n, gen (n + 1) - 1 = 2 * (gen n - 1)) (n : ℕ) :
    gen n - 1 = 2 ^ n * (gen 0 - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [hstep, ih, pow_succ]; ring

/-- Theorem 1.2's genus formula: if moreover `g(C_0) - 1 = 2^g (g - 1)`, then
`g(C_n) - 1 = 2^(g+n) (g - 1)`. -/
theorem genus_tower' (gen : ℕ → ℤ) (g : ℕ) (h0 : gen 0 - 1 = 2 ^ g * (g - 1))
    (hstep : ∀ n, gen (n + 1) - 1 = 2 * (gen n - 1)) (n : ℕ) :
    gen n - 1 = 2 ^ (g + n) * (g - 1) := by
  rw [genus_tower gen hstep n, h0, pow_add]; ring

/-- `|H_n| = 2^(g+n) = 2^g · 2^n`. -/
theorem order_tower (g n : ℕ) : (2 : ℕ) ^ (g + n) = 2 ^ g * 2 ^ n := pow_add 2 g n

/-- For `g ≥ 2`, the genus `g(C_n) = 2^(g+n) (g - 1) + 1` tends to infinity with `n`. -/
theorem genus_tendsto_atTop (gen : ℕ → ℤ) (g : ℕ) (hg : 2 ≤ g)
    (hgen : ∀ n, gen n - 1 = 2 ^ (g + n) * (g - 1)) : Tendsto gen atTop atTop := by
  have hle : ∀ n : ℕ, (n : ℤ) ≤ gen n := fun n => by
    have h1 : (1 : ℤ) ≤ g - 1 := by omega
    have h2 : (n : ℤ) < 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    have h3 : (2 : ℤ) ^ n ≤ 2 ^ (g + n) := pow_le_pow_right₀ (by norm_num) (by omega)
    have := hgen n
    nlinarith
  exact tendsto_atTop_mono hle tendsto_natCast_atTop_atTop

/-- Corollary 3.24's final summation: if `a_p ≤ 2 (1 + B_p) g` for every `p` in a finite set
`Σ` of positive integers, then `log ∏_{p ∈ Σ} p^{a_p} ≤ (2 ∑_{p ∈ Σ} (1 + B_p) log p) · g`. -/
theorem conductor_sum_bound (S : Finset ℕ) (B a : ℕ → ℕ) (gn : ℕ)
    (hpos : ∀ p ∈ S, 1 ≤ p) (ha : ∀ p ∈ S, (a p : ℝ) ≤ 2 * (1 + B p) * gn) :
    Real.log (∏ p ∈ S, (p : ℝ) ^ a p) ≤ (2 * ∑ p ∈ S, (1 + B p) * Real.log p) * gn := by
  rw [Real.log_prod (fun p hp => by
        have : (1 : ℝ) ≤ p := by exact_mod_cast hpos p hp
        positivity)]
  simp only [Real.log_pow]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpos p hp)
  calc (a p : ℝ) * Real.log p ≤ 2 * (1 + B p) * gn * Real.log p :=
        mul_le_mul_of_nonneg_right (ha p hp) hlog
    _ = 2 * ((1 + B p) * Real.log p) * gn := by ring

end GSArith.Numeric

end
