/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import GSArith.Ledger

/-!
# Chebyshev bounds in the paper's normalization

Proposition 3.17 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic
surfaces*, uses two classical estimates, both derived from the primorial bound
`primorial n < 4 ^ n`:

* `ϑ(x) ≤ 4 x log 2` for `x ≥ 2`, and
* `π(x) ≤ √x + 8 (log 2) x / log x`, obtained by splitting the primes at `√x`.

Mathlib already proves both, in a slightly sharper form: `Chebyshev.theta_le_log4_mul_x`
gives `ϑ(x) ≤ x log 4`, and `Chebyshev.pi_le_log4_mul_div` gives
`π(x) ≤ (log 4) x / log √x + √x = √x + 4 (log 2) x / log x`.  This file only restates them in
the shape the paper uses, so that `GSArith.Numeric.ObstructionBound` can quote the paper's
inequalities verbatim.  Nothing here is assumed.

## Main results

* `GSArith.Numeric.theta_le_four_log_two_mul`: `ϑ(x) ≤ 4 (log 2) x` for `0 ≤ x`.
* `GSArith.Numeric.primeCounting_le_sqrt_add`: `π(⌊x⌋) ≤ √x + 4 (log 2) x / log x` for
  `1 < x`, Mathlib's constant.
* `GSArith.Numeric.primeCounting_le_sqrt_add_eight`: the paper's constant `8`, for `2 ≤ x`.
-/

@[expose] public section

namespace GSArith.Numeric

open Real Chebyshev
open scoped Chebyshev

/-- `log 4 = 2 log 2`. -/
theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  norm_num

/-- Chebyshev's upper bound for `ϑ` in the paper's normalization: `ϑ(x) ≤ 4 (log 2) x`.
(Mathlib's `Chebyshev.theta_le_log4_mul_x` gives the sharper `ϑ(x) ≤ (log 4) x`.) -/
theorem theta_le_four_log_two_mul {x : ℝ} (hx : 0 ≤ x) : θ x ≤ 4 * Real.log 2 * x := by
  have h := theta_le_log4_mul_x hx
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [log_four] at h
  nlinarith

/-- The prime-counting bound obtained by splitting the primes at `√x`:
`π(⌊x⌋) ≤ √x + 4 (log 2) x / log x` for `1 < x`.  This is `Chebyshev.pi_le_log4_mul_div`
rewritten with `log √x = (log x)/2` and `log 4 = 2 log 2`. -/
theorem primeCounting_le_sqrt_add {x : ℝ} (hx : 1 < x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ √x + 4 * Real.log 2 * x / Real.log x := by
  have h := pi_le_log4_mul_div hx
  have hx0 : 0 ≤ x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  rw [Real.log_sqrt hx0, log_four] at h
  calc (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ 2 * Real.log 2 * x / (Real.log x / 2) + √x := h
    _ = √x + 4 * Real.log 2 * x / Real.log x := by
      field_simp
      ring

/-- The paper's form of the prime-counting bound, with the constant `8`:
`π(⌊x⌋) ≤ √x + 8 (log 2) x / log x` for `2 ≤ x`. -/
theorem primeCounting_le_sqrt_add_eight {x : ℝ} (hx : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ √x + 8 * Real.log 2 * x / Real.log x := by
  have h := primeCounting_le_sqrt_add (by linarith : 1 < x)
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : 4 * Real.log 2 * x / Real.log x ≤ 8 * Real.log 2 * x / Real.log x := by
    rw [div_le_div_iff_of_pos_right hlog]
    nlinarith
  linarith

end GSArith.Numeric

end
