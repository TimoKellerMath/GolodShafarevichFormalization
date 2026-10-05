/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Numeric.Chebyshev
public import GSArith.Combinatorics.DyadicTree

/-!
# The obstruction bound `b(g,m)` and the threshold `m ≥ 10529`

Proposition 3.17 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic
surfaces*, bounds the dimension of the obstruction space by

  `b(g, m) = (328 g + 327) t + (10 m + 20) g + 9`,   `t = #{odd primes p ≤ 2g + 1}`,

and asserts that `b(g, m) < g² / 4` for `g = 2^m - 1` and every `m ≥ 32768`.  This file proves
the numerical claim with the **sharper threshold `m ≥ 10529`**.  It is the one explicit number
in the paper, and it is entirely oracle-free: the only input is the prime-counting bound of
`GSArith.Numeric.Chebyshev`, which Mathlib derives from `primorial n < 4 ^ n`.

The chain follows the paper, with Mathlib's constant `4 log 2` in place of the paper's `8 log 2`
(the paper's own `ϑ(x) ≤ 4 (log 2) x` is twice the standard `ϑ(x) < x log 4`), and without
rounding the second step:

1. `t ≤ π(2g + 1) ≤ √(2g+1) + 4 (log 2)(2g+1) / log (2g+1)`;
2. `2g + 1 ≥ 2^m`, so `log (2g+1) ≥ m log 2`, whence `t ≤ 2 √g + (8 g + 4) / m`;
3. `b(g,m) ≤ 329 g · t + (10 m + 29) g ≤ 658 g √g + 2632 g² / m + 1316 g / m + (10 m + 29) g`;
4. for `m ≥ 10529`: the three small terms are each `≤ g²/10⁶`, `2632 g²/m ≤ (2632/10529) g²`,
   and `3/10⁶ + 2632/10529 < 1/4`.

The limit of this method is `m > 4 · 8 · 328 = 10496`; the paper's `32768` came from the
factor two in `ϑ` and from rounding `(8g + 4)/m` up to `17 g/m`.

The file also records the **`m`-free form** of the bound: the paper proves the exact dyadic
component count `n₂ = 2^(m-1) - 1` (Proposition 3.13) and then discards it for `n₂ ≤ 2gm`; kept,
it gives `b'(g, m) = (328 g + 327) t + 5 (2^(m-1) - 1) + 20 g + 9 = (328 g + 327) t + (45 g + 13)/2`.

## Main results

* `GSArith.Numeric.oddPrimeCount`, `GSArith.Numeric.b`, `GSArith.Numeric.b'`: the quantities
  of Proposition 3.17 and its sharpened form.
* `GSArith.Numeric.b_lt_quarter_sq`: `b(g, m) < g² / 4` for `g = 2^m - 1`, `m ≥ 10529`.
* `GSArith.Numeric.b'_eq`, `b'_le_b`, `b'_lt_quarter_sq`: the `m`-free bound, its comparison
  with `b`, and the same threshold.
-/

@[expose] public section

namespace GSArith.Numeric

open Real

/-- `t = #{p odd prime : p ≤ 2g + 1}`, the number of odd primes up to `2g + 1`. -/
def oddPrimeCount (g : ℕ) : ℕ := Nat.primeCounting (2 * g + 1) - 1

/-- The bound `b(g, m) = (328 g + 327) t + (10 m + 20) g + 9` of Proposition 3.17. -/
noncomputable def b (g m : ℕ) : ℝ :=
  (328 * g + 327) * oddPrimeCount g + (10 * m + 20) * g + 9

/-- The `m`-free bound `b'(g, m) = (328 g + 327) t + 5 (2^(m-1) - 1) + 20 g + 9`, obtained by
keeping the exact dyadic component count `n₂ = 2^(m-1) - 1` of Proposition 3.13. -/
noncomputable def b' (g m : ℕ) : ℝ :=
  (328 * g + 327) * oddPrimeCount g + 5 * ((2 ^ (m - 1) - 1 : ℕ) : ℝ) + 20 * g + 9

/-! ### Step 1: the prime-counting input -/

theorem oddPrimeCount_le (g : ℕ) : (oddPrimeCount g : ℝ) ≤ Nat.primeCounting (2 * g + 1) := by
  unfold oddPrimeCount
  exact_mod_cast Nat.sub_le _ _

/-- `√4 = 2`. -/
theorem sqrt_four : √(4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `√(2g + 1) ≤ 2 √g` for `g ≥ 1`. -/
theorem sqrt_two_mul_add_one_le {g : ℝ} (hg : 1 ≤ g) : √(2 * g + 1) ≤ 2 * √g := by
  calc √(2 * g + 1) ≤ √(4 * g) := Real.sqrt_le_sqrt (by linarith)
    _ = 2 * √g := by rw [Real.sqrt_mul (by norm_num) g, sqrt_four]

/-- Step 1: `π(2g+1) ≤ √(2g+1) + 4 (log 2)(2g+1) / log(2g+1)` for `g ≥ 1`. -/
theorem primeCounting_two_mul_add_one_le {g : ℕ} (hg : 1 ≤ g) :
    (Nat.primeCounting (2 * g + 1) : ℝ) ≤
      √(2 * g + 1) + 4 * Real.log 2 * (2 * g + 1) / Real.log (2 * g + 1) := by
  have h := primeCounting_le_sqrt_add (x := ((2 * g + 1 : ℕ) : ℝ)) (by exact_mod_cast (by omega))
  rw [Nat.floor_natCast] at h
  push_cast at h
  exact h

/-! ### Step 2: `log (2g+1) ≥ m log 2` when `g = 2^m - 1` -/

/-- The elementary size facts about `g = 2^m - 1` needed below, for `m ≥ 10529`. -/
theorem two_pow_sub_one_facts {m : ℕ} (hm : 10529 ≤ m) :
    327 ≤ 2 ^ m - 1 ∧ 658000000 ^ 2 ≤ 2 ^ m - 1 ∧ 1000000 * (10 * m + 29) ≤ 2 ^ m - 1 ∧
      2 ^ m ≤ 2 * (2 ^ m - 1) + 1 := by
  have h60 : 2 ^ 60 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsplit : 2 ^ m = 2 ^ 25 * 2 ^ (m - 25) := by
    rw [← pow_add]; congr 1; omega
  have hlt : m - 25 < 2 ^ (m - 25) := Nat.lt_two_pow_self
  have hlin : 2 ^ 25 * (m - 25 + 1) ≤ 2 ^ m := by
    rw [hsplit]; exact Nat.mul_le_mul_left _ hlt
  norm_num at h60 hlin ⊢
  generalize 2 ^ m = N at *
  omega

/-- `m log 2 ≤ log (2g + 1)` when `2^m ≤ 2g + 1`. -/
theorem mul_log_two_le_log {g : ℝ} {m : ℕ} (h : (2 : ℝ) ^ m ≤ 2 * g + 1) :
    m * Real.log 2 ≤ Real.log (2 * g + 1) := by
  rw [← Real.log_pow]
  exact Real.log_le_log (by positivity) h

/-- Step 2: `t ≤ 2 √g + (8 g + 4) / m` for `g = 2^m - 1`, `m ≥ 10529`. -/
theorem oddPrimeCount_le_sqrt_add {g m : ℕ} (hm : 10529 ≤ m) (hg : g = 2 ^ m - 1) :
    (oddPrimeCount g : ℝ) ≤ 2 * √g + (8 * g + 4) / m := by
  obtain ⟨h327, -, -, hpow⟩ := two_pow_sub_one_facts hm
  rw [← hg] at h327 hpow
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (by omega : 1 ≤ g)
  have hpowR : (2 : ℝ) ^ m ≤ 2 * g + 1 := by exact_mod_cast hpow
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : m * Real.log 2 ≤ Real.log (2 * g + 1) := mul_log_two_le_log hpowR
  have hlogpos : 0 < m * Real.log 2 := by positivity
  calc (oddPrimeCount g : ℝ) ≤ Nat.primeCounting (2 * g + 1) := oddPrimeCount_le g
    _ ≤ √(2 * g + 1) + 4 * Real.log 2 * (2 * g + 1) / Real.log (2 * g + 1) :=
        primeCounting_two_mul_add_one_le (by omega)
    _ ≤ 2 * √g + 4 * Real.log 2 * (2 * g + 1) / (m * Real.log 2) :=
        add_le_add (sqrt_two_mul_add_one_le hg1)
          (div_le_div_of_nonneg_left (by positivity) hlogpos hlog)
    _ = 2 * √g + (8 * g + 4) / m := by
        field_simp
        ring

/-! ### Steps 3 and 4: the bound on `b` and the threshold -/

/-- Step 3: `b(g,m) ≤ 329 g t + (10m + 29) g` once `g ≥ 327`. -/
theorem b_le_of_le {g m : ℕ} (hg : 327 ≤ g) :
    b g m ≤ 329 * g * oddPrimeCount g + (10 * m + 29) * g := by
  unfold b
  have hgR : (327 : ℝ) ≤ g := by exact_mod_cast hg
  have ht : (0 : ℝ) ≤ oddPrimeCount g := by positivity
  nlinarith

/-- **Proposition 3.17, numerical claim, sharpened.**  For `g = 2^m - 1` and `m ≥ 10529`,
`b(g, m) < g² / 4`.  (The paper states this for `m ≥ 32768`.) -/
@[gs_public]
theorem b_lt_quarter_sq {g m : ℕ} (hm : 10529 ≤ m) (hg : g = 2 ^ m - 1) :
    b g m < (g : ℝ) ^ 2 / 4 := by
  obtain ⟨h327, h658, hlin, -⟩ := two_pow_sub_one_facts hm
  rw [← hg] at h327 h658 hlin
  have hgR : (327 : ℝ) ≤ g := by exact_mod_cast h327
  have h658R : (658000000 : ℝ) ^ 2 ≤ g := by exact_mod_cast h658
  have hlinR : (1000000 : ℝ) * (10 * m + 29) ≤ g := by exact_mod_cast hlin
  have hmR : (10529 : ℝ) ≤ m := by exact_mod_cast hm
  have hg0 : (0 : ℝ) < g := by linarith
  have ht := oddPrimeCount_le_sqrt_add hm hg
  have ht0 : (0 : ℝ) ≤ oddPrimeCount g := by positivity
  have hm0 : (0 : ℝ) < m := by linarith
  -- the pieces of step 4
  have hsqrt : (658000000 : ℝ) ≤ √g := by
    rw [Real.le_sqrt (by norm_num) hg0.le]; exact h658R
  have hsq : √(g : ℝ) * √g = g := Real.mul_self_sqrt hg0.le
  have hsqrt0 : (0 : ℝ) ≤ √g := Real.sqrt_nonneg g
  have h1 : 658 * (g : ℝ) * √g ≤ g ^ 2 / 1000000 := by
    have h : 658000000 * √(g : ℝ) ≤ g := by
      calc 658000000 * √(g : ℝ) ≤ √g * √g := by nlinarith
        _ = g := hsq
    nlinarith
  have h2eq : 329 * (g : ℝ) * ((8 * g + 4) / m) = 2632 * g ^ 2 / m + 1316 * g / m := by
    field_simp
    ring
  have h2a : 2632 * (g : ℝ) ^ 2 / m ≤ 2632 * g ^ 2 / 10529 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hmR
  have h2b : 1316 * (g : ℝ) / m ≤ g ^ 2 / 1000000 := by
    rw [div_le_iff₀ hm0]; nlinarith
  have h2 : 329 * (g : ℝ) * ((8 * g + 4) / m) ≤ 2632 * g ^ 2 / 10529 + g ^ 2 / 1000000 := by
    rw [h2eq]; linarith
  have h3 : (10 * m + 29) * (g : ℝ) ≤ g ^ 2 / 1000000 := by nlinarith
  have hg2 : (0 : ℝ) < g ^ 2 := by positivity
  calc b g m ≤ 329 * g * oddPrimeCount g + (10 * m + 29) * g := b_le_of_le h327
    _ ≤ 329 * g * (2 * √g + (8 * g + 4) / m) + (10 * m + 29) * g := by
        have : 329 * (g : ℝ) * oddPrimeCount g ≤ 329 * g * (2 * √g + (8 * g + 4) / m) :=
          mul_le_mul_of_nonneg_left ht (by positivity)
        linarith
    _ = 658 * g * √g + 329 * g * ((8 * g + 4) / m) + (10 * m + 29) * g := by ring
    _ ≤ g ^ 2 / 1000000 + (2632 * g ^ 2 / 10529 + g ^ 2 / 1000000) + g ^ 2 / 1000000 := by
        linarith
    _ < g ^ 2 / 4 := by linarith

/-! ### The `m`-free form of the bound -/

/-- With `g = 2^m - 1`, the exact dyadic count gives `b'(g, m) = (328 g + 327) t + (45 g + 13)/2`. -/
theorem b'_eq {g m : ℕ} (hm : 1 ≤ m) (hg : g = 2 ^ m - 1) :
    b' g m = (328 * g + 327) * oddPrimeCount g + (45 * g + 13) / 2 := by
  have hQ : 2 ^ m = 2 * 2 ^ (m - 1) := by rw [← pow_succ']; congr 1; omega
  have h1 : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  have hX : ((2 ^ (m - 1) - 1 : ℕ) : ℝ) = ((2 ^ (m - 1) : ℕ) : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  have hgR : (g : ℝ) = 2 * ((2 ^ (m - 1) : ℕ) : ℝ) - 1 := by
    rw [hg, hQ, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_one]
    norm_num
  unfold b'
  rw [hX, hgR]
  ring

/-- `b' ≤ b`: the exact count `2^(m-1) - 1` is at most the paper's `2gm`. -/
theorem b'_le_b {g m : ℕ} (hm : 4 ≤ m) (hg : g = 2 ^ m - 1) : b' g m ≤ b g m := by
  have h := (Combinatorics.dyadic_component_le m hm).1.trans
    (Combinatorics.dyadic_component_le m hm).2
  rw [← hg] at h
  have hR : ((2 ^ (m - 1) - 1 : ℕ) : ℝ) ≤ 2 * g * m := by exact_mod_cast h
  unfold b b'
  nlinarith

/-- The `m`-free bound is below `g²/4` in the same range. -/
theorem b'_lt_quarter_sq {g m : ℕ} (hm : 10529 ≤ m) (hg : g = 2 ^ m - 1) :
    b' g m < (g : ℝ) ^ 2 / 4 :=
  (b'_le_b (by omega) hg).trans_lt (b_lt_quarter_sq hm hg)

end GSArith.Numeric

end
