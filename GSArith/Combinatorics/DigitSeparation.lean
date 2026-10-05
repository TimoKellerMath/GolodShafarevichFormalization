/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Log
public import GSArith.Ledger

/-!
# Separating integers by `p`-adic digits

The counting core of Proposition 3.10 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich
for arithmetic surfaces*.  Starting from `ℙ¹` over `ℤ_(p)` with the sections `x = 0, …, N-1`,
one repeatedly blows up every special-fibre point met by at least two strict transforms.  The
centres of the `k`-th step are the residue classes mod `p^k` containing at least two of
`0, …, N-1`; there are at most `p^k` of them, and none once `p^k ≥ N`.  With
`e = ⌊log_p (N-1)⌋` the total number of centres is at most `∑_{k=1}^{e} p^k < p N/(p-1) ≤ 3N/2`
for odd `p`, and each centre adds one component, so the component count is `n_p ≤ 1 + 3N/2`.

Only the counting is formalized here; that each blow-up is at a smooth point of a reduced
nodal tree, adds one rational component and keeps the marked sections away from the nodes is
Tier C geometry, in the oracle interface.
-/

@[expose] public section

namespace GSArith.Combinatorics

open Finset

/-- The residue classes mod `p^k` containing at least two of `0, …, N-1`: the centres of the
`k`-th separation step. -/
def crowdedClasses (p k N : ℕ) : Finset ℕ :=
  (range (p ^ k)).filter fun c => 2 ≤ ((range N).filter fun a => a % p ^ k = c).card

theorem card_crowdedClasses_le (p k N : ℕ) : (crowdedClasses p k N).card ≤ p ^ k :=
  (card_filter_le _ _).trans (by simp)

/-- No residue class mod `p^k` is crowded once `p^k ≥ N`. -/
theorem crowdedClasses_eq_empty (p k N : ℕ) (h : N ≤ p ^ k) : crowdedClasses p k N = ∅ := by
  rw [crowdedClasses, filter_eq_empty_iff]
  intro c _ hc
  have hle : ((range N).filter fun a => a % p ^ k = c).card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    simp only [mem_filter, mem_range] at ha hb
    have ha' := ha.2
    have hb' := hb.2
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le ha.1 h)] at ha'
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hb.1 h)] at hb'
    omega
  omega

/-- `2 ∑_{k=1}^{e} p^k ≤ 3 (p^e - 1)` for `p ≥ 3`. -/
theorem two_mul_sum_pow_le (p : ℕ) (hp : 3 ≤ p) (e : ℕ) :
    2 * ∑ k ∈ Icc 1 e, p ^ k ≤ 3 * (p ^ e - 1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [sum_Icc_succ_top (by omega), mul_add]
    have h1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ (by omega)
    have h2 : 3 * p ^ e ≤ p ^ (e + 1) := by
      rw [pow_succ]
      exact (Nat.mul_le_mul_right (p ^ e) hp).trans_eq (mul_comm _ _)
    omega

/-- The total number of blow-up centres needed to separate the sections `0, …, N-1` at `p`. -/
def centreCount (p N : ℕ) : ℕ :=
  ∑ k ∈ Icc 1 (Nat.log p (N - 1)), (crowdedClasses p k N).card

/-- **Proposition 3.10, the count**: for odd `p ≥ 3` and `N ≥ 2`, the number of centres is less
than `3N/2`. -/
theorem two_mul_centreCount_lt (p : ℕ) (hp : 3 ≤ p) (N : ℕ) (hN : 2 ≤ N) :
    2 * centreCount p N < 3 * N := by
  unfold centreCount
  have hsum : ∑ k ∈ Icc 1 (Nat.log p (N - 1)), (crowdedClasses p k N).card ≤
      ∑ k ∈ Icc 1 (Nat.log p (N - 1)), p ^ k :=
    sum_le_sum fun k _ => card_crowdedClasses_le p k N
  have hlog : p ^ Nat.log p (N - 1) ≤ N - 1 := Nat.pow_log_le_self p (by omega)
  have := two_mul_sum_pow_le p hp (Nat.log p (N - 1))
  omega

/-- The component count `n_p = 1 + #centres` satisfies `n_p ≤ 1 + 3N/2`, i.e.
`2 n_p ≤ 2 + 3N`. -/
theorem two_mul_componentCount_le (p : ℕ) (hp : 3 ≤ p) (N : ℕ) (hN : 2 ≤ N) :
    2 * (1 + centreCount p N) ≤ 2 + 3 * N := by
  have := two_mul_centreCount_lt p hp N hN
  omega

end GSArith.Combinatorics

end
