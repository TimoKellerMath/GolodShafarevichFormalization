/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Module.Defs

/-!
# `𝔽₂`-linear combinations are subset sums

The one fact about `𝔽₂ = ZMod 2`-modules used throughout: a linear combination
`∑ cᵢ • vᵢ` with `cᵢ ∈ 𝔽₂` is the sum of the `vᵢ` over `{i | cᵢ = 1}`.  This turns linear
(in)dependence over `𝔽₂` into statements about subset sums (TauCeti does the same for
square classes in `TauCeti.linearIndependent_squareClass_iff`).
-/

@[expose] public section

namespace GSArith.LinearAlgebra

theorem zmod_two_eq_zero_or_one (t : ZMod 2) : t = 0 ∨ t = 1 := by revert t; decide

/-- A `𝔽₂`-linear combination is the subset sum over the coefficients equal to `1`. -/
theorem sum_zmod_two_smul {ι M : Type*} [Fintype ι] [AddCommMonoid M] [Module (ZMod 2) M]
    (c : ι → ZMod 2) (f : ι → M) :
    ∑ i, c i • f i = ∑ i ∈ Finset.univ.filter (fun i => c i = 1), f i := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases zmod_two_eq_zero_or_one (c i) with h0 | h1
  · rw [h0, ite_eq_right_iff.mpr (fun h => absurd h (by decide))]; exact zero_smul _ _
  · rw [h1, one_smul]; simp

end GSArith.LinearAlgebra

end
