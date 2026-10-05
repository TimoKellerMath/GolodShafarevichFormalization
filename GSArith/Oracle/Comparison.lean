/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Colimit
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.DegreeTwoDescent
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Algebra.Field.ZMod
public import GSArith.Profinite.TrivialCoefficients
public import GSArith.LinearAlgebra.ZModTwo

/-!
# Comparison with continuous group cohomology (Proposition 2.29)

Proposition 2.29 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic
surfaces*, is the injection `H²_cts(Π, 𝔽₂) ↪ H²_G(T)`.  Its proof has two halves.

* **Tier C** (descent and the spectral sequence).  For each admissible finite Galois `M/K`
  containing `L = ℚ(T)`, with `H_M = Gal(M/K)` and `T_M` the normalization of `T` in `M`, descent
  along the `A_M`-torsor `T_M → T` identifies `H^i_{H_M}(T_M)` with `H^i_G(T)`, and the five-term
  sequence of the bar spectral sequence gives edge maps
  `e_M : H²(H_M, 𝔽₂) → H²_G(T)` compatible under inflation, whose kernel is the image of the
  transgression from `H¹_ét(T_M, 𝔽₂)^{H_M}`.  A class in that kernel is represented by a torsor
  which splits on an admissible cover `T_{M'}`, so by naturality of transgression it inflates to
  zero in `H²(H_{M'}, 𝔽₂)`.

* **Tier A** (continuous cochains).  Every continuous cochain factors through a finite quotient,
  so `H²_cts(Π, 𝔽₂)` is the filtered colimit of the `H²(H_M, 𝔽₂)`; the edge maps then assemble
  to an injection.

This file records the Tier-C half as the interface `GSArith.Oracle.ComparisonSituation` — the
edge maps `e`, their compatibility `e_transition`, and the kernel-killing property `e_eq_zero`,
the latter two ledgered — and **proves the Tier-A half** from TauCeti's degree-two descent
(`TauCeti.ContCohomology.exists_explicitInfl2_eq`: every class of `H²(Γ, 𝔽₂)` is inflated from
some open normal subgroup) and the compatibility of inflation with the finite-level transitions
(`explicitInfl2_explicitFiniteQuotientTransition2`):

* `GSArith.Oracle.ComparisonSituation.card_le_of_linearIndependent`: a linearly independent
  finite family in `H²_cts(Γ, 𝔽₂)` has at most `dim H²_G(T)` members;
* `GSArith.Oracle.ComparisonSituation.finite_H2` and `finrank_H2_le`: `H²_cts(Γ, 𝔽₂)` is
  finite-dimensional of dimension at most `h²_G(T)`.

The argument avoids the injectivity half of the colimit (which TauCeti does not provide in
degree two at the pinned revision): a putative independent family is inflated from a common
finite level `W`, its images in `H²_G(T)` are dependent by dimension, the corresponding subset
sum lies in `ker e_W`, so it dies at a deeper level `W'`, and the same subset sum of the original
family is inflated from that zero — contradicting independence.  Only surjectivity, additivity
and compatibility are used.

The paper's edge maps are only defined at levels below `N₀ = ker(Π → G)` (the levels `M ⊇ L`);
the interface carries that subgroup and only assumes the maps there.
-/

@[expose] public section

namespace GSArith.Oracle

open TauCeti.ContCohomology GSArith.Profinite GSArith.LinearAlgebra

universe u

-- The trivial-action instance is file-wide; no `•` with `𝔽₂` scalars on a module is written
-- below it (it would be captured), which is why `sum_zmod_two_smul` lives in
-- `GSArith.LinearAlgebra.ZModTwo` and is only *applied* here.
attribute [local instance] trivialDistribMulAction trivialContinuousSMul

/-! ### The finite levels -/

variable (Γ : Type u) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- The finite-level cohomology `H²(Γ/U, 𝔽₂)` at an open normal subgroup `U`, in TauCeti's
convention with coefficients in the `U`-invariants of `𝔽₂` (all of `𝔽₂`, since the action is
trivial). -/
abbrev H2Level (U : OpenNormalSubgroup Γ) : Type u :=
  H2 (Γ ⧸ U.toSubgroup) (FixedPoints.addSubgroup U.toSubgroup (ZMod 2))

/-- Inflation from the level `U` to `H²_cts(Γ, 𝔽₂)`. -/
noncomputable abbrev levelInfl (U : OpenNormalSubgroup Γ) : H2Level Γ U →+ H2 Γ (ZMod 2) :=
  explicitInfl2 Γ (ZMod 2) U.toSubgroup

/-- Inflation between finite levels, from `U` to the deeper `U' ≤ U`. -/
noncomputable abbrev levelTransition {U U' : OpenNormalSubgroup Γ} (h : U' ≤ U) :
    H2Level Γ U →+ H2Level Γ U' :=
  explicitFiniteQuotientTransition2 Γ (ZMod 2) U U' h

/-- Inflating to a deeper level and then to `Γ` is inflating to `Γ`. -/
theorem levelInfl_levelTransition {U U' : OpenNormalSubgroup Γ} (h : U' ≤ U) (y : H2Level Γ U) :
    levelInfl Γ U' (levelTransition Γ h y) = levelInfl Γ U y :=
  explicitInfl2_explicitFiniteQuotientTransition2 h y

/-! ### The interface -/

/-- **The Tier-C half of Proposition 2.29.**  The equivariant cohomology `V = H²_G(T)`
(an `𝔽₂`-vector space of dimension `h2 = h²_G(T)`), the open normal subgroup
`N₀ = ker(Π → G)`, and for every level `U ≤ N₀` the edge map `e_U : H²(Γ/U, 𝔽₂) → H²_G(T)`,
compatible with inflation and with kernel killed at a deeper level. -/
structure ComparisonSituation (h2 : ℕ) where
  /-- `H²_G(T)` -/
  V : Type u
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module (ZMod 2) V]
  [instFinite : Module.Finite (ZMod 2) V]
  /-- its dimension is the record's `h²_G(T)` -/
  finrank_V : Module.finrank (ZMod 2) V = h2
  /-- `ker(Π → G)`: the levels `M ⊇ L` are the open normal subgroups below it -/
  N₀ : OpenNormalSubgroup Γ
  /-- the edge maps `e_M : H²(H_M, 𝔽₂) → H²_G(T)` of the bar spectral sequence -/
  e : ∀ U : OpenNormalSubgroup Γ, U ≤ N₀ → H2Level Γ U →+ V
  -- OBLIGATION[stacks:03AG,03RV,025P][tier:C][crit:yes][prop:2.29] edge maps compatible
  e_transition : ∀ (U U' : OpenNormalSubgroup Γ) (hU : U ≤ N₀) (hU' : U' ≤ N₀) (h : U' ≤ U)
    (y : H2Level Γ U), e U' hU' (levelTransition Γ h y) = e U hU y
  -- OBLIGATION[stacks:03AG,03RV][tier:C][crit:yes][prop:2.29] ker e_M dies at a deeper level
  e_eq_zero : ∀ (U : OpenNormalSubgroup Γ) (hU : U ≤ N₀) (y : H2Level Γ U), e U hU y = 0 →
    ∃ (U' : OpenNormalSubgroup Γ) (h : U' ≤ U), levelTransition Γ h y = 0

attribute [instance] ComparisonSituation.instAddCommGroup ComparisonSituation.instModule
  ComparisonSituation.instFinite

namespace ComparisonSituation

variable {Γ} [CompactSpace Γ] [TotallyDisconnectedSpace Γ] {h2 : ℕ}

/-- **Proposition 2.29, the Tier-A half.**  A linearly independent finite family in
`H²_cts(Γ, 𝔽₂)` has at most `h²_G(T)` members. -/
theorem card_le_of_linearIndependent (S : ComparisonSituation Γ h2)
    (s : Finset (H2 Γ (ZMod 2)))
    (hs : LinearIndependent (ZMod 2) (fun x : s => (x : H2 Γ (ZMod 2)))) : s.card ≤ h2 := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  -- every member is inflated from a finite level
  have hx : ∀ x : s, ∃ (U : OpenNormalSubgroup Γ) (y : H2Level Γ U), levelInfl Γ U y = x :=
    fun x => exists_explicitInfl2_eq (x : H2 Γ (ZMod 2))
  choose U y hy using hx
  -- a common level `W` below `N₀`
  have huniv : (Finset.univ : Finset s).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨_, hne.choose_spec⟩⟩
  let W : OpenNormalSubgroup Γ := Finset.univ.inf' huniv U ⊓ S.N₀
  have hWN : W ≤ S.N₀ := inf_le_right
  have hWU : ∀ x : s, W ≤ U x := fun x =>
    inf_le_left.trans (Finset.inf'_le U (Finset.mem_univ x))
  let z : s → H2Level Γ W := fun x => levelTransition Γ (hWU x) (y x)
  have hz : ∀ x : s, levelInfl Γ W (z x) = x := fun x => by
    rw [levelInfl_levelTransition]; exact hy x
  -- the images in `H²_G(T)` are independent
  let v : s → S.V := fun x => S.e W hWN (z x)
  have hv : LinearIndependent (ZMod 2) v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∑ x ∈ Finset.univ.filter (fun x => c x = 1), v x = 0 :=
      (sum_zmod_two_smul c v).symm.trans hc
    have hsum : S.e W hWN (∑ x ∈ Finset.univ.filter (fun x => c x = 1), z x) = 0 := by
      rw [map_sum]; exact hc'
    obtain ⟨W', hW', hzero⟩ := S.e_eq_zero W hWN _ hsum
    -- the same subset sum of the original family is inflated from that zero
    have key : ∑ x ∈ Finset.univ.filter (fun x => c x = 1), (x : H2 Γ (ZMod 2)) = 0 := by
      calc ∑ x ∈ Finset.univ.filter (fun x => c x = 1), (x : H2 Γ (ZMod 2))
          = ∑ x ∈ Finset.univ.filter (fun x => c x = 1),
              levelInfl Γ W' (levelTransition Γ hW' (z x)) := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [levelInfl_levelTransition, hz x]
        _ = levelInfl Γ W' (levelTransition Γ hW'
              (∑ x ∈ Finset.univ.filter (fun x => c x = 1), z x)) := by
            rw [map_sum, map_sum]
        _ = 0 := by rw [hzero, map_zero]
    exact Fintype.linearIndependent_iff.mp hs c
      ((sum_zmod_two_smul c fun x : s => (x : H2 Γ (ZMod 2))).trans key)
  have h := hv.fintype_card_le_finrank
  rw [S.finrank_V, Fintype.card_coe] at h
  exact h

/-- `rank H²_cts(Γ, 𝔽₂) ≤ h²_G(T)`. -/
theorem rank_H2_le (S : ComparisonSituation Γ h2) : Module.rank (ZMod 2) (H2 Γ (ZMod 2)) ≤ h2 :=
  rank_le fun s hs => S.card_le_of_linearIndependent s hs

/-- **`H²_cts(Γ, 𝔽₂)` is finite-dimensional** (the finiteness input of Proposition 3.17). -/
theorem finite_H2 (S : ComparisonSituation Γ h2) : Module.Finite (ZMod 2) (H2 Γ (ZMod 2)) :=
  Module.rank_lt_aleph0_iff.mp (S.rank_H2_le.trans_lt Cardinal.natCast_lt_aleph0)

/-- **Proposition 2.29, in dimensions.**  `dim H²_cts(Γ, 𝔽₂) ≤ h²_G(T)`. -/
@[gs_public]
theorem finrank_H2_le (S : ComparisonSituation Γ h2) :
    Module.finrank (ZMod 2) (H2 Γ (ZMod 2)) ≤ h2 :=
  Module.finrank_le_of_rank_le S.rank_H2_le

end ComparisonSituation

end GSArith.Oracle

end
