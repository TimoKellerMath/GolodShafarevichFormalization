/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import GSArith.Ledger

/-!
# `H²(Γ, 𝔽₂)` with trivial coefficients: module structure and inflation

Throughout the paper, `H²(Γ, 𝔽₂)` denotes continuous cochain cohomology of a profinite (or
finite) group `Γ` with coefficients in `𝔽₂` carrying the trivial action.  TauCeti's
`TauCeti.ContCohomology.H2` is the general explicit low-degree theory; this file specializes
it to the paper's setting:

* `GSArith.Profinite.trivialDistribMulAction`: the trivial action, to be installed as a
  *local* instance (a global one would clash with `𝔽₂` acting on itself), exactly as TauCeti
  does for its multiplicative counterpart;
* `H2 G (ZMod 2)` is an `𝔽₂`-vector space (every element is killed by `2`), finite-dimensional
  when `G` is finite;
* `GSArith.Profinite.infl q`: inflation (pullback) along a continuous homomorphism
  `q : Γ →ₜ* H`, as an `𝔽₂`-linear map `H²(H, 𝔽₂) → H²(Γ, 𝔽₂)`;
* every class has a normalized representative `c` with `c (1, 1) = 0`.
-/

@[expose] public section

namespace GSArith.Profinite

open TauCeti.ContCohomology

/-! ### The trivial action -/

/-- The trivial action `g • m = m` of a monoid `G` on an additive monoid `M`.  Not a global
instance: install it with `attribute [local instance] GSArith.Profinite.trivialDistribMulAction`
where the paper's `H²(Γ, 𝔽₂)` is meant. -/
abbrev trivialDistribMulAction (G M : Type*) [Monoid G] [AddMonoid M] : DistribMulAction G M where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

section TrivialAction

variable {G M : Type*} [Monoid G] [AddMonoid M]

attribute [local instance] trivialDistribMulAction

@[simp] theorem trivialDistribMulAction_smul (g : G) (m : M) : g • m = m := rfl

/-- The trivial action is continuous. -/
abbrev trivialContinuousSMul [TopologicalSpace G] [TopologicalSpace M] : ContinuousSMul G M :=
  ⟨by
    simp only [trivialDistribMulAction_smul]
    exact continuous_snd⟩

end TrivialAction

/-! ### `H²(G, 𝔽₂)` as an `𝔽₂`-vector space -/

section ModuleH2

variable (G : Type*) [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

theorem two_nsmul_eq_zero_H2 (x : H2 G (ZMod 2)) : (2 : ℕ) • x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    rw [← QuotientAddGroup.mk_nsmul]
    have hz : (2 : ℕ) • z = 0 := Subtype.ext (funext fun p => by
      simp [two_nsmul, CharTwo.add_self_eq_zero])
    rw [hz, QuotientAddGroup.mk_zero]

/-- `H²(G, 𝔽₂)` is an `𝔽₂`-vector space. -/
noncomputable instance instModuleH2 : Module (ZMod 2) (H2 G (ZMod 2)) :=
  AddCommGroup.zmodModule (two_nsmul_eq_zero_H2 G)

/-- For finite `G`, `H²(G, 𝔽₂)` is finite (hence finite-dimensional). -/
instance instFiniteH2 [Finite G] : Finite (H2 G (ZMod 2)) := inferInstance

end ModuleH2

/-! ### Inflation along a continuous homomorphism -/

section Inflation

variable {Γ H : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ]
  [Group H] [TopologicalSpace H] [ContinuousMul H]
  (M : Type*) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

attribute [local instance] trivialDistribMulAction trivialContinuousSMul

/-- Inflation (pullback of cocycles) along a continuous homomorphism `q : Γ →ₜ* H`, on
`H²(-, M)` with trivial coefficients. -/
noncomputable def infl (q : Γ →ₜ* H) : H2 H M →+ H2 Γ M :=
  explicitMap2 H M Γ M q (AddMonoidHom.id M) continuous_id (fun _ _ => rfl)

/-- Inflation on the class of a cocycle is the class of the pulled-back cocycle. -/
theorem infl_mk (q : Γ →ₜ* H) (c : Z2 H M) :
    infl M q (H2pi H M c) =
      H2pi Γ M (cocyclesMap2 H M Γ M q (AddMonoidHom.id M) continuous_id (fun _ _ => rfl) c) :=
  explicitMap2_mk H M Γ M q _ _ _ c

/-- Inflation along the identity is the identity. -/
theorem infl_id : infl M (ContinuousMonoidHom.id H) = AddMonoidHom.id (H2 H M) :=
  explicitMap2_id H M

/-- Inflation on `H²(-, 𝔽₂)` as an `𝔽₂`-linear map. -/
noncomputable def inflₗ (q : Γ →ₜ* H) : H2 H (ZMod 2) →ₗ[ZMod 2] H2 Γ (ZMod 2) :=
  (infl (ZMod 2) q).toZModLinearMap 2

@[simp] theorem inflₗ_apply (q : Γ →ₜ* H) (x : H2 H (ZMod 2)) :
    inflₗ q x = infl (ZMod 2) q x := rfl

end Inflation

/-! ### The class map -/

section ClassMap

variable {G M : Type*} [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- `TauCeti.ContCohomology.H2pi_eq_zero_iff`, phrased with `H2pi`. -/
theorem H2pi_eq_zero_iff' {f : Z2 G M} : H2pi G M f = 0 ↔ (f : G × G → M) ∈ B2 G M :=
  H2pi_eq_zero_iff

end ClassMap

/-! ### Normalized representatives -/

section Normalized

variable {G M : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

attribute [local instance] trivialDistribMulAction trivialContinuousSMul

/-- With trivial coefficients, every class in `H²(G, M)` is represented by a cocycle `c` with
`c (1, 1) = 0` (hence `c (1, g) = c (g, 1) = 0` for all `g`): subtract the coboundary of the
constant cochain `c (1, 1)`. -/
theorem exists_normalized_rep (x : H2 G M) :
    ∃ c : Z2 G M, H2pi G M c = x ∧ (c : G × G → M) (1, 1) = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    let b : G → M := fun _ => (z : G × G → M) (1, 1)
    have hb : d1 G M b ∈ B2 G M := mem_B2_iff.mpr ⟨b, continuous_const, rfl⟩
    refine ⟨z - ⟨d1 G M b, B2_le_Z2 G M hb⟩, ?_, ?_⟩
    · rw [map_sub]
      change H2pi G M z - H2pi G M ⟨d1 G M b, B2_le_Z2 G M hb⟩ = H2pi G M z
      rw [sub_eq_self]
      exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr hb)
    · simp [b, d1_apply]

end Normalized

end GSArith.Profinite

end
