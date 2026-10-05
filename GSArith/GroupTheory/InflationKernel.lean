/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Profinite.TrivialCoefficients
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Inflation into a smaller cohomology group has a nonzero kernel

The dimension-counting step of Proposition 2.34 of Dérickx–Gillibert–Keller–Pagano,
*Golod–Shafarevich for arithmetic surfaces*: if `dim_{𝔽₂} H²(Γ, 𝔽₂) < dim_{𝔽₂} H²(H, 𝔽₂)`,
then inflation along any continuous homomorphism `q : Γ →ₜ* H` kills a nonzero class.  This
is rank–nullity for the `𝔽₂`-linear map `inflₗ q`.

The paper takes `H²(Γ, 𝔽₂)` finite-dimensional for granted (it comes from Proposition 3.17);
here it is an explicit hypothesis, without which `finrank` would be `0` and the statement
false.
-/

@[expose] public section

namespace GSArith.Profinite

open TauCeti.ContCohomology

variable {Γ H : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ]
  [Group H] [TopologicalSpace H] [ContinuousMul H]

attribute [local instance] trivialDistribMulAction trivialContinuousSMul

/-- If `H²(Γ, 𝔽₂)` is finite-dimensional of dimension less than that of `H²(H, 𝔽₂)`, inflation
along `q : Γ →ₜ* H` has a nonzero kernel. -/
theorem exists_ne_zero_infl_eq_zero [Module.Finite (ZMod 2) (H2 Γ (ZMod 2))] (q : Γ →ₜ* H)
    (hdim : Module.finrank (ZMod 2) (H2 Γ (ZMod 2)) <
      Module.finrank (ZMod 2) (H2 H (ZMod 2))) :
    ∃ θ : H2 H (ZMod 2), θ ≠ 0 ∧ infl (ZMod 2) q θ = 0 := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (inflₗ q) :=
    (injective_iff_map_eq_zero (inflₗ q)).mpr fun θ hθ => by
      by_contra hne
      exact hcon θ hne hθ
  have := LinearMap.finrank_le_finrank_of_injective hinj
  omega

end GSArith.Profinite

end
