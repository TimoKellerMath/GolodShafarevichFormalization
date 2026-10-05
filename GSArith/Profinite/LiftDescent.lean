/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Profinite.FieldEmbedding

/-!
# Descent of a lifted homomorphism (Proposition 2.31)

Proposition 2.31 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic
surfaces*: let `J ⊲ Γ` be a closed normal subgroup killed by `q : Γ ↠ H`, and `q̃` a lift of `q`
to a central extension by `𝔽₂`.  The restriction `λ = q̃|_J` lands in the central kernel and is a
homomorphism; its class in `Hom_cts(J, 𝔽₂)^Γ / res_J Hom_cts(Γ, 𝔽₂)` is independent of the
lift, and a lift factoring through `Γ/J` exists iff that class vanishes.

In the explicit model `E_c` (kernel `M`) this reads: a lift killing `J` exists iff the
restriction of the `M`-coordinate `liftFst q̃` to `J` is the restriction of a continuous
homomorphism `Γ → M`.  That is the statement proved here; the quotient by `res_J` is exactly
the freedom of twisting by characters of `Γ` (`GSArith.Profinite.CentralExt.twist`).
Normality and closedness of `J` are not needed for this form.  Off the critical path.
-/

@[expose] public section

namespace GSArith.Profinite

open TauCeti.ContCohomology

variable {H M : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H] [DiscreteTopology H]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] [DiscreteTopology M]
  {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ]

attribute [local instance] trivialDistribMulAction trivialContinuousSMul

namespace CentralExt

variable {c : NormalizedCocycle H M}

omit [DiscreteTopology H] [DiscreteTopology M] [ContinuousMul Γ] in
/-- On a subgroup killed by `q`, the `M`-coordinate of a lift is a homomorphism. -/
theorem liftFst_mul_of_mem (q : Γ →ₜ* H) (J : Subgroup Γ) (hJ : ∀ j ∈ J, q j = 1)
    (q' : Γ →ₜ* CentralExt c) (hq' : (projₜ c).comp q' = q) {j j' : Γ} (hj : j ∈ J)
    (hj' : j' ∈ J) : liftFst q' (j * j') = liftFst q' j + liftFst q' j' := by
  have hs : ∀ γ, (q' γ).snd = q γ := fun γ => DFunLike.congr_fun hq' γ
  rw [liftFst_mul, hs, hs, hJ j hj, hJ j' hj', c.fn_one_one, add_zero]

omit [ContinuousMul Γ] in
/-- **Proposition 2.31.**  A lift of `q` killing `J` exists iff the restriction to `J` of the
`M`-coordinate of the given lift is the restriction of a continuous homomorphism `Γ → M`. -/
theorem exists_lift_trivial_on_iff (q : Γ →ₜ* H) (J : Subgroup Γ) (hJ : ∀ j ∈ J, q j = 1)
    (q' : Γ →ₜ* CentralExt c) (hq' : (projₜ c).comp q' = q) :
    (∃ q'' : Γ →ₜ* CentralExt c, (projₜ c).comp q'' = q ∧ ∀ j ∈ J, q'' j = 1) ↔
      ∃ χ : Γ → M, Continuous χ ∧ (∀ γ δ, χ (γ * δ) = χ γ + χ δ) ∧
        ∀ j ∈ J, χ j = liftFst q' j := by
  constructor
  · rintro ⟨q'', hq'', hJ''⟩
    obtain ⟨χ, hχc, hχ, hdiff⟩ := exists_hom_of_lifts q q' q'' hq' hq''
    refine ⟨χ, hχc, hχ, fun j hj => ?_⟩
    have h0 : liftFst q'' j = 0 := by
      simp [liftFst, hJ'' j hj]
    rw [hdiff j, h0, zero_add]
  · rintro ⟨χ, hχc, hχ, hres⟩
    refine ⟨twist q' (fun γ => -χ γ) hχc.neg (fun γ δ => by rw [hχ]; abel),
      projₜ_comp_twist q q' hq' _ _ _, fun j hj => ?_⟩
    have hs : (q' j).snd = q j := DFunLike.congr_fun hq' j
    ext
    · simp only [twist_apply, one_fst]
      change liftFst q' j + -χ j = 0
      rw [hres j hj, add_neg_cancel]
    · simp [twist_apply, hs, hJ j hj]

end CentralExt

end GSArith.Profinite

end
