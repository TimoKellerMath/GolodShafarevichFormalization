/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Profinite.Lifting

/-!
# The field embedding obstruction (Proposition 2.30), general form

Proposition 2.30 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic
surfaces*: for a finite Galois extension `M/K` with group `H`, `q : G_K ↠ H`, and a central
extension classified by `θ ∈ H²(H, 𝔽₂)`, a continuous lift of `q` exists iff `q^*θ = 0` in
`H²_cts(G_K, 𝔽₂)`, and the lifts form a torsor under `Hom_cts(G_K, 𝔽₂)`.

The first half is the profinite lifting lemma `GSArith.Profinite.CentralExt.exists_lift_iff`
for an arbitrary topological group in place of `G_K`; the identification
`H²_cts(G_K, 𝔽₂) = Br(K)[2]` mentioned in the paper is not load-bearing (LEAN-PLAN.md, P31)
and is not formalized.  This file proves the second half, in the explicit model `E_c`: two
lifts differ by a continuous homomorphism `Γ → M`, and adding a continuous homomorphism to a
lift gives a lift.  Off the critical path (LEAN-PLAN.md §2).
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

omit [Group Γ] [ContinuousMul Γ] in
/-- A map into the discrete group `E_c` with continuous coordinates is continuous. -/
theorem continuous_mk (b : Γ → M) (s : Γ → H) (hb : Continuous b) (hs : Continuous s) :
    Continuous (fun γ => (⟨b γ, s γ⟩ : CentralExt c)) := by
  rw [continuous_discrete_rng]
  rintro ⟨m, h⟩
  have hpre : (fun γ => (⟨b γ, s γ⟩ : CentralExt c)) ⁻¹' {⟨m, h⟩} = b ⁻¹' {m} ∩ s ⁻¹' {h} := by
    ext γ; simp [CentralExt.ext_iff]
  rw [hpre]
  exact (hb.isOpen_preimage _ (isOpen_discrete _)).inter (hs.isOpen_preimage _ (isOpen_discrete _))

/-- The `M`-coordinate of a lift. -/
def liftFst (q' : Γ →ₜ* CentralExt c) : Γ → M := fun γ => (q' γ).fst

omit [DiscreteTopology H] [DiscreteTopology M] [ContinuousMul Γ] in
theorem continuous_liftFst (q' : Γ →ₜ* CentralExt c) : Continuous (liftFst q') :=
  continuous_of_discreteTopology.comp q'.continuous

omit [DiscreteTopology H] [DiscreteTopology M] [ContinuousMul Γ] in
theorem liftFst_mul (q' : Γ →ₜ* CentralExt c) (γ δ : Γ) :
    liftFst q' (γ * δ) = liftFst q' γ + liftFst q' δ + c.fn ((q' γ).snd, (q' δ).snd) := by
  simp [liftFst, map_mul]

omit [DiscreteTopology H] [ContinuousMul Γ] in
/-- **Proposition 2.30, second half.**  Two continuous lifts of `q` differ by a continuous
homomorphism `Γ → M`. -/
theorem exists_hom_of_lifts (q : Γ →ₜ* H) (q₁ q₂ : Γ →ₜ* CentralExt c)
    (h₁ : (projₜ c).comp q₁ = q) (h₂ : (projₜ c).comp q₂ = q) :
    ∃ χ : Γ → M, Continuous χ ∧ (∀ γ δ, χ (γ * δ) = χ γ + χ δ) ∧
      ∀ γ, liftFst q₁ γ = liftFst q₂ γ + χ γ := by
  refine ⟨fun γ => liftFst q₁ γ - liftFst q₂ γ, (continuous_liftFst q₁).sub (continuous_liftFst q₂),
    ?_, fun γ => by simp⟩
  intro γ δ
  have hs₁ : ∀ γ, (q₁ γ).snd = q γ := fun γ => DFunLike.congr_fun h₁ γ
  have hs₂ : ∀ γ, (q₂ γ).snd = q γ := fun γ => DFunLike.congr_fun h₂ γ
  simp only [liftFst_mul, hs₁, hs₂]
  abel

/-- Twisting a lift by a continuous homomorphism `χ : Γ → M`. -/
noncomputable def twist (q' : Γ →ₜ* CentralExt c) (χ : Γ → M) (hχc : Continuous χ)
    (hχ : ∀ γ δ, χ (γ * δ) = χ γ + χ δ) : Γ →ₜ* CentralExt c :=
  ⟨MonoidHom.mk' (fun γ => ⟨(q' γ).fst + χ γ, (q' γ).snd⟩) (fun γ δ => by
      ext
      · simp only [mul_fst, map_mul, hχ]
        abel
      · simp [map_mul]),
    continuous_mk _ _ ((continuous_liftFst q').add hχc)
      (continuous_of_discreteTopology.comp q'.continuous)⟩

omit [ContinuousMul Γ] in
@[simp] theorem twist_apply (q' : Γ →ₜ* CentralExt c) (χ : Γ → M) (hχc : Continuous χ)
    (hχ : ∀ γ δ, χ (γ * δ) = χ γ + χ δ) (γ : Γ) :
    twist q' χ hχc hχ γ = ⟨(q' γ).fst + χ γ, (q' γ).snd⟩ := rfl

omit [ContinuousMul Γ] in
/-- The twist of a lift of `q` is again a lift of `q`. -/
theorem projₜ_comp_twist (q : Γ →ₜ* H) (q' : Γ →ₜ* CentralExt c) (hq' : (projₜ c).comp q' = q)
    (χ : Γ → M) (hχc : Continuous χ) (hχ : ∀ γ δ, χ (γ * δ) = χ γ + χ δ) :
    (projₜ c).comp (twist q' χ hχc hχ) = q :=
  ContinuousMonoidHom.ext fun γ => DFunLike.congr_fun hq' γ

end CentralExt

end GSArith.Profinite

end
