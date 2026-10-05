/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import GSArith.Ledger

/-!
# Telescoping dimensions along a filtration (Proposition 3.8)

Proposition 3.8 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic
surfaces*: the three obstruction maps `o₁, o₂, o₃` measure successive quotients of the same
space of extension classes, `H² ⊇ V₁ = ker o₁ ⊇ V₂ = ker o₂ ⊇ ker o₃ = ker obs`, so

  `dim im obs = dim im o₁ + dim im o₂ + dim im o₃`.

This is pure linear algebra — rank–nullity three times — and is formalized as such: `o₂` is a
map out of `ker o₁`, `o₃` a map out of `ker o₂`, and the hypothesis identifies `ker obs` with
the image of `ker o₃` in the ambient space.  Off the critical path (LEAN-PLAN.md §2).
-/

@[expose] public section

namespace GSArith.LinearAlgebra

open Module LinearMap

variable {K W T₁ T₂ T₃ T : Type*} [Field K] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] [AddCommGroup T₁] [Module K T₁] [AddCommGroup T₂] [Module K T₂]
  [AddCommGroup T₃] [Module K T₃] [AddCommGroup T] [Module K T]

/-- **Proposition 3.8.**  For linear maps `o₁ : W → T₁`, `o₂ : ker o₁ → T₂`, `o₃ : ker o₂ → T₃`
and `obs : W → T` with `ker obs` the image of `ker o₃` in `W`,
`dim im obs = dim im o₁ + dim im o₂ + dim im o₃`. -/
theorem finrank_range_telescope (o₁ : W →ₗ[K] T₁) (o₂ : ker o₁ →ₗ[K] T₂)
    (o₃ : ker o₂ →ₗ[K] T₃) (obs : W →ₗ[K] T)
    (h : ker obs = (ker o₃).map ((ker o₁).subtype.comp (ker o₂).subtype)) :
    finrank K (range obs) = finrank K (range o₁) + finrank K (range o₂) + finrank K (range o₃) := by
  have hinj : Function.Injective ((ker o₁).subtype.comp (ker o₂).subtype) := by
    simp only [LinearMap.coe_comp, Submodule.coe_subtype]
    exact Subtype.val_injective.comp Subtype.val_injective
  have hker : finrank K (ker obs) = finrank K (ker o₃) := by
    rw [h]
    exact (Submodule.equivMapOfInjective _ hinj (ker o₃)).finrank_eq.symm
  have hA := finrank_range_add_finrank_ker obs
  have hB := finrank_range_add_finrank_ker o₁
  have hC := finrank_range_add_finrank_ker o₂
  have hD := finrank_range_add_finrank_ker o₃
  omega

end GSArith.LinearAlgebra

end
