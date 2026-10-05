/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Profinite.TrivialCoefficients
public import GSArith.GroupTheory.CentralExtension

/-!
# Lifting a finite quotient along a central extension

The profinite lifting lemma underlying Propositions 2.30 and 2.34 of
Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic surfaces*.

Let `Γ` be a topological group, `q : Γ →ₜ* H` a continuous homomorphism to a discrete group
`H`, and `θ ∈ H²(H, M)` (trivial coefficients) represented by a normalized cocycle `c`.  The
class `θ` classifies the central extension

  `E_c = M × H`,   `(a, g) · (b, h) = (a + b + c(g, h), g h)`,

and the paper's cocycle equation `db = q^* c` says exactly that a continuous lift
`q̃ : Γ → E_c` of `q` exists if and only if the inflation `q^* θ` vanishes in `H²(Γ, M)`.
Taking `Γ = H` and `q = id` gives the classical statement that `E_c → H` splits iff `θ = 0`.

## Main definitions and results

* `GSArith.Profinite.NormalizedCocycle H M`: a continuous `2`-cocycle with `c (1, 1) = 0`;
  every class has such a representative (`GSArith.Profinite.exists_normalized_rep`).
* `GSArith.Profinite.CentralExt c`: the group `E_c`, with projection
  `GSArith.Profinite.CentralExt.proj c : E_c →* H`, whose kernel is central and isomorphic to
  `M` (`CentralExt.kerEquiv`), and `CentralExt.isCentralExtensionByTwo` when `|M| = 2`.
* `GSArith.Profinite.CentralExt.exists_lift_iff`: a continuous lift of `q` exists iff
  `infl M q [c] = 0`.
* `GSArith.Profinite.CentralExt.splits_iff`: `E_c → H` splits iff `[c] = 0`.
-/

@[expose] public section

namespace GSArith.Profinite

open TauCeti.ContCohomology GSArith.GroupTheory

variable {H M : Type*} [Group H] [TopologicalSpace H] [ContinuousMul H]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]

attribute [local instance] trivialDistribMulAction trivialContinuousSMul

/-! ### Normalized cocycles -/

/-- A normalized continuous `2`-cocycle of `H` with trivial coefficients in `M`:
`c ∈ Z²(H, M)` with `c (1, 1) = 0`. -/
structure NormalizedCocycle (H M : Type*) [Group H] [TopologicalSpace H] [ContinuousMul H]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] where
  /-- The underlying cocycle. -/
  toZ2 : Z2 H M
  /-- Normalization. -/
  map_one_one : (toZ2 : H × H → M) (1, 1) = 0

namespace NormalizedCocycle

variable (c : NormalizedCocycle H M)

/-- The underlying function `H × H → M`. -/
def fn : H × H → M := c.toZ2

theorem fn_one_one : c.fn (1, 1) = 0 := c.map_one_one

theorem fn_one_fst (h : H) : c.fn (1, h) = 0 := by
  unfold fn; rw [map_one_fst_of_mem_Z2 c.toZ2.2]; exact c.map_one_one

theorem fn_one_snd (h : H) : c.fn (h, 1) = 0 := by
  unfold fn; rw [map_one_snd_of_mem_Z2 c.toZ2.2]; exact c.map_one_one

/-- The cocycle identity, for the trivial action. -/
theorem cocycle (g h k : H) :
    c.fn (h, k) - c.fn (g * h, k) + c.fn (g, h * k) - c.fn (g, h) = 0 := by
  have h₀ := (mem_Z2_iff.mp c.toZ2.2).2 g h k
  rw [trivialDistribMulAction_smul] at h₀
  have h₁ : c.fn (g * h, k) + c.fn (g, h) = c.fn (h, k) + c.fn (g, h * k) := h₀
  rw [← sub_eq_zero] at h₁
  calc c.fn (h, k) - c.fn (g * h, k) + c.fn (g, h * k) - c.fn (g, h)
      = -(c.fn (g * h, k) + c.fn (g, h) - (c.fn (h, k) + c.fn (g, h * k))) := by abel
    _ = 0 := by rw [h₁, neg_zero]

/-- The class of a normalized cocycle. -/
abbrev cls : H2 H M := H2pi H M c.toZ2

/-- Every class in `H²(H, M)` is the class of a normalized cocycle. -/
theorem exists_cls_eq (x : H2 H M) : ∃ c : NormalizedCocycle H M, c.cls = x := by
  obtain ⟨c, hc, h11⟩ := exists_normalized_rep x
  exact ⟨⟨c, h11⟩, hc⟩

end NormalizedCocycle

/-! ### The central extension `E_c` -/

/-- The central extension `E_c = M × H` attached to a normalized cocycle `c`, with
multiplication `(a, g)(b, h) = (a + b + c(g, h), gh)`. -/
@[ext]
structure CentralExt (c : NormalizedCocycle H M) where
  /-- The `M`-coordinate. -/
  fst : M
  /-- The `H`-coordinate. -/
  snd : H

namespace CentralExt

variable {c : NormalizedCocycle H M}

instance : Mul (CentralExt c) :=
  ⟨fun x y => ⟨x.fst + y.fst + c.fn (x.snd, y.snd), x.snd * y.snd⟩⟩

instance : One (CentralExt c) := ⟨⟨0, 1⟩⟩

instance : Inv (CentralExt c) :=
  ⟨fun x => ⟨-x.fst - c.fn (x.snd⁻¹, x.snd), x.snd⁻¹⟩⟩

@[simp] theorem mul_fst (x y : CentralExt c) :
    (x * y).fst = x.fst + y.fst + c.fn (x.snd, y.snd) := rfl

@[simp] theorem mul_snd (x y : CentralExt c) : (x * y).snd = x.snd * y.snd := rfl

@[simp] theorem one_fst : (1 : CentralExt c).fst = 0 := rfl

@[simp] theorem one_snd : (1 : CentralExt c).snd = 1 := rfl

@[simp] theorem inv_fst (x : CentralExt c) : x⁻¹.fst = -x.fst - c.fn (x.snd⁻¹, x.snd) := rfl

@[simp] theorem inv_snd (x : CentralExt c) : x⁻¹.snd = x.snd⁻¹ := rfl

instance : Group (CentralExt c) where
  mul_assoc x y z := by
    ext
    · simp only [mul_fst, mul_snd]
      have hc := c.cocycle x.snd y.snd z.snd
      rw [← sub_eq_zero,
        show x.fst + y.fst + c.fn (x.snd, y.snd) + z.fst + c.fn (x.snd * y.snd, z.snd) -
            (x.fst + (y.fst + z.fst + c.fn (y.snd, z.snd)) + c.fn (x.snd, y.snd * z.snd)) =
          -(c.fn (y.snd, z.snd) - c.fn (x.snd * y.snd, z.snd) + c.fn (x.snd, y.snd * z.snd) -
            c.fn (x.snd, y.snd)) by abel, hc, neg_zero]
    · simp only [mul_snd, mul_assoc]
  one_mul x := by ext <;> simp [c.fn_one_fst]
  mul_one x := by ext <;> simp [c.fn_one_snd]
  inv_mul_cancel x := by
    ext
    · simp only [mul_fst, inv_fst, inv_snd, one_fst]; abel
    · simp

/-- The projection `E_c → H`. -/
def proj (c : NormalizedCocycle H M) : CentralExt c →* H where
  toFun := CentralExt.snd
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem proj_apply (x : CentralExt c) : proj c x = x.snd := rfl

theorem proj_surjective (c : NormalizedCocycle H M) : Function.Surjective (proj c) :=
  fun h => ⟨⟨0, h⟩, rfl⟩

/-- The kernel of the projection is `M`, embedded as `a ↦ (a, 1)`. -/
def kerEquiv (c : NormalizedCocycle H M) : (proj c).ker ≃ M where
  toFun x := x.1.fst
  invFun a := ⟨⟨a, 1⟩, rfl⟩
  left_inv x := Subtype.ext (CentralExt.ext rfl (MonoidHom.mem_ker.mp x.2).symm)
  right_inv _ := rfl

theorem card_ker (c : NormalizedCocycle H M) : Nat.card (proj c).ker = Nat.card M :=
  Nat.card_congr (kerEquiv c)

/-- The kernel of the projection is central. -/
theorem ker_le_center (c : NormalizedCocycle H M) :
    (proj c).ker ≤ Subgroup.center (CentralExt c) := by
  intro x hx
  have hx' : x.snd = 1 := MonoidHom.mem_ker.mp hx
  rw [Subgroup.mem_center_iff]
  intro y
  ext
  · simp [hx', c.fn_one_fst, c.fn_one_snd, add_comm]
  · simp [hx']

/-- For `|M| = 2`, `E_c → H` is a central extension by `𝔽₂` in the sense of
`GSArith.GroupTheory.IsCentralExtensionByTwo`. -/
theorem isCentralExtensionByTwo (c : NormalizedCocycle H M) (hM : Nat.card M = 2) :
    IsCentralExtensionByTwo (proj c) :=
  ⟨proj_surjective c, by rw [card_ker, hM], ker_le_center c⟩

/-- `E_c ≃ M × H` as types. -/
def equivProd (c : NormalizedCocycle H M) : CentralExt c ≃ M × H where
  toFun x := (x.fst, x.snd)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_eq (c : NormalizedCocycle H M) :
    Nat.card (CentralExt c) = Nat.card M * Nat.card H := by
  rw [Nat.card_congr (equivProd c), Nat.card_prod]

instance [Finite M] [Finite H] : Finite (CentralExt c) :=
  Finite.of_equiv _ (equivProd c).symm

/-! ### Topology: `E_c` is discrete -/

instance : TopologicalSpace (CentralExt c) := ⊥

instance : DiscreteTopology (CentralExt c) := ⟨rfl⟩

instance : ContinuousMul (CentralExt c) := ⟨continuous_of_discreteTopology⟩

/-- The projection as a continuous homomorphism. -/
def projₜ (c : NormalizedCocycle H M) : CentralExt c →ₜ* H :=
  ⟨proj c, continuous_of_discreteTopology⟩

@[simp] theorem projₜ_apply (x : CentralExt c) : projₜ c x = x.snd := rfl

/-! ### The lifting lemma -/

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ]

/-- **The lifting lemma.**  A continuous lift `q̃ : Γ → E_c` of `q : Γ →ₜ* H` exists if and only
if the inflation of `[c]` to `H²(Γ, M)` vanishes. -/
theorem exists_lift_iff [DiscreteTopology H] [DiscreteTopology M] (q : Γ →ₜ* H)
    (c : NormalizedCocycle H M) :
    (∃ q' : Γ →ₜ* CentralExt c, (projₜ c).comp q' = q) ↔ infl M q c.cls = 0 := by
  rw [NormalizedCocycle.cls, infl_mk, H2pi_eq_zero_iff', mem_B2_iff]
  constructor
  · rintro ⟨q', hq'⟩
    have hsnd : ∀ γ, (q' γ).snd = q γ := fun γ => DFunLike.congr_fun hq' γ
    refine ⟨fun γ => -(q' γ).fst, (continuous_of_discreteTopology.comp q'.continuous).neg, ?_⟩
    funext p
    obtain ⟨γ, δ⟩ := p
    simp only [d1_apply, trivialDistribMulAction_smul, cocyclesMap2_apply, AddMonoidHom.id_apply]
    have hmul := congrArg CentralExt.fst (map_mul q' γ δ)
    rw [mul_fst, hsnd, hsnd] at hmul
    rw [hmul]
    change _ = c.fn (q γ, q δ)
    abel
  · rintro ⟨f, hf, hdf⟩
    have hrel : ∀ γ δ, f δ - f (γ * δ) + f γ = c.fn (q γ, q δ) := fun γ δ => by
      have := congrArg (fun F => F (γ, δ)) hdf
      simpa [d1_apply, trivialDistribMulAction_smul, cocyclesMap2_apply,
        NormalizedCocycle.fn] using this
    let b : Γ → M := fun γ => -f γ
    have hb : ∀ γ δ, b (γ * δ) = b γ + b δ + c.fn (q γ, q δ) := fun γ δ => by
      simp only [b]; rw [← hrel γ δ]; abel
    let q'' : Γ →* CentralExt c :=
      MonoidHom.mk' (fun γ => ⟨b γ, q γ⟩) (fun γ δ => by ext <;> simp [hb])
    have hcont : Continuous q'' := by
      rw [continuous_discrete_rng]
      rintro ⟨m, h⟩
      have hpre : (fun γ => (⟨b γ, q γ⟩ : CentralExt c)) ⁻¹' {⟨m, h⟩} = b ⁻¹' {m} ∩ q ⁻¹' {h} := by
        ext γ; simp [CentralExt.ext_iff]
      change IsOpen ((fun γ => (⟨b γ, q γ⟩ : CentralExt c)) ⁻¹' {⟨m, h⟩})
      rw [hpre]
      exact (hf.neg.isOpen_preimage _ (isOpen_discrete _)).inter
        (q.continuous.isOpen_preimage _ (isOpen_discrete _))
    exact ⟨⟨q'', hcont⟩, ContinuousMonoidHom.ext fun γ => rfl⟩

/-- **Splitting criterion.**  For discrete `H`, the central extension `E_c → H` splits if and
only if `[c] = 0` in `H²(H, M)`. -/
theorem splits_iff [DiscreteTopology H] [DiscreteTopology M] (c : NormalizedCocycle H M) :
    Splits (proj c) ↔ c.cls = 0 := by
  have h := exists_lift_iff (ContinuousMonoidHom.id H) c
  rw [infl_id, AddMonoidHom.id_apply] at h
  rw [← h]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨⟨σ, continuous_of_discreteTopology⟩,
      ContinuousMonoidHom.ext fun h => DFunLike.congr_fun hσ h⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ.toMonoidHom, MonoidHom.ext fun h => DFunLike.congr_fun hσ h⟩

end CentralExt

end GSArith.Profinite

end
