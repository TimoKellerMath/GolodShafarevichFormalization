/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Arithmetic.BranchClasses
public import TauCeti.NumberTheory.Multiquadratic.SquareClass.Independence

/-!
# The multiquadratic cover of Proposition 3.1 (its function-field content)

Proposition 3.1 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic
surfaces*: for `g ≥ 2`, `ℓ > g`, the curve `C : y² = F(x) = ∏_{i=0}^{g} (x - i)(x - i - ℓ)`
and `uᵢ = (x - i)(x - i - ℓ)/(x - g)²`, `0 ≤ i < g`, the extension
`L = K(√u₀, …, √u_{g-1})` of `K = ℚ(C) = ℚ(x)(√F)` has degree `2^g` and Galois group `𝔽₂^g`,
because the `uᵢ` are independent in `K^×/K^{×2}`.

This file proves that independence over any field `k` of characteristic zero, from
Proposition 2.16's square-class description (`GSArith.Arithmetic.BranchClasses`): a nonempty
product `∏_{i ∈ S} uᵢ` is `∏_{a ∈ E_S}(x - a)` times a square, with `E_S = ⋃_{i ∈ S}{i, i + ℓ}`
nonempty and omitting the last pair `{g, g + ℓ}`, so neither it nor its quotient by `F` is a
square in `k(x)`, hence it is not a square in `k(x)(√F)`.

* `GSArith.Arithmetic.not_isSquare_prod_uFun`: no nonempty subset product of the `uᵢ` is a
  square in `k(x)(√F)`;
* `GSArith.Arithmetic.linearIndependent_uUnit`: the square classes of the `uᵢ` are
  `𝔽₂`-linearly independent (`TauCeti.linearIndependent_squareClass_iff`);
* `GSArith.Arithmetic.finrank_adjoin_sqrt_uUnit`: `[K(√u₀, …, √u_{g-1}) : K] = 2^g` in any
  field containing the square roots (TauCeti's multiquadratic degree theorem).

The group-theoretic conclusions of Proposition 3.1 for the abstract group `Π_m` (`|G₀| = 2^g`,
`d(G₀) = g`, geometricity) remain fields of `GSArith.Oracle.PaperSetup`: they concern the
Galois group of the *curve* cover, whose identification with this field extension is Tier C.

Decidable equality on `k` is assumed explicitly (the branch set is a `Finset`); for `k = ℚ`
it is the standard instance.
-/

@[expose] public section

namespace GSArith.Arithmetic

open Polynomial TauCeti

variable {k : Type*} [Field k]

/-! ### Characteristic zero passes to `k(x)` and `k(x)(√F)` -/

instance instCharZeroRatFunc [CharZero k] : CharZero (RatFunc k) :=
  (RingHom.charZero_iff (RatFunc.algebraMap_injective k)).mp inferInstance

instance instCharZeroBranchExt [CharZero k] (B : Finset k) [Fact B.Nonempty] :
    CharZero (BranchExt B) :=
  (RingHom.charZero_iff (algebraMap (RatFunc k) (BranchExt B)).injective).mp inferInstance

/-! ### The branch points `{0, …, g} ∪ {ℓ, …, g + ℓ}` and the functions `uᵢ` -/

variable [DecidableEq k]

/-- The pair `{i, i + ℓ} ⊆ k`. -/
def pairSet (ℓ i : ℕ) : Finset k := {(i : k), ((i + ℓ : ℕ) : k)}

/-- The branch set `ℬ = ⋃_{i ≤ g} {i, i + ℓ}`. -/
def branchSet (g ℓ : ℕ) : Finset k := (Finset.range (g + 1)).biUnion (pairSet ℓ)

theorem mem_pairSet {ℓ i : ℕ} {a : k} :
    a ∈ pairSet ℓ i ↔ a = (i : k) ∨ a = ((i + ℓ : ℕ) : k) := by
  simp [pairSet]

theorem natCast_mem_pairSet (ℓ i : ℕ) : (i : k) ∈ pairSet ℓ i := mem_pairSet.mpr (Or.inl rfl)

theorem natCast_mem_branchSet {g ℓ i : ℕ} (hi : i ≤ g) : (i : k) ∈ branchSet g ℓ :=
  Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), natCast_mem_pairSet ℓ i⟩

instance instFactBranchSetNonempty (g ℓ : ℕ) : Fact (branchSet (k := k) g ℓ).Nonempty :=
  ⟨⟨0, by exact_mod_cast natCast_mem_branchSet (k := k) (ℓ := ℓ) (Nat.zero_le g)⟩⟩

theorem biUnion_pairSet_subset_branchSet {g ℓ : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range (g + 1)) : S.biUnion (pairSet (k := k) ℓ) ⊆ branchSet g ℓ :=
  Finset.biUnion_subset_biUnion_of_subset_left _ hS

theorem biUnion_pairSet_nonempty {ℓ : ℕ} {S : Finset ℕ} (hS : S.Nonempty) :
    (S.biUnion (pairSet (k := k) ℓ)).Nonempty := by
  obtain ⟨i, hi⟩ := hS
  exact Finset.biUnion_nonempty.mpr ⟨i, hi, ⟨_, natCast_mem_pairSet ℓ i⟩⟩

/-- `uᵢ = (x - i)(x - i - ℓ)/(x - g)² ∈ k(x)`. -/
noncomputable def uFun (g ℓ i : ℕ) : RatFunc k :=
  algebraMap k[X] (RatFunc k) (linProd (pairSet ℓ i)) /
    algebraMap k[X] (RatFunc k) (X - C (g : k)) ^ 2

omit [DecidableEq k] in
theorem X_sub_C_natCast_ne_zero (g : ℕ) :
    algebraMap k[X] (RatFunc k) (X - C (g : k)) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).mpr (X_sub_C_ne_zero _)

theorem uFun_ne_zero (g ℓ i : ℕ) : uFun (k := k) g ℓ i ≠ 0 :=
  div_ne_zero ((map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).mpr (linProd_ne_zero _))
    (pow_ne_zero _ (X_sub_C_natCast_ne_zero (k := k) g))

/-- `uᵢ` as a unit of `k(x)(√F)`, `i < g`. -/
noncomputable def uUnit (g ℓ : ℕ) (i : Fin g) : (BranchExt (branchSet (k := k) g ℓ))ˣ :=
  branchUnit (branchSet g ℓ) (uFun_ne_zero g ℓ i)

omit [DecidableEq k] in
/-- Multiplying by a nonzero square does not change squareness. -/
theorem isSquare_mul_sq_iff {x w : k} (hw : w ≠ 0) : IsSquare (x * w ^ 2) ↔ IsSquare x := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨r / w, ?_⟩
    field_simp
    linear_combination hr
  · rintro ⟨r, hr⟩
    exact ⟨r * w, by rw [hr]; ring⟩

/-! ### Distinctness of the branch points, in characteristic zero -/

variable [CharZero k]

/-- For `i ≠ j ≤ g < ℓ`, the pairs `{i, i + ℓ}` and `{j, j + ℓ}` are disjoint. -/
theorem pairSet_disjoint {g ℓ i j : ℕ} (hℓ : g < ℓ) (hi : i ≤ g) (hj : j ≤ g) (hij : i ≠ j) :
    Disjoint (pairSet (k := k) ℓ i) (pairSet ℓ j) := by
  rw [Finset.disjoint_left]
  intro a hai haj
  rw [mem_pairSet] at hai haj
  rcases hai with rfl | rfl <;> rcases haj with h | h <;>
    · have := Nat.cast_injective (R := k) h
      omega

theorem pairwiseDisjoint_pairSet {g ℓ : ℕ} (hℓ : g < ℓ) :
    Set.PairwiseDisjoint (↑(Finset.range (g + 1)) : Set ℕ) (pairSet (k := k) ℓ) := by
  intro i hi j hj hij
  rw [Finset.mem_coe, Finset.mem_range] at hi hj
  exact pairSet_disjoint hℓ (by omega) (by omega) hij

/-- `∏_{a ∈ E_S}(x - a) = ∏_{i ∈ S} (x - i)(x - i - ℓ)` for `S ⊆ {0, …, g}`. -/
theorem linProd_biUnion_pairSet {g ℓ : ℕ} (hℓ : g < ℓ) {S : Finset ℕ}
    (hS : S ⊆ Finset.range (g + 1)) :
    linProd (S.biUnion (pairSet (k := k) ℓ)) = ∏ i ∈ S, linProd (pairSet ℓ i) :=
  Finset.prod_biUnion ((pairwiseDisjoint_pairSet hℓ).subset (Finset.coe_subset.mpr hS))

/-- For `S ⊆ {0, …, g - 1}`, the last branch point `g` is not in `E_S`. -/
theorem natCast_notMem_biUnion_pairSet {g ℓ : ℕ} (hℓ : g < ℓ) {S : Finset ℕ}
    (hS : S ⊆ Finset.range g) : (g : k) ∉ S.biUnion (pairSet ℓ) := by
  rw [Finset.mem_biUnion]
  rintro ⟨i, hi, hgi⟩
  have hi' := Finset.mem_range.mp (hS hi)
  rw [mem_pairSet] at hgi
  rcases hgi with h | h <;>
    · have := Nat.cast_injective (R := k) h
      omega

/-- A subset product of the `uᵢ` is `∏_{a ∈ E_S}(x - a)` times a square. -/
theorem prod_uFun {g ℓ : ℕ} (hℓ : g < ℓ) {S : Finset ℕ} (hS : S ⊆ Finset.range (g + 1)) :
    ∏ i ∈ S, uFun (k := k) g ℓ i =
      algebraMap k[X] (RatFunc k) (linProd (S.biUnion (pairSet ℓ))) *
        ((algebraMap k[X] (RatFunc k) (X - C (g : k)))⁻¹ ^ S.card) ^ 2 := by
  rw [linProd_biUnion_pairSet hℓ hS, map_prod]
  simp only [uFun, div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const]
  ring

/-! ### Proposition 3.1 -/

/-- **Proposition 3.1, independence.**  No nonempty product of the `uᵢ`, `i < g`, is a square in
`k(x)(√F)`. -/
theorem not_isSquare_prod_uFun {g ℓ : ℕ} (hℓ : g < ℓ) {S : Finset ℕ} (hS : S ⊆ Finset.range g)
    (hne : S.Nonempty) :
    ¬ IsSquare (algebraMap (RatFunc k) (BranchExt (branchSet (k := k) g ℓ))
      (∏ i ∈ S, uFun (k := k) g ℓ i)) := by
  have hS' : S ⊆ Finset.range (g + 1) := hS.trans (Finset.range_mono (Nat.le_succ g))
  rw [isSquare_algebraMap_quadExt_iff _ (branchF_ne_zero _), prod_uFun (k := k) hℓ hS']
  have hw0 : (algebraMap k[X] (RatFunc k) (X - C (g : k)))⁻¹ ^ S.card ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero (X_sub_C_natCast_ne_zero (k := k) g))
  rw [isSquare_mul_sq_iff hw0, mul_div_right_comm, isSquare_mul_sq_iff hw0, isSquare_linProd_iff,
    isSquare_linProd_div_iff (biUnion_pairSet_subset_branchSet hS')]
  rintro (h | h)
  · exact (biUnion_pairSet_nonempty hne).ne_empty h
  · exact natCast_notMem_biUnion_pairSet hℓ hS (h ▸ natCast_mem_branchSet le_rfl)

/-- **Proposition 3.1.**  The square classes of `u₀, …, u_{g-1}` in `k(x)(√F)` are
`𝔽₂`-linearly independent. -/
@[gs_public]
theorem linearIndependent_uUnit {g ℓ : ℕ} (hℓ : g < ℓ) :
    LinearIndependent (ZMod 2) (fun i : Fin g => squareClass (uUnit (k := k) g ℓ i)) := by
  rw [linearIndependent_squareClass_iff]
  intro S hS
  rw [← isSquare_units_val_iff, Units.coe_prod]
  simp only [uUnit, branchUnit_val]
  rw [← map_prod]
  have hprod : ∏ i ∈ S, uFun (k := k) g ℓ (i : ℕ) =
      ∏ i ∈ S.map Fin.valEmbedding, uFun g ℓ i := by
    rw [Finset.prod_map]
    rfl
  rw [hprod]
  refine not_isSquare_prod_uFun (k := k) hℓ (fun i hi => ?_) hS.map
  obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hi
  exact Finset.mem_range.mpr j.2

/-- **Proposition 3.1, the degree.**  In any field `L'` over `K = k(x)(√F)` containing square
roots `rᵢ` of the `uᵢ`, the field `K(r₀, …, r_{g-1})` has degree `2^g` over `K`. -/
theorem finrank_adjoin_sqrt_uUnit {g ℓ : ℕ} (hℓ : g < ℓ) {L' : Type*} [Field L']
    [Algebra (BranchExt (branchSet (k := k) g ℓ)) L'] (root : Fin g → L')
    (hroot : ∀ i, root i ^ 2 =
      algebraMap (BranchExt (branchSet (k := k) g ℓ)) L' (uUnit (k := k) g ℓ i).val) :
    Module.finrank (BranchExt (branchSet (k := k) g ℓ))
      (IntermediateField.adjoin (BranchExt (branchSet (k := k) g ℓ)) (Set.range root)) = 2 ^ g := by
  have := Multiquadratic.finrank_adjoin_range_of_linearIndependent hroot
    (linearIndependent_uUnit hℓ)
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this

end GSArith.Arithmetic

end
