/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Algebra.Module.Hom
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.ZMod.Basic
public import GSArith.Ledger

/-!
# Nonsplit central extensions by `𝔽₂`

Proposition 2.32 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic
surfaces*: for a nonsplit central extension `1 → 𝔽₂ → E →ρ H → 1` of finite `2`-groups,

* every subgroup `A ≤ E` with `ρ(A) = H` is all of `E`;
* `ker ρ ≤ Φ(E)`, the Frattini subgroup;
* `d(E) = d(H)`, where `d(G) = dim_{𝔽₂} H¹(G, 𝔽₂) = dim_{𝔽₂} Hom(G, 𝔽₂)` is the generator
  rank.

The formal statements are slightly more general than the paper's: none of the three
conclusions uses that `E` and `H` are finite `2`-groups, nor that the kernel is central.  What
is used is only that `ρ` is surjective, that its kernel has order two (so that a subgroup
either meets it trivially or contains it), and that `ρ` admits no homomorphic section.  The
paper's route to the Frattini statement goes through "maximal subgroups of a finite `2`-group
have index two"; the route here goes through the first conclusion instead, which is why the
`2`-group hypothesis disappears.  The generator rank is defined as
`dim_{𝔽₂} Hom(G, 𝔽₂)`, which for a finite `2`-group agrees with `dim_{𝔽₂} G/Φ(G)`
(Burnside's basis theorem); only the `Hom` description is needed downstream.

## Main definitions and results

* `GSArith.GroupTheory.IsCentralExtensionByTwo ρ`: `ρ` is surjective with central kernel of
  order two.
* `GSArith.GroupTheory.Splits ρ`: `ρ` has a homomorphic section.
* `GSArith.GroupTheory.genRank G`: the generator rank `dim_{𝔽₂} Hom(G, 𝔽₂)`.
* `IsCentralExtensionByTwo.eq_top_of_map_eq_top`, `.ker_le_frattini`, `.genRank_eq`: the three
  parts of Proposition 2.32.
-/

@[expose] public section

namespace GSArith.GroupTheory

open Subgroup

variable {E H : Type*} [Group E] [Group H]

/-- A central extension `1 → 𝔽₂ → E →ρ H → 1`: `ρ` is surjective and its kernel is central of
order two. -/
structure IsCentralExtensionByTwo (ρ : E →* H) : Prop where
  surjective : Function.Surjective ρ
  card_ker : Nat.card ρ.ker = 2
  central : ρ.ker ≤ center E

/-- `ρ` splits if it admits a homomorphic section. -/
def Splits (ρ : E →* H) : Prop := ∃ σ : H →* E, ρ.comp σ = MonoidHom.id H

/-- The generator rank `d(G) = dim_{𝔽₂} Hom(G, 𝔽₂) = dim_{𝔽₂} H¹(G, 𝔽₂)`. -/
noncomputable def genRank (G : Type*) [Group G] : ℕ :=
  Module.finrank (ZMod 2) (Additive G →+ ZMod 2)

/-- If a subgroup `S ≤ E` surjects onto `H` and meets `ker ρ` trivially, then `ρ` splits:
`ρ` restricts to an isomorphism `S ≃ H`. -/
theorem splits_of_map_eq_top_of_inf_ker_eq_bot {ρ : E →* H} (S : Subgroup E)
    (hS : S.map ρ = ⊤) (hker : S ⊓ ρ.ker = ⊥) : Splits ρ := by
  let f : S →* H := ρ.comp S.subtype
  have hinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, hx⟩ hfx
    have hxk : x ∈ S ⊓ ρ.ker := ⟨hx, MonoidHom.mem_ker.mp hfx⟩
    rw [hker, Subgroup.mem_bot] at hxk
    simp [hxk]
  have hsurj : Function.Surjective f := by
    intro h
    have hh : h ∈ S.map ρ := by rw [hS]; exact Subgroup.mem_top h
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hh
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : S ≃* H := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨S.subtype.comp e.symm.toMonoidHom, ?_⟩
  ext h
  exact e.apply_symm_apply h

namespace IsCentralExtensionByTwo

variable {ρ : E →* H} (hρ : IsCentralExtensionByTwo ρ)
include hρ

/-- A subgroup of `E` either meets the order-two kernel trivially or contains it. -/
theorem inf_ker_eq_bot_or_le (S : Subgroup E) : S ⊓ ρ.ker = ⊥ ∨ ρ.ker ≤ S := by
  have : Fact (Nat.card ρ.ker).Prime := ⟨by rw [hρ.card_ker]; exact Nat.prime_two⟩
  rcases (S.subgroupOf ρ.ker).eq_bot_or_eq_top_of_prime_card with h | h
  · left
    exact disjoint_iff.mp (subgroupOf_eq_bot.mp h)
  · right
    exact subgroupOf_eq_top.mp h

/-- **Proposition 2.32 (i).**  In a nonsplit central extension by `𝔽₂`, a subgroup mapping onto
`H` is the whole group. -/
theorem eq_top_of_map_eq_top (hns : ¬ Splits ρ) (S : Subgroup E) (hS : S.map ρ = ⊤) :
    S = ⊤ := by
  rcases hρ.inf_ker_eq_bot_or_le S with h | h
  · exact absurd (splits_of_map_eq_top_of_inf_ker_eq_bot S hS h) hns
  · rw [← comap_map_eq_self h, hS, comap_top]

/-- Every maximal subgroup of `E` contains the kernel. -/
theorem ker_le_of_isCoatom (hns : ¬ Splits ρ) {K : Subgroup E} (hK : IsCoatom K) :
    ρ.ker ≤ K := by
  by_cases hmap : K.map ρ = ⊤
  · exact absurd (hρ.eq_top_of_map_eq_top hns K hmap) hK.1
  · have hle : K ≤ (K.map ρ).comap ρ := le_comap_map ρ K
    have hne : (K.map ρ).comap ρ ≠ ⊤ := by
      intro htop
      apply hmap
      rw [← map_comap_eq_self_of_surjective hρ.surjective (K.map ρ), htop,
        map_top_of_surjective ρ hρ.surjective]
    have heq : (K.map ρ).comap ρ = K := by
      by_contra hne'
      exact hne (hK.2 _ (lt_of_le_of_ne hle (Ne.symm hne')))
    rw [← heq]
    intro x hx
    rw [mem_comap, MonoidHom.mem_ker.mp hx]
    exact one_mem _

/-- **Proposition 2.32 (ii).**  The kernel of a nonsplit central extension by `𝔽₂` lies in the
Frattini subgroup. -/
theorem ker_le_frattini (hns : ¬ Splits ρ) : ρ.ker ≤ frattini E := by
  unfold frattini Order.radical
  exact le_iInf₂ fun K hK => hρ.ker_le_of_isCoatom hns hK

/-- Every `𝔽₂`-valued character of `E` kills the kernel of a nonsplit central extension by
`𝔽₂`: otherwise its kernel would be a complement to `ker ρ`, splitting the extension. -/
theorem char_ker_eq_zero (hns : ¬ Splits ρ) (χ : Additive E →+ ZMod 2) {k : E}
    (hk : k ∈ ρ.ker) : χ (Additive.ofMul k) = 0 := by
  by_contra hne
  let S : Subgroup E :=
    { carrier := {x | χ (Additive.ofMul x) = 0}
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [ofMul_mul, map_add, hx, hy, add_zero]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [ofMul_inv, map_neg, hx, neg_zero] }
  have hkS : k ∉ S := hne
  have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hχk : χ (Additive.ofMul k) = 1 := (h01 _).resolve_left hne
  have hmap : S.map ρ = ⊤ := by
    rw [eq_top_iff]
    intro h _
    obtain ⟨x, rfl⟩ := hρ.surjective h
    rcases h01 (χ (Additive.ofMul x)) with hx | hx
    · exact ⟨x, hx, rfl⟩
    · refine ⟨x * k, ?_, ?_⟩
      · change χ (Additive.ofMul (x * k)) = 0
        rw [ofMul_mul, map_add, hx, hχk]
        decide
      · rw [map_mul, MonoidHom.mem_ker.mp hk, mul_one]
  rcases hρ.inf_ker_eq_bot_or_le S with h | h
  · exact hns (splits_of_map_eq_top_of_inf_ker_eq_bot S hmap h)
  · exact hkS (h hk)

end IsCentralExtensionByTwo

/-- Pullback of `𝔽₂`-valued characters along `ρ`, as an `𝔽₂`-linear map
`Hom(H, 𝔽₂) → Hom(E, 𝔽₂)`. -/
def pullbackChar (ρ : E →* H) :
    (Additive H →+ ZMod 2) →ₗ[ZMod 2] (Additive E →+ ZMod 2) where
  toFun χ := χ.comp (MonoidHom.toAdditive ρ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem pullbackChar_apply (ρ : E →* H) (χ : Additive H →+ ZMod 2) (x : Additive E) :
    pullbackChar ρ χ x = χ (Additive.ofMul (ρ x.toMul)) := rfl

theorem toAdditive_surjective {ρ : E →* H} (hρ : Function.Surjective ρ) :
    Function.Surjective (MonoidHom.toAdditive ρ) := fun y => by
  obtain ⟨x, hx⟩ := hρ y.toMul
  exact ⟨Additive.ofMul x, by simp [hx]⟩

theorem pullbackChar_injective {ρ : E →* H} (hρ : Function.Surjective ρ) :
    Function.Injective (pullbackChar ρ) := by
  intro χ₁ χ₂ h
  ext y
  obtain ⟨x, rfl⟩ := toAdditive_surjective hρ y
  exact congrArg (fun χ => χ x) h

namespace IsCentralExtensionByTwo

variable {ρ : E →* H} (hρ : IsCentralExtensionByTwo ρ)
include hρ

theorem pullbackChar_surjective (hns : ¬ Splits ρ) : Function.Surjective (pullbackChar ρ) := by
  intro χ'
  have hker : (MonoidHom.toAdditive ρ).ker ≤ χ'.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    have hx' : ρ x.toMul = 1 := by simpa using hx
    have := hρ.char_ker_eq_zero hns χ' (MonoidHom.mem_ker.mpr hx')
    simpa using this
  refine ⟨(MonoidHom.toAdditive ρ).liftOfSurjective (toAdditive_surjective hρ.surjective)
    ⟨χ', hker⟩, ?_⟩
  exact AddMonoidHom.liftOfRightInverse_comp _ _ _ ⟨χ', hker⟩

/-- **Proposition 2.32 (iii).**  A nonsplit central extension by `𝔽₂` does not change the
generator rank: `d(E) = d(H)`. -/
theorem genRank_eq (hns : ¬ Splits ρ) : genRank E = genRank H := by
  unfold genRank
  rw [← LinearMap.finrank_range_of_inj (pullbackChar_injective hρ.surjective),
    LinearMap.range_eq_top.mpr (hρ.pullbackChar_surjective hns), finrank_top]

end IsCentralExtensionByTwo

end GSArith.GroupTheory

end
