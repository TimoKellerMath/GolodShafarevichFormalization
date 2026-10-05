/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Algebra.GroupWithZero.Idempotent
public import GSArith.Ledger

/-!
# Finite étale covers of `Spec ℤ` (Propositions 2.6 and 2.7)

Proposition 2.6 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic
surfaces*: every finite étale `ℤ`-algebra is `ℤ^d`.  The paper's proof reduces to a connected
cover, identifies its coordinate ring with the ring of integers `𝓞_K` of a number field `K`,
observes that étaleness makes the trace pairing perfect so that `|disc K| = 1`, and concludes
`K = ℚ` from Minkowski's bound `|disc K| > 1` for `K ≠ ℚ`.

The arithmetic heart is Tier A and is proved here from Mathlib's
`NumberField.abs_discr_gt_two`:

* `GSArith.Arithmetic.finrank_eq_one_of_abs_discr_eq_one`: `|disc K| = 1 ⟹ [K : ℚ] = 1`;
* `GSArith.Arithmetic.finrank_eq_one_of_etale`: if `𝓞_K` is étale over `ℤ` then `K = ℚ`,
  modulo the single ledgered input that a finite étale `ℤ`-algebra has unit discriminant
  (Stacks: étale ⟺ the trace form is perfect, for finite free algebras);
* `GSArith.Arithmetic.ringOfIntegersEquivInt`: `𝓞_K ≃ ℤ` for `K` of degree one.

The **full étale-algebra form** of Proposition 2.6 is `GSArith.Arithmetic.finite_etale_over_int`:
`A ≃ₐ[ℤ] ℤ^d` for every finite étale `ℤ`-algebra `A`.  Its scheme-theoretic reduction — a
finite étale `ℤ`-algebra is a finite product of connected ones (finitely many idempotents),
each connected factor is a normal domain (étale over normal is normal, Stacks `025P`, `0357`),
finite over `ℤ`, hence the ring of integers of its fraction field — is the ledgered input
`exists_algEquiv_pi_ringOfIntegers`; everything after it is proved.

**Proposition 2.7** at the level of algebras: the `ℤ`-algebra sections `A → ℤ` of `A ≃ ℤ^d` are
the `d` coordinate projections (`GSArith.Arithmetic.ringHomPiIntEquiv`,
`card_ringHom_int_eq`): a ring homomorphism `ℤ^d → ℤ` sends the orthogonal idempotents `eᵢ` to
idempotents `0` or `1` of `ℤ` summing to `1`, so exactly one `eᵢ` goes to `1`, and the map is
evaluation there.
-/

@[expose] public section

namespace GSArith.Arithmetic

open NumberField

universe u

/-! ### The arithmetic core -/

/-- **Minkowski.**  A number field with `|disc K| = 1` is `ℚ`. -/
theorem finrank_eq_one_of_abs_discr_eq_one (K : Type*) [Field K] [NumberField K]
    (h : |discr K| = 1) : Module.finrank ℚ K = 1 := by
  by_contra hne
  have h0 : 0 < Module.finrank ℚ K := Module.finrank_pos
  have h1 : 1 < Module.finrank ℚ K := by omega
  have := abs_discr_gt_two h1
  rw [h] at this
  norm_num at this

-- OBLIGATION[stacks:0BVH][tier:C][crit:yes][prop:2.6] finite étale over ℤ ⟹ unit discriminant
theorem isUnit_discr_of_etale (K : Type*) [Field K] [NumberField K]
    [Algebra.Etale ℤ (𝓞 K)] : IsUnit (discr K) := by
  sorry

/-- **Proposition 2.6, arithmetic form.**  If the ring of integers of a number field `K` is
étale over `ℤ`, then `K = ℚ`: there is no nontrivial number field unramified at every finite
prime. -/
theorem finrank_eq_one_of_etale (K : Type*) [Field K] [NumberField K]
    [Algebra.Etale ℤ (𝓞 K)] : Module.finrank ℚ K = 1 :=
  finrank_eq_one_of_abs_discr_eq_one K (Int.isUnit_iff_abs_eq.mp (isUnit_discr_of_etale K))

/-! ### From `[K : ℚ] = 1` to `𝓞_K = ℤ` -/

/-- A number field of degree one is `ℚ`: `algebraMap ℚ K` is bijective. -/
theorem bijective_algebraMap_of_finrank_eq_one (K : Type*) [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 1) : Function.Bijective (algebraMap ℚ K) := by
  refine ⟨(algebraMap ℚ K).injective, fun x => ?_⟩
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : K) one_ne_zero).mp h x
  exact ⟨c, by rw [← hc, Algebra.smul_def, mul_one]⟩

/-- `𝓞_K ≃ ℤ` for a number field `K` of degree one. -/
noncomputable def ringOfIntegersEquivInt (K : Type*) [Field K] [NumberField K]
    (h : Module.finrank ℚ K = 1) : 𝓞 K ≃+* ℤ :=
  (RingOfIntegers.mapRingEquiv (RingEquiv.ofBijective (algebraMap ℚ K)
    (bijective_algebraMap_of_finrank_eq_one K h)).symm).trans Rat.ringOfIntegersEquiv

/-! ### Proposition 2.6, the étale-algebra form -/

-- OBLIGATION[stacks:02GH,025P,0357][tier:C][crit:yes][prop:2.6] finite étale ℤ-algebra = ∏ 𝓞_{K_i}
theorem exists_algEquiv_pi_ringOfIntegers (A : Type u) [CommRing A] [Module.Finite ℤ A]
    [Algebra.Etale ℤ A] :
    ∃ (ι : Type u) (_ : Fintype ι) (K : ι → Type u) (_ : ∀ i, Field (K i))
      (_ : ∀ i, NumberField (K i)) (_ : ∀ i, Algebra.Etale ℤ (𝓞 (K i))),
      Nonempty (A ≃ₐ[ℤ] ∀ i, 𝓞 (K i)) := by
  sorry

/-- **Proposition 2.6.**  Every finite étale `ℤ`-algebra is `ℤ^d` for some `d ≥ 0`. -/
theorem finite_etale_over_int (A : Type u) [CommRing A] [Module.Finite ℤ A]
    [Algebra.Etale ℤ A] : ∃ d : ℕ, Nonempty (A ≃ₐ[ℤ] (Fin d → ℤ)) := by
  obtain ⟨ι, _, K, _, _, _, ⟨e⟩⟩ := exists_algEquiv_pi_ringOfIntegers A
  refine ⟨Fintype.card ι, ⟨?_⟩⟩
  let e₂ : (∀ i, 𝓞 (K i)) ≃ₐ[ℤ] (ι → ℤ) :=
    AlgEquiv.piCongrRight fun i =>
      (ringOfIntegersEquivInt (K i) (finrank_eq_one_of_etale (K i))).toIntAlgEquiv
  let e₃ : (ι → ℤ) ≃ₐ[ℤ] (Fin (Fintype.card ι) → ℤ) :=
    AlgEquiv.piCongrLeft' (R := ℤ) (fun _ : ι => ℤ) (Fintype.equivFin ι)
  exact e.trans (e₂.trans e₃)

/-! ### Proposition 2.7, the algebraic form: the sections of `ℤ^d` are the projections -/

section Sections

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- A ring homomorphism `ℤ^ι → ℤ` sends each `eᵢ = Pi.single i 1` to `0` or `1`. -/
theorem ringHom_single_eq_zero_or_one (f : (ι → ℤ) →+* ℤ) (i : ι) :
    f (Pi.single i 1) = 0 ∨ f (Pi.single i 1) = 1 := by
  refine IsIdempotentElem.iff_eq_zero_or_one.mp ?_
  change f (Pi.single i 1) * f (Pi.single i 1) = f (Pi.single i 1)
  rw [← map_mul]
  congr 1
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

/-- The values on the `eᵢ` sum to `1`. -/
theorem sum_ringHom_single (f : (ι → ℤ) →+* ℤ) : ∑ i, f (Pi.single i 1) = 1 := by
  rw [← map_sum]
  have : (∑ i, Pi.single i (1 : ℤ) : ι → ℤ) = 1 := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [this, map_one]

omit [Fintype ι] in
/-- Two distinct `eᵢ`, `eⱼ` cannot both go to `1`. -/
theorem ringHom_single_eq_zero_of_ne (f : (ι → ℤ) →+* ℤ) {i j : ι} (hij : i ≠ j)
    (hi : f (Pi.single i 1) = 1) : f (Pi.single j 1) = 0 := by
  have h : f (Pi.single j 1) * f (Pi.single i 1) = 0 := by
    rw [← map_mul]
    convert map_zero f using 2
    ext l
    by_cases hl : l = i
    · subst hl; simp [hij.symm]
    · simp [hl]
  rwa [hi, mul_one] at h

omit [Fintype ι] [DecidableEq ι] in
/-- A ring homomorphism `ℤ^ι → ℤ` is evaluation at some index. -/
theorem exists_eq_evalRingHom [Finite ι] (f : (ι → ℤ) →+* ℤ) :
    ∃ i, f = Pi.evalRingHom (fun _ => ℤ) i := by
  classical
  let := Fintype.ofFinite ι
  have hex : ∃ i, f (Pi.single i 1) = 1 := by
    by_contra hne
    have hzero : ∀ i, f (Pi.single i 1) = 0 := fun i =>
      (ringHom_single_eq_zero_or_one f i).resolve_right fun h => hne ⟨i, h⟩
    have := sum_ringHom_single f
    simp only [hzero, Finset.sum_const_zero] at this
    exact zero_ne_one this
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, RingHom.ext fun x => ?_⟩
  have hx : x = ∑ j, (x j : ℤ) • (Pi.single j 1 : ι → ℤ) := by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  rw [Pi.evalRingHom_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  simp only [map_zsmul, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · rw [hi, mul_one]
  · intro j _ hji
    rw [ringHom_single_eq_zero_of_ne f (Ne.symm hji) hi, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [Fintype ι] [DecidableEq ι] in
/-- The evaluations at distinct indices are distinct. -/
theorem evalRingHom_injective :
    Function.Injective (fun i : ι => Pi.evalRingHom (fun _ => ℤ) i) := by
  classical
  intro i j h
  by_contra hij
  have := congrArg (fun φ : (ι → ℤ) →+* ℤ => φ (Pi.single i 1)) h
  rw [Pi.evalRingHom_apply, Pi.evalRingHom_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne (Ne.symm hij)] at this
  exact one_ne_zero this

omit [DecidableEq ι] in
/-- **Proposition 2.7, algebraic form.**  The ring homomorphisms `ℤ^ι → ℤ` are exactly the `|ι|`
coordinate projections. -/
noncomputable def ringHomPiIntEquiv : ((ι → ℤ) →+* ℤ) ≃ ι :=
  (Equiv.ofBijective (fun i : ι => Pi.evalRingHom (fun _ => ℤ) i)
    ⟨evalRingHom_injective, fun f => (exists_eq_evalRingHom f).imp fun _ h => h.symm⟩).symm

/-- Transport of ring homomorphisms to `ℤ` along a ring isomorphism of the source. -/
def ringHomCongrDomain {A B : Type*} [Ring A] [Ring B] (e : A ≃+* B) : (A →+* ℤ) ≃ (B →+* ℤ) where
  toFun f := f.comp e.symm.toRingHom
  invFun g := g.comp e.toRingHom
  left_inv f := by ext; simp
  right_inv g := by ext; simp

end Sections

/-- **Propositions 2.6 and 2.7 together.**  A finite étale `ℤ`-algebra `A` is `ℤ^d`, and it has
exactly `d` ring homomorphisms to `ℤ` (the sections of `Spec A → Spec ℤ`). -/
theorem card_ringHom_int_eq (A : Type u) [CommRing A] [Module.Finite ℤ A] [Algebra.Etale ℤ A] :
    ∃ d : ℕ, Nonempty (A ≃ₐ[ℤ] (Fin d → ℤ)) ∧ Nat.card (A →+* ℤ) = d := by
  obtain ⟨d, ⟨e⟩⟩ := finite_etale_over_int A
  refine ⟨d, ⟨e⟩, ?_⟩
  rw [Nat.card_congr ((ringHomCongrDomain e.toRingEquiv).trans ringHomPiIntEquiv),
    Nat.card_eq_fintype_card, Fintype.card_fin]

end GSArith.Arithmetic

end
