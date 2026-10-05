/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import TauCeti.FieldTheory.SquareClassGroup.Basic
public import GSArith.Ledger

/-!
# Square classes of `ℚ_p` (Proposition 2.23)

The computation at the heart of Proposition 2.23 of Dérickx–Gillibert–Keller–Pagano,
*Golod–Shafarevich for arithmetic surfaces*:

  `dim_{𝔽₂} ℚ_p^× / ℚ_p^{×2} = 2` for odd `p`  (and `3` for `p = 2`).

Following the paper: a square has even valuation, so the uniformizer `p` is not a square; at
odd `p` Hensel's lemma makes every unit congruent to a square mod `p` a square, so a unit is
determined modulo squares by its residue, and the residues modulo squares form a group of
order two.  Hence `{p, u}`, with `u` a lift of a quadratic non-residue, is a basis of the
square-class group.

The square-class group is TauCeti's `TauCeti.SquareClassGroup ℚ_[p]`, an `𝔽₂`-vector space;
Hensel's lemma is Mathlib's `hensels_lemma` applied to `X² - u`.

## Main results

* `GSArith.Arithmetic.PadicInt.isSquare_of_isSquare_toZMod`: Hensel for unit squares, `p` odd.
* `GSArith.Arithmetic.finrank_squareClassGroup_padic_of_odd`: the dimension is `2` for odd `p`.

* `GSArith.Arithmetic.finrank_squareClassGroup_padic_two`: the dyadic case, dimension `3`, via
  residues mod `8` and Hensel's lemma at `2`.
* `GSArith.Arithmetic.finrank_squareClassGroup_padic`: both cases together.
-/

@[expose] public section

namespace GSArith.Arithmetic

open TauCeti Polynomial

/-! ### Generalities on square classes -/

section SquareClass

variable {K : Type*} [Field K]

theorem isSquare_units_of_isSquare_val {x : Kˣ} (h : IsSquare (x : K)) : IsSquare x := by
  obtain ⟨y, hy⟩ := h
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact x.ne_zero (by rw [hy, mul_zero])
  exact ⟨Units.mk0 y hy0, Units.ext (by simpa using hy)⟩

theorem isSquare_val_of_isSquare {x : Kˣ} (h : IsSquare x) : IsSquare (x : K) := by
  obtain ⟨y, hy⟩ := h
  exact ⟨y, by rw [hy, Units.val_mul]⟩

/-- The square-class group is killed by `2`: `c + c = 0`. -/
theorem add_self_squareClassGroup (c : SquareClassGroup K) : c + c = 0 := by
  have h : c + c = ((1 : ZMod 2) + 1) • c := by rw [add_smul, one_smul]
  have h11 : ((1 : ZMod 2) + 1) = 0 := by decide
  rw [h, h11, zero_smul]

theorem squareClass_mul_self (w : Kˣ) : squareClass (w * w) = 0 :=
  (squareClass_eq_zero_iff _).mpr ⟨w, rfl⟩

theorem squareClass_one : squareClass (1 : Kˣ) = 0 :=
  (squareClass_eq_zero_iff 1).mpr ⟨1, by simp⟩

theorem squareClass_inv (w : Kˣ) : squareClass w⁻¹ = squareClass w := by
  have h : squareClass w = squareClass w⁻¹ + squareClass (w * w) := by
    rw [← squareClass_mul, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [h, squareClass_mul_self]
  exact (add_zero (squareClass w⁻¹)).symm

theorem squareClass_zpow (w : Kˣ) (n : ℤ) :
    squareClass (w ^ n) = (n.natAbs : ZMod 2) • squareClass w := by
  rw [Nat.cast_smul_eq_nsmul, ← squareClass_pow]
  rcases Int.natAbs_eq n with h | h
  · rw [h, zpow_natCast]
    simp only [Int.natAbs_natCast]
  · rw [h, zpow_neg, zpow_natCast, squareClass_inv]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]

/-- Every element of the square-class group is the class of a unit. -/
theorem exists_squareClass_eq (c : SquareClassGroup K) : ∃ x : Kˣ, squareClass x = c := by
  induction c using QuotientAddGroup.induction_on with
  | _ z => exact ⟨Additive.toMul z, by rw [squareClass_def]; rfl⟩

end SquareClass

/-! ### `p`-adic preliminaries -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- A square in `ℚ_p^×` has norm an even power of `p`. -/
theorem exists_norm_eq_of_isSquare {x : ℚ_[p]ˣ} (h : IsSquare x) :
    ∃ w : ℤ, ‖(x : ℚ_[p])‖ = (p : ℝ) ^ (2 * w) := by
  obtain ⟨y, hy⟩ := h
  refine ⟨-(y : ℚ_[p]).valuation, ?_⟩
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [hy, Units.val_mul, norm_mul, Padic.norm_eq_zpow_neg_valuation y.ne_zero, ← zpow_add₀ hp0]
  congr 1
  ring

/-- An element of `ℚ_p^×` of norm `p⁻¹` (valuation one) is not a square. -/
theorem not_isSquare_of_norm_eq_inv {x : ℚ_[p]ˣ} (h : ‖(x : ℚ_[p])‖ = (p : ℝ)⁻¹) :
    ¬ IsSquare x := by
  intro hsq
  obtain ⟨w, hw⟩ := exists_norm_eq_of_isSquare hsq
  rw [h, ← zpow_neg_one] at hw
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have := zpow_right_injective₀ (by positivity) hp1.ne' hw
  omega

/-- The uniformizer `p` as a unit of `ℚ_p`. -/
noncomputable def pUnit (p : ℕ) [Fact p.Prime] : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)

@[simp] theorem val_pUnit : ((pUnit p : ℚ_[p]ˣ) : ℚ_[p]) = p := rfl

theorem norm_pUnit : ‖((pUnit p : ℚ_[p]ˣ) : ℚ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [val_pUnit, Padic.norm_p]

/-- Units of `ℤ_p` as units of `ℚ_p`. -/
noncomputable def unitsMap (p : ℕ) [Fact p.Prime] : ℤ_[p]ˣ →* ℚ_[p]ˣ :=
  Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom

@[simp] theorem val_unitsMap (v : ℤ_[p]ˣ) : ((unitsMap p v : ℚ_[p]ˣ) : ℚ_[p]) = (v : ℤ_[p]) := rfl

theorem norm_unitsMap (v : ℤ_[p]ˣ) : ‖((unitsMap p v : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
  rw [val_unitsMap, ← PadicInt.norm_def]
  exact PadicInt.isUnit_iff.mp v.isUnit

theorem isSquare_unitsMap_of_isSquare {v : ℤ_[p]ˣ} (h : IsSquare (v : ℤ_[p])) :
    IsSquare (unitsMap p v) := by
  obtain ⟨z, hz⟩ := h
  apply isSquare_units_of_isSquare_val
  exact ⟨(z : ℚ_[p]), by rw [val_unitsMap, hz, PadicInt.coe_mul]⟩

theorem isSquare_coe_of_isSquare_unitsMap {v : ℤ_[p]ˣ} (h : IsSquare (unitsMap p v)) :
    IsSquare (v : ℤ_[p]) := by
  obtain ⟨y, hy⟩ := isSquare_val_of_isSquare h
  rw [val_unitsMap] at hy
  have hy1 : ‖y‖ = 1 := by
    have h1 : ‖((v : ℤ_[p]) : ℚ_[p])‖ = 1 := by
      rw [← PadicInt.norm_def]; exact PadicInt.isUnit_iff.mp v.isUnit
    rw [hy, norm_mul] at h1
    nlinarith [norm_nonneg y, h1]
  exact ⟨(⟨y, hy1.le⟩ : ℤ_[p]), Subtype.ext hy⟩

theorem isSquare_toZMod_of_isSquare {v : ℤ_[p]} (h : IsSquare v) :
    IsSquare (PadicInt.toZMod v) := by
  obtain ⟨z, hz⟩ := h
  exact ⟨PadicInt.toZMod z, by rw [hz, map_mul]⟩

/-- `x ∈ ℤ_p` lies in the maximal ideal iff its residue vanishes. -/
theorem norm_lt_one_iff_toZMod_eq_zero (x : ℤ_[p]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← PadicInt.mem_nonunits, ← IsLocalRing.mem_maximalIdeal, ← PadicInt.ker_toZMod,
    RingHom.mem_ker]

theorem norm_eq_one_of_toZMod_ne_zero {x : ℤ_[p]} (h : PadicInt.toZMod x ≠ 0) : ‖x‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one x)
    (not_lt.mp fun hlt => h ((norm_lt_one_iff_toZMod_eq_zero x).mp hlt))

/-! ### Hensel's lemma for unit squares, `p` odd -/

theorem norm_mul' (x y : ℤ_[p]) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  rw [PadicInt.norm_def, PadicInt.coe_mul, norm_mul, ← PadicInt.norm_def, ← PadicInt.norm_def]

theorem norm_two_eq_one (hp2 : p ≠ 2) : ‖(2 : ℤ_[p])‖ = 1 := by
  have hnot : ¬ ‖((2 : ℤ) : ℤ_[p])‖ < 1 := by
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    intro hdvd
    have h2 : p ∣ 2 := by exact_mod_cast hdvd
    have := Nat.le_of_dvd (by norm_num) h2
    have := hp.out.two_le
    omega
  have hle := PadicInt.norm_le_one ((2 : ℤ) : ℤ_[p])
  push_cast at hnot hle
  exact le_antisymm hle (not_lt.mp hnot)

/-- **Hensel.**  For odd `p`, a unit of `ℤ_p` whose residue mod `p` is a square is a square. -/
theorem PadicInt.isSquare_of_isSquare_toZMod (hp2 : p ≠ 2) {u : ℤ_[p]} (hu : IsUnit u)
    (h : IsSquare (PadicInt.toZMod u)) : IsSquare u := by
  obtain ⟨b, hb⟩ := h
  have hu0 : PadicInt.toZMod u ≠ 0 := (hu.map PadicInt.toZMod).ne_zero
  have hb0 : b ≠ 0 := fun h0 => hu0 (by rw [hb, h0, mul_zero])
  set a : ℤ_[p] := (b.val : ℤ_[p]) with ha
  have hta : PadicInt.toZMod a = b := by rw [ha, map_natCast, ZMod.natCast_zmod_val]
  set F : ℤ_[p][X] := X ^ 2 - C u with hF
  have hFa : aeval a F = a ^ 2 - u := by simp [hF]
  have hF'a : aeval a (derivative F) = 2 * a := by
    simp [hF]
    norm_num
  have hnum : ‖aeval a F‖ < 1 := by
    rw [hFa, norm_lt_one_iff_toZMod_eq_zero, map_sub, map_pow, hta, hb, sq, sub_self]
  have ha1 : ‖a‖ = 1 := norm_eq_one_of_toZMod_ne_zero (by rw [hta]; exact hb0)
  have hden : ‖aeval a (derivative F)‖ = 1 := by
    rw [hF'a, norm_mul', norm_two_eq_one hp2, ha1, one_mul]
  obtain ⟨z, hz, -, -, -⟩ := hensels_lemma (F := F) (a := a) (by rw [hden, one_pow]; exact hnum)
  have hz' : z ^ 2 - u = 0 := by simpa [hF] using hz
  exact ⟨z, by rw [sq] at hz'; exact (sub_eq_zero.mp hz').symm⟩

/-! ### Residues modulo squares, `p` odd -/

theorem ringChar_zmod_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp2

/-- In `𝔽_p^×` (`p` odd) the product of two non-squares is a square. -/
theorem isSquare_mul_of_not_isSquare (hp2 : p ≠ 2) {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0)
    (hsa : ¬ IsSquare a) (hsb : ¬ IsSquare b) : IsSquare (a * b) := by
  have hchar := ringChar_zmod_ne_two hp2
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have key : ∀ {c : ZMod p}, c ≠ 0 → ¬ IsSquare c → c ^ (Fintype.card (ZMod p) / 2) = -1 := by
    intro c hc hsc
    rcases FiniteField.pow_dichotomy hchar hc with h | h
    · exact absurd ((FiniteField.isSquare_iff hchar hc).mpr h) hsc
    · exact h
  rw [FiniteField.isSquare_iff hchar (mul_ne_zero ha hb), mul_pow, key ha hsa, key hb hsb]
  norm_num

/-! ### The main theorem for odd `p` -/

/-- **Proposition 2.23, odd `p`.**  `dim_{𝔽₂} ℚ_p^× / ℚ_p^{×2} = 2`. -/
@[gs_public]
theorem finrank_squareClassGroup_padic_of_odd (hp2 : p ≠ 2) :
    Module.finrank (ZMod 2) (SquareClassGroup ℚ_[p]) = 2 := by
  classical
  -- a quadratic non-residue and its lift
  obtain ⟨a₀, ha₀⟩ := FiniteField.exists_nonsquare (ringChar_zmod_ne_two hp2)
  have ha₀0 : a₀ ≠ 0 := fun h => ha₀ (by rw [h]; exact ⟨0, by simp⟩)
  set u₀ : ℤ_[p] := (ZMod.val a₀ : ℤ_[p]) with hu₀
  have htu₀ : PadicInt.toZMod u₀ = a₀ := by rw [hu₀, map_natCast, ZMod.natCast_zmod_val]
  have hu₀unit : IsUnit u₀ :=
    PadicInt.isUnit_iff.mpr (norm_eq_one_of_toZMod_ne_zero (by rw [htu₀]; exact ha₀0))
  set uU : ℤ_[p]ˣ := hu₀unit.unit with huU
  have huU_val : (uU : ℤ_[p]) = u₀ := IsUnit.unit_spec hu₀unit
  -- the two basis classes
  set pc := squareClass (pUnit p) with hpc
  set uc := squareClass (unitsMap p uU) with huc
  have hp_nsq : ¬ IsSquare (pUnit p) := not_isSquare_of_norm_eq_inv norm_pUnit
  have hu_nsq : ¬ IsSquare (unitsMap p uU) := fun h => by
    have := isSquare_toZMod_of_isSquare (isSquare_coe_of_isSquare_unitsMap h)
    rw [huU_val, htu₀] at this
    exact ha₀ this
  have hpu_nsq : ¬ IsSquare (pUnit p * unitsMap p uU) :=
    not_isSquare_of_norm_eq_inv
      (by rw [Units.val_mul, norm_mul, norm_pUnit, norm_unitsMap, mul_one])
  -- linear independence, via the subset-product criterion
  set d : Fin 2 → ℚ_[p]ˣ := ![pUnit p, unitsMap p uU] with hd
  have hli : LinearIndependent (ZMod 2) (fun i => squareClass (d i)) := by
    rw [linearIndependent_squareClass_iff]
    intro S hS
    have hS' : S = {0, 1} ∨ S = {0} ∨ S = {1} := by
      by_cases h0 : (0 : Fin 2) ∈ S <;> by_cases h1 : (1 : Fin 2) ∈ S
      · left; ext i; fin_cases i <;> simp [h0, h1]
      · right; left; ext i; fin_cases i <;> simp [h0, h1]
      · right; right; ext i; fin_cases i <;> simp [h0, h1]
      · exfalso
        obtain ⟨i, hi⟩ := hS
        fin_cases i <;> contradiction
    rcases hS' with rfl | rfl | rfl
    · rw [Finset.prod_pair (by decide)]; exact hpu_nsq
    · rw [Finset.prod_singleton]; exact hp_nsq
    · rw [Finset.prod_singleton]; exact hu_nsq
  have hli' : LinearIndependent (ZMod 2) ![pc, uc] := by
    have : (fun i => squareClass (d i)) = ![pc, uc] := by
      funext i; fin_cases i <;> rfl
    rw [← this]; exact hli
  -- spanning: every class lies in the span of `pc` and `uc`
  have hspan : ∀ c : SquareClassGroup ℚ_[p],
      c ∈ Submodule.span (ZMod 2) (Set.range ![pc, uc]) := by
    intro c
    obtain ⟨x, rfl⟩ := exists_squareClass_eq c
    -- decompose `x = p^n * v` with `v` a unit of `ℤ_p`
    set n : ℤ := (x : ℚ_[p]).valuation with hn
    have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    set v : ℚ_[p] := (x : ℚ_[p]) * (p : ℚ_[p]) ^ (-n) with hv
    have hvnorm : ‖v‖ = 1 := by
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      rw [hv, norm_mul, norm_zpow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation x.ne_zero, ← hn,
        inv_zpow, ← zpow_neg, neg_neg, ← zpow_add₀ hpR, neg_add_cancel, zpow_zero]
    set vI : ℤ_[p] := ⟨v, hvnorm.le⟩ with hvI
    have hvI_norm : ‖vI‖ = 1 := by rw [hvI, PadicInt.norm_eq_padic_norm]; exact hvnorm
    have hvunit : IsUnit vI := PadicInt.isUnit_iff.mpr hvI_norm
    set vU : ℤ_[p]ˣ := hvunit.unit with hvU
    have hvU_val : (vU : ℤ_[p]) = vI := IsUnit.unit_spec hvunit
    have hx : x = pUnit p ^ n * unitsMap p vU := by
      apply Units.ext
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, val_pUnit, val_unitsMap, hvU_val]
      change (x : ℚ_[p]) = (p : ℚ_[p]) ^ n * v
      rw [hv, ← mul_assoc, mul_comm ((p : ℚ_[p]) ^ n), mul_assoc, ← zpow_add₀ hp0,
        add_neg_cancel, zpow_zero, mul_one]
    -- the class of the unit part is `0` or `uc`
    have hvclass : squareClass (unitsMap p vU) = 0 ∨ squareClass (unitsMap p vU) = uc := by
      have htv : PadicInt.toZMod vI ≠ 0 := by
        intro h0
        have := (norm_lt_one_iff_toZMod_eq_zero vI).mpr h0
        rw [hvI_norm] at this
        exact lt_irrefl _ this
      by_cases hsq : IsSquare (PadicInt.toZMod vI)
      · left
        rw [squareClass_eq_zero_iff]
        exact isSquare_unitsMap_of_isSquare
          (PadicInt.isSquare_of_isSquare_toZMod hp2 hvunit hsq)
      · right
        have hprod : IsSquare (PadicInt.toZMod (vI * u₀)) := by
          rw [map_mul, htu₀]
          exact isSquare_mul_of_not_isSquare hp2 htv ha₀0 hsq ha₀
        have hsqI : IsSquare (vI * u₀) :=
          PadicInt.isSquare_of_isSquare_toZMod hp2 (hvunit.mul hu₀unit) hprod
        have h0 : squareClass (unitsMap p vU) + uc = 0 := by
          rw [huc, ← squareClass_mul, ← map_mul, squareClass_eq_zero_iff]
          apply isSquare_unitsMap_of_isSquare
          rw [Units.val_mul, hvU_val, huU_val]
          exact hsqI
        calc squareClass (unitsMap p vU)
            = squareClass (unitsMap p vU) + (uc + uc) := by
              rw [add_self_squareClassGroup]
              exact (add_zero (squareClass (unitsMap p vU))).symm
          _ = (squareClass (unitsMap p vU) + uc) + uc := by abel
          _ = 0 + uc := by rw [h0]
          _ = uc := zero_add uc
    rw [hx, squareClass_mul, squareClass_zpow]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) ?_
    rcases hvclass with h | h
    · rw [h]; exact Submodule.zero_mem _
    · rw [h]; exact Submodule.subset_span ⟨1, rfl⟩
  have htop : ⊤ ≤ Submodule.span (ZMod 2) (Set.range ![pc, uc]) := fun c _ => hspan c
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli' htop), Fintype.card_fin]

/-! ### The dyadic case -/

section Two

/-- Reduction modulo `8` of a `2`-adic integer. -/
noncomputable abbrev toZMod8 : ℤ_[2] →+* ZMod (2 ^ 3) := PadicInt.toZModPow 3

theorem toZMod8_eq_one_iff (u : ℤ_[2]) :
    toZMod8 u = 1 ↔ u - 1 ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 3} := by
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]

/-- A `2`-adic integer is a unit iff its residue mod `2` is nonzero, iff its residue mod `8` is
odd. -/
theorem cast_toZMod8_ne_zero_of_isUnit {u : ℤ_[2]} (hu : IsUnit u) :
    (ZMod.cast (toZMod8 u) : ZMod (2 ^ 1)) ≠ 0 := by
  rw [toZMod8, PadicInt.cast_toZModPow 1 3 (by norm_num)]
  intro h0
  have hker : u ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 1} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker]; exact h0
  rw [pow_one, ← PadicInt.maximalIdeal_eq_span_p, IsLocalRing.mem_maximalIdeal] at hker
  exact hker hu

theorem toZMod8_mem_of_isUnit {u : ℤ_[2]} (hu : IsUnit u) :
    toZMod8 u = 1 ∨ toZMod8 u = 3 ∨ toZMod8 u = 5 ∨ toZMod8 u = 7 := by
  have key : ∀ a : ZMod (2 ^ 3), (ZMod.cast a : ZMod (2 ^ 1)) ≠ 0 →
      a = 1 ∨ a = 3 ∨ a = 5 ∨ a = 7 := by decide
  exact key _ (cast_toZMod8_ne_zero_of_isUnit hu)

/-- **Hensel at `2`.**  A `2`-adic integer congruent to `1` mod `8` is a square. -/
theorem isSquare_of_toZMod8_eq_one {u : ℤ_[2]} (h : toZMod8 u = 1) : IsSquare u := by
  have hmem : u - 1 ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ 3} := (toZMod8_eq_one_iff u).mp h
  have hnorm : ‖u - 1‖ ≤ ((2 : ℕ) : ℝ) ^ (-(3 : ℕ) : ℤ) :=
    (PadicInt.norm_le_pow_iff_mem_span_pow (u - 1) 3).mpr hmem
  set F : ℤ_[2][X] := X ^ 2 - C u with hF
  have hFa : aeval (1 : ℤ_[2]) F = 1 - u := by simp [hF]
  have hF'a : aeval (1 : ℤ_[2]) (derivative F) = 2 := by
    simp [hF]
    norm_num
  have h2 : ‖(2 : ℤ_[2])‖ = (2 : ℝ)⁻¹ := by
    have := PadicInt.norm_p (p := 2)
    simpa using this
  have hlt : ‖aeval (1 : ℤ_[2]) F‖ < ‖aeval (1 : ℤ_[2]) (derivative F)‖ ^ 2 := by
    rw [hFa, hF'a, h2]
    calc ‖(1 : ℤ_[2]) - u‖ = ‖u - 1‖ := norm_sub_rev _ _
      _ ≤ ((2 : ℕ) : ℝ) ^ (-(3 : ℕ) : ℤ) := hnorm
      _ < ((2 : ℝ)⁻¹) ^ 2 := by norm_num
  obtain ⟨z, hz, -, -, -⟩ := hensels_lemma hlt
  have hz' : z ^ 2 - u = 0 := by simpa [hF] using hz
  exact ⟨z, by rw [sq] at hz'; exact (sub_eq_zero.mp hz').symm⟩

/-- The square of a `2`-adic unit is `1` mod `8`. -/
theorem toZMod8_eq_one_of_isSquare {u : ℤ_[2]} (hu : IsUnit u) (h : IsSquare u) :
    toZMod8 u = 1 := by
  obtain ⟨z, hz⟩ := h
  have hz' : IsUnit z := isUnit_of_mul_isUnit_left (hz ▸ hu)
  have key : ∀ a : ZMod (2 ^ 3), (ZMod.cast a : ZMod (2 ^ 1)) ≠ 0 → a * a = 1 := by decide
  rw [hz, map_mul]
  exact key _ (cast_toZMod8_ne_zero_of_isUnit hz')

/-- The units `3` and `5` of `ℤ_2`. -/
theorem isUnit_three : IsUnit (3 : ℤ_[2]) :=
  PadicInt.isUnit_iff.mpr (norm_eq_one_of_toZMod_ne_zero (by rw [map_ofNat]; decide))

theorem isUnit_five : IsUnit (5 : ℤ_[2]) :=
  PadicInt.isUnit_iff.mpr (norm_eq_one_of_toZMod_ne_zero (by rw [map_ofNat]; decide))

/-- **Proposition 2.23, `p = 2`.**  `dim_{𝔽₂} ℚ_2^× / ℚ_2^{×2} = 3`. -/
@[gs_public]
theorem finrank_squareClassGroup_padic_two :
    Module.finrank (ZMod 2) (SquareClassGroup ℚ_[2]) = 3 := by
  classical
  set u3 : ℤ_[2]ˣ := isUnit_three.unit with hu3
  set u5 : ℤ_[2]ˣ := isUnit_five.unit with hu5
  have hu3v : (u3 : ℤ_[2]) = 3 := IsUnit.unit_spec isUnit_three
  have hu5v : (u5 : ℤ_[2]) = 5 := IsUnit.unit_spec isUnit_five
  set c2 := squareClass (pUnit 2) with hc2
  set c3 := squareClass (unitsMap 2 u3) with hc3
  set c5 := squareClass (unitsMap 2 u5) with hc5
  -- non-squares: valuation one, or residue mod 8 not one
  have h2_nsq : ¬ IsSquare (pUnit 2) := not_isSquare_of_norm_eq_inv norm_pUnit
  have hunit_nsq : ∀ v : ℤ_[2]ˣ, toZMod8 (v : ℤ_[2]) ≠ 1 → ¬ IsSquare (unitsMap 2 v) :=
    fun v hv h => hv (toZMod8_eq_one_of_isSquare v.isUnit (isSquare_coe_of_isSquare_unitsMap h))
  have h2u_nsq : ∀ v : ℤ_[2]ˣ, ¬ IsSquare (pUnit 2 * unitsMap 2 v) := fun v =>
    not_isSquare_of_norm_eq_inv
      (by rw [Units.val_mul, norm_mul, norm_pUnit, norm_unitsMap, mul_one])
  have h3 : toZMod8 (u3 : ℤ_[2]) = 3 := by rw [hu3v, map_ofNat]
  have h5 : toZMod8 (u5 : ℤ_[2]) = 5 := by rw [hu5v, map_ofNat]
  have h35 : toZMod8 ((u3 * u5 : ℤ_[2]ˣ) : ℤ_[2]) = 7 := by
    rw [Units.val_mul, map_mul, h3, h5]; decide
  -- linear independence via the subset-product criterion
  set d : Fin 3 → ℚ_[2]ˣ := ![pUnit 2, unitsMap 2 u3, unitsMap 2 u5] with hd
  have hli : LinearIndependent (ZMod 2) (fun i => squareClass (d i)) := by
    rw [linearIndependent_squareClass_iff]
    intro S hS
    have hS' : S = {0, 1, 2} ∨ S = {0, 1} ∨ S = {0, 2} ∨ S = {1, 2} ∨ S = {0} ∨ S = {1} ∨
        S = {2} := by
      by_cases h0 : (0 : Fin 3) ∈ S <;> by_cases h1 : (1 : Fin 3) ∈ S <;>
        by_cases h2 : (2 : Fin 3) ∈ S
      · left; ext i; fin_cases i <;> simp [h0, h1, h2]
      · right; left; ext i; fin_cases i <;> simp [h0, h1, h2]
      · right; right; left; ext i; fin_cases i <;> simp [h0, h1, h2]
      · right; right; right; right; left; ext i; fin_cases i <;> simp [h0, h1, h2]
      · right; right; right; left; ext i; fin_cases i <;> simp [h0, h1, h2]
      · right; right; right; right; right; left; ext i; fin_cases i <;> simp [h0, h1, h2]
      · right; right; right; right; right; right; ext i; fin_cases i <;> simp [h0, h1, h2]
      · exfalso
        obtain ⟨i, hi⟩ := hS
        fin_cases i <;> contradiction
    have hprod3 : ∏ i ∈ ({0, 1, 2} : Finset (Fin 3)), d i = d 0 * (d 1 * d 2) := by
      rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
    rcases hS' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hprod3]
      change ¬ IsSquare (pUnit 2 * (unitsMap 2 u3 * unitsMap 2 u5))
      rw [← map_mul]
      exact h2u_nsq _
    · rw [Finset.prod_pair (by decide)]; exact h2u_nsq u3
    · rw [Finset.prod_pair (by decide)]; exact h2u_nsq u5
    · rw [Finset.prod_pair (by decide)]
      change ¬ IsSquare (unitsMap 2 u3 * unitsMap 2 u5)
      rw [← map_mul]
      exact hunit_nsq (u3 * u5) (by rw [h35]; decide)
    · rw [Finset.prod_singleton]; exact h2_nsq
    · rw [Finset.prod_singleton]; exact hunit_nsq u3 (by rw [h3]; decide)
    · rw [Finset.prod_singleton]; exact hunit_nsq u5 (by rw [h5]; decide)
  have hli' : LinearIndependent (ZMod 2) ![c2, c3, c5] := by
    have : (fun i => squareClass (d i)) = ![c2, c3, c5] := by
      funext i; fin_cases i <;> rfl
    rw [← this]; exact hli
  -- spanning
  have hspan : ∀ c : SquareClassGroup ℚ_[2],
      c ∈ Submodule.span (ZMod 2) (Set.range ![c2, c3, c5]) := by
    intro c
    obtain ⟨x, rfl⟩ := exists_squareClass_eq c
    set n : ℤ := (x : ℚ_[2]).valuation with hn
    have hp0 : ((2 : ℕ) : ℚ_[2]) ≠ 0 := by norm_num
    set v : ℚ_[2] := (x : ℚ_[2]) * ((2 : ℕ) : ℚ_[2]) ^ (-n) with hv
    have hvnorm : ‖v‖ = 1 := by
      have hpR : ((2 : ℕ) : ℝ) ≠ 0 := by norm_num
      rw [hv, norm_mul, norm_zpow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation x.ne_zero, ← hn,
        inv_zpow, ← zpow_neg, neg_neg, ← zpow_add₀ hpR, neg_add_cancel, zpow_zero]
    set vI : ℤ_[2] := ⟨v, hvnorm.le⟩ with hvI
    have hvI_norm : ‖vI‖ = 1 := by rw [hvI, PadicInt.norm_eq_padic_norm]; exact hvnorm
    have hvunit : IsUnit vI := PadicInt.isUnit_iff.mpr hvI_norm
    set vU : ℤ_[2]ˣ := hvunit.unit with hvU
    have hvU_val : (vU : ℤ_[2]) = vI := IsUnit.unit_spec hvunit
    have hx : x = pUnit 2 ^ n * unitsMap 2 vU := by
      apply Units.ext
      rw [Units.val_mul, Units.val_zpow_eq_zpow_val, val_pUnit, val_unitsMap, hvU_val]
      change (x : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) ^ n * v
      rw [hv, ← mul_assoc, mul_comm (((2 : ℕ) : ℚ_[2]) ^ n), mul_assoc, ← zpow_add₀ hp0,
        add_neg_cancel, zpow_zero, mul_one]
    -- the class of the unit part, by its residue mod 8
    have hvclass : squareClass (unitsMap 2 vU) = 0 ∨ squareClass (unitsMap 2 vU) = c3 ∨
        squareClass (unitsMap 2 vU) = c5 ∨ squareClass (unitsMap 2 vU) = c3 + c5 := by
      -- `w` a unit with `vI * w ≡ 1 mod 8` makes `vI * w` a square
      have step : ∀ w : ℤ_[2]ˣ, toZMod8 (vI * w) = 1 →
          squareClass (unitsMap 2 vU) + squareClass (unitsMap 2 w) = 0 := fun w hw => by
        rw [← squareClass_mul, ← map_mul, squareClass_eq_zero_iff]
        apply isSquare_unitsMap_of_isSquare
        rw [Units.val_mul, hvU_val]
        exact isSquare_of_toZMod8_eq_one hw
      have cancel : ∀ a b : SquareClassGroup ℚ_[2], a + b = 0 → a = b := fun a b hab =>
        calc a = a + (b + b) := by
              rw [add_self_squareClassGroup]; exact (add_zero a).symm
          _ = (a + b) + b := by abel
          _ = 0 + b := by rw [hab]
          _ = b := zero_add b
      rcases toZMod8_mem_of_isUnit hvunit with h | h | h | h
      · left
        rw [squareClass_eq_zero_iff]
        exact isSquare_unitsMap_of_isSquare (isSquare_of_toZMod8_eq_one h)
      · right; left
        exact cancel _ _ (step u3 (by rw [map_mul, h, hu3v, map_ofNat]; decide))
      · right; right; left
        exact cancel _ _ (step u5 (by rw [map_mul, h, hu5v, map_ofNat]; decide))
      · right; right; right
        have := cancel _ _ (step (u3 * u5) (by rw [map_mul, h, h35]; decide))
        rw [map_mul, squareClass_mul] at this
        exact this
    rw [hx, squareClass_mul, squareClass_zpow]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) ?_
    rcases hvclass with h | h | h | h
    · rw [h]; exact Submodule.zero_mem _
    · rw [h]; exact Submodule.subset_span ⟨1, rfl⟩
    · rw [h]; exact Submodule.subset_span ⟨2, rfl⟩
    · rw [h]
      exact Submodule.add_mem _ (Submodule.subset_span ⟨1, rfl⟩) (Submodule.subset_span ⟨2, rfl⟩)
  have htop : ⊤ ≤ Submodule.span (ZMod 2) (Set.range ![c2, c3, c5]) := fun c _ => hspan c
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli' htop), Fintype.card_fin]

end Two

/-- **Proposition 2.23.**  `dim_{𝔽₂} ℚ_p^× / ℚ_p^{×2}` is `3` for `p = 2` and `2` otherwise. -/
theorem finrank_squareClassGroup_padic (p : ℕ) [Fact p.Prime] :
    Module.finrank (ZMod 2) (SquareClassGroup ℚ_[p]) = if p = 2 then 3 else 2 := by
  split_ifs with h
  · subst h; exact finrank_squareClassGroup_padic_two
  · exact finrank_squareClassGroup_padic_of_odd h

end GSArith.Arithmetic

end
