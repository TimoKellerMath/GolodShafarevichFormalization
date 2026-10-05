/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Field.ZMod
public import TauCeti.FieldTheory.SquareClassGroup.Basic
public import TauCeti.Algebra.Group.Units.Basic
public import GSArith.Ledger
public import GSArith.LinearAlgebra.ZModTwo

/-!
# Branch-point square classes (Proposition 2.16, the square-class half)

Proposition 2.16 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic
surfaces*, identifies `J(C)[2]` for `C : y² = ∏_{a ∈ ℬ} (x - a)` with the classes of the
products `∏_{a ∈ E} (x - a)`, `E ⊆ ℬ` even, in the square-class group of `k̄(x)(√F)`, and shows
that the only relations are `E = ∅` and `E = ℬ`.  The argument has two halves:

1. an element `a ∈ k̄(x)` is a square in `k̄(x)(√F)` iff `a` or `a/F` is a square in `k̄(x)`
   (squaring `b + c√F` forces `bc = 0`);
2. `∏_{a ∈ E}(x - a)` is not a square in `k̄(x)` for `E ≠ ∅`, and `∏_{a ∈ E}(x - a)/F` is not a
   square for `E ≠ ℬ`: the product has odd valuation at a root in `E`, resp. at a root of
   `F` outside `E`.

This file proves both halves and assembles them, over any field `k` (of characteristic `≠ 2`
where the quadratic extension enters), as statements about `RatFunc k` and the quadratic
extension `k(x)(√F) := k(x)[X]/(X² - F)`:

* `GSArith.Arithmetic.not_isSquare_linProd`, `not_isSquare_linProd_div`: the parity core (2);
* `GSArith.Arithmetic.isSquare_algebraMap_iff_of_quadratic`: the description (1) of squares
  in a quadratic extension `K ⊕ K·s`, `s² = F`, over any field `K` with `2 ≠ 0`, and its
  instance `isSquare_algebraMap_quadExt_iff` for `K(√F) = K[X]/(X² - F)`;
* `GSArith.Arithmetic.isSquare_branchExt_linProd_iff`: for `E ⊆ ℬ`, `∏_{a ∈ E}(x - a)` is a
  square in `k(x)(√F)` iff `E = ∅` or `E = ℬ`;
* `GSArith.Arithmetic.branchMap`, `ker_branchMap`, `finrank_range_branchMap`,
  `finrank_map_evenSubsets_branchMap`: the map `E ↦ [∏_{a ∈ E}(x - a)]` from subsets of `ℬ`
  to the square-class group of `k(x)(√F)` has kernel `{∅, ℬ}`, so its image has dimension
  `|ℬ| - 1`, and the even subsets map onto a subspace of dimension `|ℬ| - 2 = 2g`.

The Kummer identification of these classes with `J(C)[2]` (Stacks `03RQ`) is Tier C and stays
in the interface (`GSArith.Oracle`).  Proposition 3.1's independence of the `uᵢ` is derived
from this file in `GSArith.Arithmetic.MultiquadraticCover`.
-/

@[expose] public section

namespace GSArith.Arithmetic

open Polynomial

/-! ### The parity core -/

section Parity

variable {k : Type*} [Field k]

/-- The product of the linear factors `X - a`, `a ∈ E`. -/
noncomputable abbrev linProd (E : Finset k) : k[X] := ∏ a ∈ E, (X - C a)

theorem linProd_ne_zero (E : Finset k) : linProd E ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun a _ => X_sub_C_ne_zero a

/-- `linProd E` has root multiplicity one at every `b ∈ E`. -/
theorem rootMultiplicity_linProd {E : Finset k} {b : k} (hb : b ∈ E) :
    rootMultiplicity b (linProd E) = 1 := by
  classical
  unfold linProd
  rw [← Finset.mul_prod_erase E _ hb,
    rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero b) (linProd_ne_zero (E.erase b))),
    rootMultiplicity_X_sub_C_self]
  have : ¬ (∏ a ∈ E.erase b, (X - C a)).IsRoot b := by
    rw [IsRoot.def, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    exact Finset.prod_ne_zero_iff.mpr fun a ha =>
      sub_ne_zero.mpr (Finset.ne_of_mem_erase ha).symm
  rw [rootMultiplicity_eq_zero this]

/-- `linProd E` has root multiplicity zero at every `b ∉ E`. -/
theorem rootMultiplicity_linProd_of_notMem {E : Finset k} {b : k} (hb : b ∉ E) :
    rootMultiplicity b (linProd E) = 0 := by
  apply rootMultiplicity_eq_zero
  rw [IsRoot.def, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  exact Finset.prod_ne_zero_iff.mpr fun a ha => sub_ne_zero.mpr fun h => hb (h ▸ ha)

/-- A polynomial identity `P * (d * d) = Q * (n * n)` with `d, n ≠ 0` forces the root
multiplicities of `P` and `Q` at every point to have the same parity. -/
theorem rootMultiplicity_parity {P Q d n : k[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) (hd : d ≠ 0)
    (hn : n ≠ 0) (h : P * (d * d) = Q * (n * n)) (b : k) :
    rootMultiplicity b P + 2 * rootMultiplicity b d =
      rootMultiplicity b Q + 2 * rootMultiplicity b n := by
  have h1 : rootMultiplicity b (P * (d * d)) =
      rootMultiplicity b P + 2 * rootMultiplicity b d := by
    rw [rootMultiplicity_mul (mul_ne_zero hP (mul_ne_zero hd hd)),
      rootMultiplicity_mul (mul_ne_zero hd hd)]
    ring
  have h2 : rootMultiplicity b (Q * (n * n)) =
      rootMultiplicity b Q + 2 * rootMultiplicity b n := by
    rw [rootMultiplicity_mul (mul_ne_zero hQ (mul_ne_zero hn hn)),
      rootMultiplicity_mul (mul_ne_zero hn hn)]
    ring
  rw [← h1, ← h2, h]

/-- Writing a rational function `r = a / b` as `num / denom` and clearing denominators. -/
theorem polynomial_eq_of_eq_div_sq {P Q : k[X]} (hQ : Q ≠ 0) (r : RatFunc k)
    (h : algebraMap k[X] (RatFunc k) P / algebraMap k[X] (RatFunc k) Q = r * r) :
    P * (r.denom * r.denom) = Q * (r.num * r.num) := by
  have hinj := RatFunc.algebraMap_injective k
  have hd : algebraMap k[X] (RatFunc k) r.denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (RatFunc.denom_ne_zero r)
  have hQ' : algebraMap k[X] (RatFunc k) Q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hQ
  rw [← RatFunc.num_div_denom r] at h
  apply hinj
  simp only [map_mul]
  field_simp at h
  linear_combination h

/-- **Proposition 2.16, first parity statement.**  For nonempty `E`, `∏_{a ∈ E} (x - a)` is not a
square in `k(x)`. -/
theorem not_isSquare_linProd {E : Finset k} (hE : E.Nonempty) :
    ¬ IsSquare (algebraMap k[X] (RatFunc k) (linProd E)) := by
  rintro ⟨r, hr⟩
  obtain ⟨b, hb⟩ := hE
  have h := polynomial_eq_of_eq_div_sq (P := linProd E) (Q := 1) one_ne_zero r
    (by rw [map_one, div_one]; exact hr)
  have hn : r.num ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_zero] at h
    exact mul_ne_zero (linProd_ne_zero E) (mul_ne_zero (RatFunc.denom_ne_zero r)
      (RatFunc.denom_ne_zero r)) h
  have := rootMultiplicity_parity (linProd_ne_zero E) one_ne_zero (RatFunc.denom_ne_zero r) hn h b
  have h1 : rootMultiplicity b (1 : k[X]) = 0 := rootMultiplicity_eq_zero (by simp)
  rw [rootMultiplicity_linProd hb, h1] at this
  omega

/-- **Proposition 2.16, second parity statement.**  For `E ⊆ B` with `E ≠ B`,
`∏_{a ∈ E} (x - a) / ∏_{a ∈ B} (x - a)` is not a square in `k(x)`. -/
theorem not_isSquare_linProd_div {E B : Finset k} (hEB : E ⊆ B) (hne : E ≠ B) :
    ¬ IsSquare (algebraMap k[X] (RatFunc k) (linProd E) /
      algebraMap k[X] (RatFunc k) (linProd B)) := by
  rintro ⟨r, hr⟩
  obtain ⟨b, hbB, hbE⟩ := Finset.exists_of_ssubset (lt_of_le_of_ne hEB hne)
  have h := polynomial_eq_of_eq_div_sq (linProd_ne_zero B) r hr
  have hn : r.num ≠ 0 := by
    intro h0
    rw [h0, mul_zero, mul_zero] at h
    exact mul_ne_zero (linProd_ne_zero E) (mul_ne_zero (RatFunc.denom_ne_zero r)
      (RatFunc.denom_ne_zero r)) h
  have := rootMultiplicity_parity (linProd_ne_zero E) (linProd_ne_zero B) (RatFunc.denom_ne_zero r)
    hn h b
  rw [rootMultiplicity_linProd_of_notMem hbE, rootMultiplicity_linProd hbB] at this
  omega

/-- The two parity statements together: for `E ⊆ B`, `∏_{a ∈ E}(x - a)` is a square in `k(x)`
iff `E = ∅`, and its quotient by `∏_{a ∈ B}(x - a)` is a square iff `E = B`. -/
theorem isSquare_linProd_iff {E : Finset k} :
    IsSquare (algebraMap k[X] (RatFunc k) (linProd E)) ↔ E = ∅ := by
  constructor
  · intro h
    by_contra hne
    exact not_isSquare_linProd (Finset.nonempty_iff_ne_empty.mpr hne) h
  · rintro rfl
    exact ⟨1, by simp⟩

theorem isSquare_linProd_div_iff {E B : Finset k} (hEB : E ⊆ B) :
    IsSquare (algebraMap k[X] (RatFunc k) (linProd E) /
      algebraMap k[X] (RatFunc k) (linProd B)) ↔ E = B := by
  constructor
  · intro h
    by_contra hne
    exact not_isSquare_linProd_div hEB hne h
  · rintro rfl
    refine ⟨1, ?_⟩
    rw [div_self ((map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).mpr (linProd_ne_zero E)),
      mul_one]

end Parity

/-! ### Squares in a quadratic extension -/

section Quadratic

variable {K L : Type*} [Field K] [CommRing L] [Algebra K L]

/-- **Squares in `K ⊕ K·s`, `s² = F`.**  If `2 ≠ 0` in `K`, `L` is spanned by `1, s` with
`1, s` linearly independent, and `s² = F ≠ 0`, then `a ∈ K` is a square in `L` iff `a` or `a/F`
is a square in `K`: in `(b + cs)² = (b² + c²F) + 2bc·s` the mixed term forces `bc = 0`. -/
theorem isSquare_algebraMap_iff_of_quadratic [NeZero (2 : K)] {s : L} {F : K} (hF : F ≠ 0)
    (hs : s * s = algebraMap K L F)
    (hspan : ∀ x : L, ∃ b c : K, x = algebraMap K L b + algebraMap K L c * s)
    (hind : ∀ b c : K, algebraMap K L b + algebraMap K L c * s = 0 → b = 0 ∧ c = 0) (a : K) :
    IsSquare (algebraMap K L a) ↔ IsSquare a ∨ IsSquare (a / F) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨b, c, rfl⟩ := hspan x
    have hsq : (algebraMap K L b + algebraMap K L c * s) *
        (algebraMap K L b + algebraMap K L c * s) =
          algebraMap K L (b * b + c * c * F) + algebraMap K L (2 * b * c) * s := by
      simp only [map_add, map_mul, map_ofNat]
      linear_combination (algebraMap K L c * algebraMap K L c) * hs
    have h0 : algebraMap K L (a - (b * b + c * c * F)) + algebraMap K L (-(2 * b * c)) * s = 0 := by
      rw [map_sub, map_neg, hx, hsq]
      ring
    obtain ⟨h1, h2⟩ := hind _ _ h0
    rw [sub_eq_zero] at h1
    rw [neg_eq_zero, mul_assoc] at h2
    rcases mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left (NeZero.ne 2)) with hb | hc
    · right
      refine ⟨c, ?_⟩
      rw [h1, hb]
      field_simp
      ring
    · left
      refine ⟨b, ?_⟩
      rw [h1, hc]
      ring
  · rintro (⟨b, hb⟩ | ⟨c, hc⟩)
    · exact ⟨algebraMap K L b, by rw [hb, map_mul]⟩
    · refine ⟨algebraMap K L c * s, ?_⟩
      have ha : a = c * c * F := by
        rw [← hc]
        field_simp
      rw [ha, map_mul, map_mul]
      linear_combination (-(algebraMap K L c * algebraMap K L c)) * hs

/-! #### The quadratic extension `K(√F) := K[X]/(X² - F)` -/

variable (F : K)

/-- The polynomial `X² - F`. -/
noncomputable abbrev quadPoly : K[X] := X ^ 2 - C F

theorem quadPoly_monic : (quadPoly F).Monic := monic_X_pow_sub_C F two_ne_zero

theorem quadPoly_natDegree : (quadPoly F).natDegree = 2 := natDegree_X_pow_sub_C

theorem quadPoly_ne_one : quadPoly F ≠ 1 := by
  intro h
  have := congrArg natDegree h
  rw [quadPoly_natDegree, natDegree_one] at this
  omega

/-- `X² - F` is irreducible iff `F` is not a square. -/
theorem irreducible_quadPoly_iff : Irreducible (quadPoly F) ↔ ¬ IsSquare F := by
  rw [quadPoly, X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two]
  constructor
  · rintro h ⟨b, hb⟩
    exact h b (by rw [hb, sq])
  · intro h b hb
    exact h ⟨b, by rw [← hb, sq]⟩

/-- `K(√F) := K[X]/(X² - F)`, a field when `F` is not a square. -/
abbrev QuadExt : Type _ := AdjoinRoot (quadPoly F)

/-- `√F ∈ K(√F)`. -/
noncomputable abbrev sqrtF : QuadExt F := AdjoinRoot.root (quadPoly F)

theorem sqrtF_mul_self : sqrtF F * sqrtF F = algebraMap K (QuadExt F) F := by
  have h := AdjoinRoot.mk_self (f := quadPoly F)
  rw [quadPoly, map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero] at h
  rw [← sq, h]
  rfl

/-- `K(√F)` is spanned by `1, √F`. -/
theorem quadExt_span (x : QuadExt F) :
    ∃ b c : K, x = algebraMap K (QuadExt F) b + algebraMap K (QuadExt F) c * sqrtF F := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    refine ⟨(p %ₘ quadPoly F).coeff 0, (p %ₘ quadPoly F).coeff 1, ?_⟩
    have hdeg : (p %ₘ quadPoly F).natDegree ≤ 1 := by
      have := natDegree_modByMonic_lt p (quadPoly_monic F) (quadPoly_ne_one F)
      rw [quadPoly_natDegree] at this
      omega
    change AdjoinRoot.mk _ p = AdjoinRoot.mk _ (C _) + AdjoinRoot.mk _ (C _) * AdjoinRoot.mk _ X
    rw [← map_mul, ← map_add, AdjoinRoot.mk_eq_mk]
    refine ⟨p /ₘ quadPoly F, ?_⟩
    have hmod := modByMonic_add_div p (quadPoly F)
    have hlin := eq_X_add_C_of_natDegree_le_one hdeg
    linear_combination hlin - hmod

/-- `1, √F` are linearly independent over `K`. -/
theorem quadExt_independent (b c : K)
    (h : algebraMap K (QuadExt F) b + algebraMap K (QuadExt F) c * sqrtF F = 0) :
    b = 0 ∧ c = 0 := by
  change AdjoinRoot.mk _ (C b) + AdjoinRoot.mk _ (C c) * AdjoinRoot.mk _ X = 0 at h
  rw [← map_mul, ← map_add, AdjoinRoot.mk_eq_zero] at h
  have h' : quadPoly F ∣ C c * X + C b := by rwa [add_comm] at h
  have hq : C c * X + C b = 0 := by
    by_contra hne
    have h1 := natDegree_le_of_dvd h' hne
    have h2 : (C c * X + C b).natDegree ≤ 1 := natDegree_linear_le
    rw [quadPoly_natDegree] at h1
    omega
  constructor
  · have := congrArg (fun q => coeff q 0) hq
    simpa using this
  · have := congrArg (fun q => coeff q 1) hq
    simpa using this

/-- **Squares in `K(√F)`.**  For `2 ≠ 0` in `K` and `F ≠ 0`: `a ∈ K` is a square in `K(√F)` iff
`a` or `a/F` is a square in `K`. -/
theorem isSquare_algebraMap_quadExt_iff [NeZero (2 : K)] (hF : F ≠ 0) (a : K) :
    IsSquare (algebraMap K (QuadExt F) a) ↔ IsSquare a ∨ IsSquare (a / F) :=
  isSquare_algebraMap_iff_of_quadratic hF (sqrtF_mul_self F) (quadExt_span F)
    (quadExt_independent F) a

end Quadratic

/-! ### The branch classes in `k(x)(√F)` -/

section BranchExt

variable {k : Type*} [Field k]

/-- `F = ∏_{a ∈ B}(x - a) ∈ k(x)`. -/
noncomputable abbrev branchF (B : Finset k) : RatFunc k :=
  algebraMap k[X] (RatFunc k) (linProd B)

theorem branchF_ne_zero (B : Finset k) : branchF B ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).mpr (linProd_ne_zero B)

/-- `k(x)(√F)` for `F = ∏_{a ∈ B}(x - a)`. -/
abbrev BranchExt (B : Finset k) : Type _ := QuadExt (branchF B)

/-- For nonempty `B`, `X² - F` is irreducible, so `k(x)(√F)` is a field. -/
theorem irreducible_quadPoly_branchF {B : Finset k} (hB : B.Nonempty) :
    Irreducible (quadPoly (branchF B)) :=
  (irreducible_quadPoly_iff _).mpr (not_isSquare_linProd hB)

instance instFactIrreducibleBranchF (B : Finset k) [hB : Fact B.Nonempty] :
    Fact (Irreducible (quadPoly (branchF B))) :=
  ⟨irreducible_quadPoly_branchF hB.out⟩

/-- **Proposition 2.16, the square classes.**  For `E ⊆ B` and `2 ≠ 0` in `k`,
`∏_{a ∈ E}(x - a)` is a square in `k(x)(√F)` iff `E = ∅` or `E = B`. -/
theorem isSquare_branchExt_linProd_iff [NeZero (2 : k)] {E B : Finset k} (hEB : E ⊆ B) :
    IsSquare (algebraMap (RatFunc k) (BranchExt B) (algebraMap k[X] (RatFunc k) (linProd E))) ↔
      E = ∅ ∨ E = B := by
  have : NeZero (2 : RatFunc k) := ⟨by
    have h2 : (2 : k[X]) ≠ 0 := by
      intro h
      have := congrArg (fun q => coeff q 0) h
      simp only [coeff_ofNat_zero, coeff_zero] at this
      exact NeZero.ne (2 : k) this
    rw [← map_ofNat (algebraMap k[X] (RatFunc k)) 2]
    exact (map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).mpr h2⟩
  rw [isSquare_algebraMap_quadExt_iff _ (branchF_ne_zero B), isSquare_linProd_iff,
    isSquare_linProd_div_iff hEB]

end BranchExt

/-! ### Subsets of `B` as `𝔽₂`-valued functions -/

section SubsetOf

open GSArith.LinearAlgebra

variable {k : Type*} (B : Finset k)

/-- The subset of `B` where a `𝔽₂`-valued function on `B` is `1`. -/
def subsetOf (f : B → ZMod 2) : Finset k :=
  (Finset.univ.filter (fun a : B => f a = 1)).map (Function.Embedding.subtype _)

theorem subsetOf_subset (f : B → ZMod 2) : subsetOf B f ⊆ B := by
  intro a ha
  obtain ⟨⟨a, haB⟩, -, rfl⟩ := Finset.mem_map.mp ha
  exact haB

theorem mem_subsetOf {f : B → ZMod 2} {a : B} : (a : k) ∈ subsetOf B f ↔ f a = 1 := by
  rw [subsetOf, Finset.mem_map]
  constructor
  · rintro ⟨b, hb, hab⟩
    have : b = a := Subtype.ext hab
    subst this
    exact (Finset.mem_filter.mp hb).2
  · intro h
    exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

theorem subsetOf_eq_empty_iff {f : B → ZMod 2} : subsetOf B f = ∅ ↔ f = 0 := by
  constructor
  · intro h
    funext a
    rcases zmod_two_eq_zero_or_one (f a) with h0 | h1
    · exact h0
    · have : (a : k) ∈ subsetOf B f := (mem_subsetOf B).mpr h1
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
  · rintro rfl
    rw [Finset.eq_empty_iff_forall_notMem]
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp ha
    have := (Finset.mem_filter.mp hb).2
    simp at this

theorem subsetOf_eq_iff {f : B → ZMod 2} : subsetOf B f = B ↔ f = 1 := by
  constructor
  · intro h
    funext a
    have : (a : k) ∈ subsetOf B f := by rw [h]; exact a.2
    exact (mem_subsetOf B).mp this
  · rintro rfl
    refine Finset.Subset.antisymm (subsetOf_subset B _) fun a ha => ?_
    exact (mem_subsetOf B (a := ⟨a, ha⟩)).mpr rfl

/-- The even subsets: the kernel of the sum `𝔽₂^B → 𝔽₂`. -/
noncomputable def evenSubsets : Submodule (ZMod 2) (B → ZMod 2) :=
  LinearMap.ker (Fintype.linearCombination (ZMod 2) fun _ : B => (1 : ZMod 2))

theorem mem_evenSubsets (f : B → ZMod 2) : f ∈ evenSubsets B ↔ ∑ a, f a = 0 := by
  rw [evenSubsets, LinearMap.mem_ker, Fintype.linearCombination_apply]
  simp only [smul_eq_mul, mul_one]

theorem finrank_evenSubsets (hB : B.Nonempty) :
    Module.finrank (ZMod 2) (evenSubsets B) = B.card - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (Fintype.linearCombination (ZMod 2) fun _ : B => (1 : ZMod 2))
  have hsurj : LinearMap.range
      (Fintype.linearCombination (ZMod 2) fun _ : B => (1 : ZMod 2)) = ⊤ := by
    obtain ⟨a, ha⟩ := hB
    classical
    refine LinearMap.range_eq_top.mpr fun c => ⟨Pi.single ⟨a, ha⟩ c, ?_⟩
    rw [Fintype.linearCombination_apply_single, smul_eq_mul, mul_one]
  rw [hsurj, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_coe] at h
  rw [evenSubsets]
  exact Nat.eq_sub_of_add_eq' h

/-- For `|B|` even, the constant function `1` (the subset `B`) is an even subset. -/
theorem one_mem_evenSubsets (hB : Even B.card) : (1 : B → ZMod 2) ∈ evenSubsets B := by
  rw [mem_evenSubsets]
  have hcard : ((B.card : ℕ) : ZMod 2) = 0 := by
    obtain ⟨n, hn⟩ := hB
    rw [hn, ← two_mul, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  simpa [Finset.card_univ] using hcard

end SubsetOf

/-! ### The dimension count: even subsets of `ℬ` modulo `{∅, ℬ}` -/

section Count

open TauCeti GSArith.LinearAlgebra

variable {k : Type*} [Field k] (B : Finset k) [Fact B.Nonempty]

/-- The image of `f ∈ k(x)` in `k(x)(√F)` as a unit, for `f ≠ 0`. -/
noncomputable def branchUnit {f : RatFunc k} (hf : f ≠ 0) : (BranchExt B)ˣ :=
  Units.mk0 (algebraMap (RatFunc k) (BranchExt B) f) ((_root_.map_ne_zero _).mpr hf)

@[simp] theorem branchUnit_val {f : RatFunc k} (hf : f ≠ 0) :
    (branchUnit B hf : BranchExt B) = algebraMap (RatFunc k) (BranchExt B) f := rfl

/-- The class of `x - a` in the square-class group of `k(x)(√F)`. -/
noncomputable def branchClass (a : k) : SquareClassGroup (BranchExt B) :=
  squareClass (branchUnit B ((map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).mpr
    (X_sub_C_ne_zero a)))

/-- **The branch map** `f ↦ [∏_{a ∈ B, f a = 1}(x - a)]`, as a linear map from `𝔽₂^B` to the
square-class group of `k(x)(√F)`. -/
noncomputable def branchMap : (B → ZMod 2) →ₗ[ZMod 2] SquareClassGroup (BranchExt B) :=
  Fintype.linearCombination (ZMod 2) fun a : B => branchClass B a

theorem branchMap_apply (f : B → ZMod 2) :
    branchMap B f = squareClass (branchUnit B ((map_ne_zero_iff _
      (RatFunc.algebraMap_injective k)).mpr (linProd_ne_zero (subsetOf B f)))) := by
  classical
  rw [branchMap, Fintype.linearCombination_apply, sum_zmod_two_smul]
  simp only [branchClass]
  rw [← squareClass_prod]
  congr 1
  apply Units.ext
  rw [Units.coe_prod]
  simp only [branchUnit_val]
  rw [← map_prod, ← map_prod]
  congr 2
  rw [subsetOf, linProd, Finset.prod_map]
  rfl

variable [NeZero (2 : k)]

/-- `ker (branchMap B) = {0, 1}`: the only relations are `∅` and `B`. -/
theorem branchMap_eq_zero_iff (f : B → ZMod 2) : branchMap B f = 0 ↔ f = 0 ∨ f = 1 := by
  rw [branchMap_apply, squareClass_eq_zero_iff, ← isSquare_units_val_iff, branchUnit_val,
    isSquare_branchExt_linProd_iff (subsetOf_subset B f), subsetOf_eq_empty_iff,
    subsetOf_eq_iff]

theorem ker_branchMap :
    LinearMap.ker (branchMap B) = Submodule.span (ZMod 2) {(1 : B → ZMod 2)} := by
  ext f
  rw [LinearMap.mem_ker, branchMap_eq_zero_iff, Submodule.mem_span_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨0, zero_smul _ _⟩
    · exact ⟨1, one_smul _ _⟩
  · rintro ⟨c, rfl⟩
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · left; exact zero_smul _ _
    · right; exact one_smul _ _

theorem finrank_ker_branchMap : Module.finrank (ZMod 2) (LinearMap.ker (branchMap B)) = 1 := by
  rw [ker_branchMap]
  refine finrank_span_singleton ?_
  intro h
  obtain ⟨a, ha⟩ := (Fact.out : B.Nonempty)
  have := congrFun h ⟨a, ha⟩
  simp at this

/-- **The image of all subsets has dimension `|B| - 1`.** -/
theorem finrank_range_branchMap :
    Module.finrank (ZMod 2) (LinearMap.range (branchMap B)) = B.card - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (branchMap B)
  rw [finrank_ker_branchMap, Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at h
  omega

/-- For `|B|` even, `{0, 1} ⊆ evenSubsets B`. -/
theorem ker_branchMap_le_evenSubsets (hB : Even B.card) :
    LinearMap.ker (branchMap B) ≤ evenSubsets B := by
  rw [ker_branchMap, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  exact one_mem_evenSubsets B hB

/-- **Proposition 2.16, the count.**  For `|B| = 2g + 2`, the classes of the even subsets of
`B` span a subspace of dimension `2g` of the square-class group of `k(x)(√F)`. -/
@[gs_public]
theorem finrank_map_evenSubsets_branchMap (hB : Even B.card) :
    Module.finrank (ZMod 2) ((evenSubsets B).map (branchMap B)) = B.card - 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker ((branchMap B).domRestrict (evenSubsets B))
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    (Submodule.comapSubtypeEquivOfLe (ker_branchMap_le_evenSubsets B hB)).finrank_eq,
    finrank_ker_branchMap, finrank_evenSubsets B (Fact.out : B.Nonempty)] at h
  have hcard : 1 ≤ B.card := Finset.card_pos.mpr (Fact.out : B.Nonempty)
  omega

end Count

end GSArith.Arithmetic

end
