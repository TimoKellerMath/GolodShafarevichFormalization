/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Module.NatInt
public import GSArith.Ledger

/-!
# Fixed points of a Frobenius-semilinear map

The semilinear-algebra core of Proposition 2.20 of Dérickx–Gillibert–Keller–Pagano,
*Golod–Shafarevich for arithmetic surfaces*.  Let `k` be a field of characteristic `p`, `V` a
finite-dimensional `k`-vector space and `F : V → V` additive with `F (a • v) = a^p • F v`
(the map induced by Frobenius on coherent cohomology).  The fixed points of `F` form an
`𝔽_p`-vector space, and

  `dim_{𝔽_p} V^F ≤ dim_k V`.

The paper's proof: a shortest `k`-linear dependence among fixed vectors, normalized so that one
coefficient is `1`, is mapped by `F` to a dependence with the coefficients raised to the `p`-th
power; the difference is a shorter dependence, so by minimality all coefficients satisfy
`c^p = c`, i.e. lie in `𝔽_p` — contradicting `𝔽_p`-independence.  Here this is an induction on
the size of the support, and "`c^p = c` forces `c ∈ 𝔽_p`" is a root count for `X^p - X`.

In the paper `k` is algebraically closed and `F - 1` is surjective (Stacks `0A3L`); neither is
needed for the inequality.

## Main definitions and results

* `GSArith.LinearAlgebra.FrobSemilinear p k V`: additive maps with `F (a • v) = a^p • F v`.
* `GSArith.LinearAlgebra.FrobSemilinear.fixedPoints F`: the fixed points, an `𝔽_p`-vector space.
* `GSArith.LinearAlgebra.exists_zmod_of_pow_eq`: `c^p = c` iff `c` is in the prime field.
* `GSArith.LinearAlgebra.FrobSemilinear.linearIndependent_of_zmod`: `𝔽_p`-independent fixed
  vectors are `k`-independent.
* `GSArith.LinearAlgebra.FrobSemilinear.finrank_fixedPoints_le`: `dim_{𝔽_p} V^F ≤ dim_k V`.
-/

@[expose] public section

namespace GSArith.LinearAlgebra

open Polynomial Finset

variable {p : ℕ} {k : Type*} [Field k] [CharP k p]

/-- The prime field `𝔽_p → k`. -/
abbrev primeFieldHom (p : ℕ) (k : Type*) [Field k] [CharP k p] : ZMod p →+* k :=
  ZMod.castHom (dvd_refl p) k

/-- In a field of characteristic `p`, the solutions of `c^p = c` are exactly the elements of
the prime field: `X^p - X` has at most `p` roots and the prime field supplies `p` of them. -/
theorem exists_zmod_of_pow_eq [hp : Fact p.Prime] {c : k} (hc : c ^ p = c) :
    ∃ n : ZMod p, primeFieldHom p k n = c := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  set f : k[X] := X ^ p - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero k hp1
  have hdeg : f.natDegree = p := FiniteField.X_pow_card_sub_X_natDegree_eq k hp1
  have hroots : Multiset.card f.roots ≤ p := hdeg ▸ card_roots' f
  set S : Finset k := univ.image (primeFieldHom p k) with hS
  have hScard : S.card = p := by
    rw [hS, card_image_of_injective _ (primeFieldHom p k).injective, card_univ, ZMod.card]
  have hroot : ∀ x : k, x ^ p = x → x ∈ f.roots.toFinset := fun x hx => by
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, hf]
    simp [hx]
  have hSsub : S ⊆ f.roots.toFinset := fun x hx => by
    obtain ⟨n, -, rfl⟩ := mem_image.mp hx
    exact hroot _ (by rw [← map_pow, ZMod.pow_card])
  by_contra hcon
  push Not at hcon
  have hcS : c ∉ S := fun h => by
    obtain ⟨n, -, hn⟩ := mem_image.mp h
    exact hcon n hn
  have h1 : (insert c S).card ≤ f.roots.toFinset.card :=
    card_le_card (insert_subset (hroot c hc) hSsub)
  rw [card_insert_of_notMem hcS, hScard] at h1
  have h2 := Multiset.toFinset_card_le (m := f.roots)
  omega

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- An additive map `F : V → V` that is semilinear for Frobenius: `F (a • v) = a^p • F v`. -/
structure FrobSemilinear (p : ℕ) (k V : Type*) [Field k] [CharP k p] [AddCommGroup V]
    [Module k V] where
  /-- The underlying additive map. -/
  toAddMonoidHom : V →+ V
  /-- Frobenius-semilinearity. -/
  map_smul' : ∀ (a : k) (v : V), toAddMonoidHom (a • v) = a ^ p • toAddMonoidHom v

namespace FrobSemilinear

variable (F : FrobSemilinear p k V)

/-- The fixed points of `F`, as an additive subgroup of `V`. -/
def fixedPoints : AddSubgroup V where
  carrier := {v | F.toAddMonoidHom v = v}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add] at ha hb ⊢
    rw [ha, hb]
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq, map_neg] at ha ⊢
    rw [ha]

theorem mem_fixedPoints {v : V} : v ∈ F.fixedPoints ↔ F.toAddMonoidHom v = v := Iff.rfl

variable [hp : Fact p.Prime]

theorem smul_mem_fixedPoints (n : ZMod p) {v : V} (hv : v ∈ F.fixedPoints) :
    primeFieldHom p k n • v ∈ F.fixedPoints := by
  rw [mem_fixedPoints] at hv ⊢
  rw [F.map_smul', hv, ← map_pow, ZMod.pow_card]

/-- The prime field acts on the fixed points: `V^F` is an `𝔽_p`-vector space, with
`n • v = (n : k) • v`. -/
instance : Module (ZMod p) F.fixedPoints where
  smul n x := ⟨primeFieldHom p k n • x.1, F.smul_mem_fixedPoints n x.2⟩
  one_smul x := Subtype.ext (show primeFieldHom p k 1 • (x : V) = x by simp)
  mul_smul m n x := Subtype.ext (show primeFieldHom p k (m * n) • (x : V) =
    primeFieldHom p k m • (primeFieldHom p k n • (x : V)) by simp [mul_smul])
  smul_zero n := Subtype.ext (show primeFieldHom p k n • (0 : V) = 0 by simp)
  smul_add n x y := Subtype.ext (show primeFieldHom p k n • ((x : V) + y) =
    primeFieldHom p k n • (x : V) + primeFieldHom p k n • (y : V) by simp [smul_add])
  add_smul m n x := Subtype.ext (show primeFieldHom p k (m + n) • (x : V) =
    primeFieldHom p k m • (x : V) + primeFieldHom p k n • (x : V) by simp [add_smul])
  zero_smul x := Subtype.ext (show primeFieldHom p k 0 • (x : V) = 0 by simp)

@[simp] theorem coe_smul (n : ZMod p) (x : F.fixedPoints) :
    ((n • x : F.fixedPoints) : V) = primeFieldHom p k n • (x : V) := rfl

/-- `𝔽_p`-linearly independent fixed vectors are `k`-linearly independent. -/
theorem linearIndependent_of_zmod {ι : Type*} [Fintype ι] (v : ι → V)
    (hv : ∀ i, F.toAddMonoidHom (v i) = v i)
    (hind : ∀ n : ι → ZMod p, ∑ i, primeFieldHom p k (n i) • v i = 0 → ∀ i, n i = 0) :
    LinearIndependent k v := by
  classical
  rw [linearIndependent_iff']
  suffices h : ∀ N, ∀ c : ι → k, (univ.filter fun i => c i ≠ 0).card ≤ N →
      ∑ i, c i • v i = 0 → ∀ i, c i = 0 by
    intro s g hg i hi
    have := h _ (fun j => if j ∈ s then g j else 0) le_rfl (by
      rw [← hg]
      simp only [ite_smul, zero_smul]
      rw [Finset.sum_ite_mem, univ_inter]) i
    simpa [hi] using this
  intro N
  induction N with
  | zero =>
    intro c hc _ i
    by_contra hne
    have hmem : i ∈ univ.filter fun i => c i ≠ 0 := by simp [hne]
    have := card_pos.mpr ⟨i, hmem⟩
    omega
  | succ N ih =>
    intro c hcard hsum
    by_contra hne
    push Not at hne
    obtain ⟨i₀, hi₀⟩ := hne
    set c' : ι → k := fun i => (c i₀)⁻¹ * c i with hc'
    have hc'i₀ : c' i₀ = 1 := inv_mul_cancel₀ hi₀
    have hsum' : ∑ i, c' i • v i = 0 := by
      simp only [hc', mul_smul, ← smul_sum, hsum, smul_zero]
    have hF' : ∑ i, (c' i ^ p) • v i = 0 := by
      have h := congrArg F.toAddMonoidHom hsum'
      rw [map_sum, map_zero] at h
      simpa only [F.map_smul', hv] using h
    set d : ι → k := fun i => c' i ^ p - c' i with hd
    have hdsum : ∑ i, d i • v i = 0 := by
      simp only [hd, sub_smul, sum_sub_distrib, hF', hsum', sub_zero]
    have hdi₀ : d i₀ = 0 := by simp [hd, hc'i₀]
    have hdcard : (univ.filter fun i => d i ≠ 0).card ≤ N := by
      have hsub : (univ.filter fun i => d i ≠ 0) ⊆ (univ.filter fun i => c i ≠ 0).erase i₀ := by
        intro i hi
        simp only [mem_filter, mem_univ, true_and, mem_erase] at hi ⊢
        refine ⟨fun h => hi (by rw [h]; exact hdi₀), fun h => hi ?_⟩
        simp [hd, hc', h, hp.out.ne_zero]
      calc _ ≤ ((univ.filter fun i => c i ≠ 0).erase i₀).card := card_le_card hsub
        _ = (univ.filter fun i => c i ≠ 0).card - 1 := card_erase_of_mem (by simp [hi₀])
        _ ≤ N := by omega
    have hd0 := ih d hdcard hdsum
    have hpf : ∀ i, ∃ n : ZMod p, primeFieldHom p k n = c' i := fun i =>
      exists_zmod_of_pow_eq (sub_eq_zero.mp (hd0 i))
    choose n hn using hpf
    have hn0 : ∀ i, n i = 0 := hind n (by simpa only [hn] using hsum')
    have := hn i₀
    rw [hn0, map_zero, hc'i₀] at this
    exact zero_ne_one this

/-- **Proposition 2.20, the linear-algebra core.**  For a Frobenius-semilinear `F` on a
finite-dimensional `k`-vector space `V`, `dim_{𝔽_p} V^F ≤ dim_k V`. -/
@[gs_public]
theorem finrank_fixedPoints_le [FiniteDimensional k V] :
    Module.finrank (ZMod p) F.fixedPoints ≤ Module.finrank k V := by
  classical
  apply Module.finrank_le_of_rank_le
  apply rank_le
  intro s hs
  have hind : ∀ n : s → ZMod p,
      ∑ i, primeFieldHom p k (n i) • ((i : F.fixedPoints) : V) = 0 → ∀ i, n i = 0 := by
    intro n hn
    have hsum : ∑ i, n i • (i : F.fixedPoints) = 0 := by
      apply Subtype.ext
      rw [ZeroMemClass.coe_zero, ← hn]
      change F.fixedPoints.subtype (∑ i, n i • (i : F.fixedPoints)) = _
      rw [map_sum]
      rfl
    exact fun i => linearIndependent_iff'.mp hs univ n (by simpa using hsum) i (mem_univ i)
  have hk : LinearIndependent k (fun i : s => ((i : F.fixedPoints) : V)) :=
    F.linearIndependent_of_zmod _ (fun i => (i : F.fixedPoints).2) hind
  have := hk.fintype_card_le_finrank
  simpa [Fintype.card_coe] using this

end FrobSemilinear

end GSArith.LinearAlgebra

end
