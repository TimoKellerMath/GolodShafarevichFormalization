/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Construction.Tower
public import GSArith.Oracle.Conductor

/-!
# Main theorems

Theorems 1.1 and 1.2 and Corollaries 3.19–3.21 of Dérickx–Gillibert–Keller–Pagano,
*Golod–Shafarevich for arithmetic surfaces*, as consequences of Theorem 3.18
(`GSArith.Construction.theorem_3_18`).

All statements are relative to

* `GolodShafarevichHypothesis` — Theorem 2.33, the Golod–Shafarevich inequality, deliberately
  left as a named hypothesis (LEAN-PLAN.md, M3), and
* the class `GSArith.Oracle.PaperConstruction` — the geometric construction of Sections 3.1–3.5
  and the Stacks-Project inputs, listed in `LEDGER.md`.

Following LEAN-PLAN.md §3.3, "`π₁` is infinite" is stated as the tower itself: connected finite
étale Galois covers of every degree `2ⁿ` with a completely split section.  Curves over `ℚ`
(Theorem 1.2, Corollaries 3.20 and 3.21) appear through their regular models: the generic fibre
`Cₙ` of `Sₙ` has the genus `gen n`, and its rational points are the sections of `Sₙ → Spec ℤ`
(Proposition 2.3), of which `2^(g+n)` are exhibited.
-/

@[expose] public section

namespace GSArith

open GSArith.Oracle GSArith.Construction GSArith.Profinite AlgebraicGeometry CategoryTheory

variable [PaperConstruction]

/-- **Theorem 1.1.**  There are a regular projective arithmetic surface `S → Spec ℤ`, a section
`s`, and a tower `⋯ → Sₙ₊₁ → Sₙ → ⋯ → S₀ ≅ S` such that

* each `Sₙ → S` is a connected finite étale Galois cover of degree `2ⁿ` and each transition
  map has degree two;
* every `Sₙ` is a regular projective arithmetic surface;
* `s` splits completely at every level: `Sₙ ×_{S,s} Spec ℤ ≅ ∐_{2ⁿ} Spec ℤ`.

In particular the geometric étale fundamental group of `S` is infinite.  The base surface is
the one of level `m = 10529`, i.e. `g = 2^10529 - 1`. -/
@[gs_public]
theorem theorem_1_1 (hGS : GolodShafarevichHypothesis.{0}) :
    ∃ (S : Scheme) (f : S ⟶ SpecZ) (s : SpecZ ⟶ S),
      IsArithmeticSurface f ∧ IsRegularScheme S ∧ PaperConstruction.IsProjective f ∧
      s ≫ f = 𝟙 SpecZ ∧
      ∃ (Sn : ℕ → Scheme) (fn : ∀ n, Sn n ⟶ SpecZ) (π : ∀ n, Sn n ⟶ S)
        (tr : ∀ n, Sn (n + 1) ⟶ Sn n),
        (∀ n, IsArithmeticSurface (fn n) ∧ IsRegularScheme (Sn n) ∧
          PaperConstruction.IsProjective (fn n)) ∧
        (∀ n, π n ≫ f = fn n) ∧
        (∀ n, IsFinite (π n) ∧ Etale (π n) ∧ PaperConstruction.IsGaloisCover (π n) ∧
          ∀ x, (π n).finrank x = 2 ^ n) ∧
        (∀ n, tr n ≫ π n = π (n + 1)) ∧
        (∀ n, IsFinite (tr n) ∧ Etale (tr n) ∧ ∀ x, (tr n).finrank x = 2) ∧
        (∀ n, SplitsCompletely (π n) s (2 ^ n)) ∧ IsIso (π 0) := by
  obtain ⟨S, f, s, h1, h2, h3, h4, Sn, fn, π, tr, -, h5, h6, h7, h8, h9, h10, -, -, h13⟩ :=
    theorem_3_18 (PaperConstruction.setup 10529 (by norm_num)) hGS le_rfl
  exact ⟨S, f, s, h1, h2, h3, h4, Sn, fn, π, tr, h5, h6, h7, h8, h9, h10, h13⟩

/-- **Theorem 1.2** (regular-model form).  For every `m ≥ 10529` (the paper says `32768`) and
`g = 2^m - 1` there is a
tower of regular arithmetic surfaces `Sₙ → S` — the regular models of the curves `Cₙ → C` of
the paper — with `Sₙ → S` finite étale Galois of degree `2ⁿ`, transition maps of degree two,
generic fibres of genus `gₙ` with `gₙ - 1 = 2^(g+n) (g - 1)`, and at least `2^(g+n)` sections
`Spec ℤ → Sₙ` (the rational points of `Cₙ` above `P₊`, Proposition 2.3). -/
@[gs_public]
theorem theorem_1_2 (hGS : GolodShafarevichHypothesis.{0}) (m : ℕ) (hm : 10529 ≤ m) :
    ∃ (S : Scheme) (f : S ⟶ SpecZ) (Sn : ℕ → Scheme) (fn : ∀ n, Sn n ⟶ SpecZ)
      (π : ∀ n, Sn n ⟶ S) (tr : ∀ n, Sn (n + 1) ⟶ Sn n) (gen : ℕ → ℕ),
      IsArithmeticSurface f ∧ (∀ n, IsArithmeticSurface (fn n) ∧ IsRegularScheme (Sn n)) ∧
      (∀ n, π n ≫ f = fn n) ∧
      (∀ n, IsFinite (π n) ∧ Etale (π n) ∧ PaperConstruction.IsGaloisCover (π n) ∧
        ∀ x, (π n).finrank x = 2 ^ n) ∧
      (∀ n, tr n ≫ π n = π (n + 1)) ∧
      (∀ n, IsFinite (tr n) ∧ Etale (tr n) ∧ ∀ x, (tr n).finrank x = 2) ∧
      (∀ n, (gen n : ℤ) - 1 = 2 ^ (2 ^ m - 1 + n) * (((2 ^ m - 1 : ℕ) : ℤ) - 1)) ∧
      (∀ n, ∃ ι : Fin (2 ^ (2 ^ m - 1 + n)) → Sections (fn n), Function.Injective ι) := by
  obtain ⟨S, f, -, h1, -, -, -, Sn, fn, π, tr, gen, h5, h6, h7, h8, h9, -, h11, h12, -⟩ :=
    theorem_3_18 (PaperConstruction.setup m (by omega)) hGS hm
  exact ⟨S, f, Sn, fn, π, tr, gen, h1, fun n => ⟨(h5 n).1, (h5 n).2.1⟩, h6, h7, h8, h9, h11,
    h12⟩

/-- **Corollary 3.19** (Bost–Charles).  An integral regular projective flat arithmetic surface
over `Spec ℤ` with a section and infinite geometric étale fundamental group: the surface of
Theorem 1.1, the infinitude being witnessed by the tower. -/
theorem corollary_3_19 (hGS : GolodShafarevichHypothesis.{0}) :
    ∃ (S : Scheme) (f : S ⟶ SpecZ) (s : SpecZ ⟶ S),
      IsArithmeticSurface f ∧ IsRegularScheme S ∧ PaperConstruction.IsProjective f ∧
      s ≫ f = 𝟙 SpecZ ∧
      ∀ n : ℕ, ∃ (Y : Scheme) (π : Y ⟶ S), IsIntegral Y ∧ IsFinite π ∧ Etale π ∧
        PaperConstruction.IsGaloisCover π ∧ (∀ x, π.finrank x = 2 ^ n) ∧
        SplitsCompletely π s (2 ^ n) := by
  obtain ⟨S, f, s, h1, h2, h3, h4, Sn, fn, π, -, h5, -, h7, -, -, h10, -⟩ := theorem_1_1 hGS
  exact ⟨S, f, s, h1, h2, h3, h4, fun n => ⟨Sn n, π n, (h5 n).1.integral, (h7 n).1, (h7 n).2.1,
    (h7 n).2.2.1, (h7 n).2.2.2, h10 n⟩⟩

/-- **Corollaries 3.20 and 3.21** (Ihara; Frey–Kani–Völklein), regular-model form: the tower of
Theorem 1.2 has a section splitting completely at every level, so the generic fibre `C` with
the point `P₊` has completely split covers of every degree `2^(g+n)`, and the `ℚ`-rational
geometric fundamental group of `(C, P₊)` is infinite.  Formally this is the splitting
statement of Theorem 1.1 together with the genus and degree formulas of Theorem 1.2. -/
theorem corollary_3_20 (hGS : GolodShafarevichHypothesis.{0}) :
    ∃ (S : Scheme) (f : S ⟶ SpecZ) (s : SpecZ ⟶ S), IsArithmeticSurface f ∧ s ≫ f = 𝟙 SpecZ ∧
      ∀ n : ℕ, ∃ (Y : Scheme) (π : Y ⟶ S), IsIntegral Y ∧ IsFinite π ∧ Etale π ∧
        PaperConstruction.IsGaloisCover π ∧ (∀ x, π.finrank x = 2 ^ n) ∧
        SplitsCompletely π s (2 ^ n) := by
  obtain ⟨S, f, s, h1, -, -, h4, h⟩ := corollary_3_19 hGS
  exact ⟨S, f, s, h1, h4, h⟩

/-- **Corollary 3.24 / Theorem 1.3** (Venkatesh).  In the tower of Theorem 1.2 the genus tends to
infinity while the logarithmic conductor grows at most linearly in the genus:
`log 𝔑(Cₙ) ≤ A_m · g(Cₙ)` with `A_m > 0` independent of `n`. -/
@[gs_public]
theorem theorem_1_3 [ConductorOracle] (hGS : GolodShafarevichHypothesis.{0}) (m : ℕ)
    (hm : 10529 ≤ m) :
    ∃ (gen cond : ℕ → ℕ),
      (∀ n, (gen n : ℤ) - 1 = 2 ^ (2 ^ m - 1 + n) * (((2 ^ m - 1 : ℕ) : ℤ) - 1)) ∧
      Filter.Tendsto (fun n => (gen n : ℤ)) Filter.atTop Filter.atTop ∧
      ∃ A : ℝ, 0 < A ∧ ∀ n, Real.log (cond n) ≤ A * gen n := by
  set P := PaperConstruction.setup m (by omega) with hP
  set D := ConductorOracle.data m (by omega) with hD
  obtain ⟨T, hT0, ρ, hρ, -, -, hcard, -, hΔ⟩ := exists_level_tower P hGS hm
  have hgen : ∀ n, (P.genus (T n) (hΔ n) : ℤ) - 1 =
      2 ^ (2 ^ m - 1 + n) * (((2 ^ m - 1 : ℕ) : ℤ) - 1) := by
    intro n
    have hgen0 : (P.genus (T 0) (hΔ 0) : ℤ) - 1 =
        2 ^ (2 ^ m - 1) * (((2 ^ m - 1 : ℕ) : ℤ) - 1) :=
      transport_L₀ P (motive := fun L hL =>
        (P.genus L hL : ℤ) - 1 = 2 ^ (2 ^ m - 1) * (((2 ^ m - 1 : ℕ) : ℤ) - 1))
        hT0 (hΔ 0) P.genus_L₀
    have h := P.genus_formula (hΔ 0) (hΔ n) (compRho T ρ n) (compRho_comp_q T ρ hρ n)
    rw [degree_eq P hcard, hgen0] at h
    rw [h]
    push_cast
    ring
  refine ⟨fun n => P.genus (T n) (hΔ n), fun n => D.conductor (T n) (hΔ n), hgen, ?_, ?_⟩
  · have hg2 : 2 ≤ 2 ^ m - 1 := by
      have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Numeric.genus_tendsto_atTop (fun n => (P.genus (T n) (hΔ n) : ℤ)) (2 ^ m - 1) hg2 hgen
  · have hsum : (0 : ℝ) ≤ ∑ p ∈ D.bad, (1 + D.B p) * Real.log p :=
      Finset.sum_nonneg fun p hp =>
        mul_nonneg (by positivity) (Real.log_nonneg (by exact_mod_cast D.bad_pos p hp))
    refine ⟨2 * ∑ p ∈ D.bad, (1 + D.B p) * Real.log p + 1, by linarith, fun n => ?_⟩
    have hcond : ((D.conductor (T n) (hΔ n) : ℕ) : ℝ) =
        ∏ p ∈ D.bad, (p : ℝ) ^ D.exponent p (T n) (hΔ n) := by
      rw [D.conductor_eq]
      push_cast
      rfl
    rw [hcond]
    have hb := Numeric.conductor_sum_bound D.bad D.B (fun p => D.exponent p (T n) (hΔ n))
      (P.genus (T n) (hΔ n)) D.bad_pos
      (fun p hp => by exact_mod_cast D.exponent_le p hp (T n) (hΔ n))
    have hg0 : (0 : ℝ) ≤ P.genus (T n) (hΔ n) := by positivity
    nlinarith [hb, hsum, hg0]

end GSArith

end
