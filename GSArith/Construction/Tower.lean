/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Oracle.Surfaces
public import GSArith.Construction.ObstructionBound

/-!
# The infinite geometric tower (Theorem 3.18)

The assembly of Theorem 3.18 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for
arithmetic surfaces*, from

* Proposition 3.17 (`GSArith.Oracle.PaperSetup.finrank_H2_lt_quarter_sq`, from
  `ObstructionSituation.hG2_lt_quarter_sq` and the comparison of Proposition 2.29): for
  `m ≥ 10529`, `dim H²_cts(Π_m, 𝔽₂) < g²/4`;
* Proposition 2.34 (`GSArith.Profinite.exists_tower`): the tower of finite quotients
  `qₙ : Π_m ↠ Hₙ`, `|Hₙ| = 2^(g+n)`, `d(Hₙ) = g`, `qₙ(Δ) = Hₙ`, with nonsplit central steps;
* the geometric interface `GSArith.Oracle.PaperSetup` realizing finite quotients as regular
  projective arithmetic surfaces with sections (Propositions 3.2, 3.4, 2.4, 2.5, 2.7, 2.17).

The Golod–Shafarevich inequality enters as the hypothesis `GolodShafarevichHypothesis`.
-/

@[expose] public section

namespace GSArith.Construction

open GSArith.Oracle GSArith.Profinite GSArith.GroupTheory AlgebraicGeometry CategoryTheory
  Limits TauCeti.ContCohomology

attribute [local instance] trivialDistribMulAction trivialContinuousSMul

/-! ### Composite connecting maps of a tower of levels -/

section Composite

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  (T : ℕ → Level Γ) (ρ : ∀ n, (T (n + 1)).H →* (T n).H)

/-- The composite `Hₙ → H₀` of the connecting maps. -/
def compRho : ∀ n, (T n).H →* (T 0).H
  | 0 => MonoidHom.id _
  | n + 1 => (compRho n).comp (ρ n)

@[simp] theorem compRho_zero : compRho T ρ 0 = MonoidHom.id _ := rfl

theorem compRho_succ (n : ℕ) : compRho T ρ (n + 1) = (compRho T ρ n).comp (ρ n) := rfl

theorem compRho_comp_q (hρ : ∀ n, (ρ n).comp (T (n + 1)).q.toMonoidHom = (T n).q.toMonoidHom) :
    ∀ n, (compRho T ρ n).comp (T n).q.toMonoidHom = (T 0).q.toMonoidHom
  | 0 => MonoidHom.id_comp _
  | n + 1 => by rw [compRho_succ, MonoidHom.comp_assoc, hρ n, compRho_comp_q hρ n]

end Composite

/-! ### The tower of finite quotients -/

variable {IsProj : ∀ {S : Scheme}, (S ⟶ SpecZ) → Prop} {IsGal : ∀ {X Y : Scheme}, (X ⟶ Y) → Prop}
  {m : ℕ} (P : PaperSetup IsProj IsGal m)

/-- `g = 2^m - 1 ≥ 1` for `m ≥ 1`. -/
theorem one_le_g {m : ℕ} (hm : 1 ≤ m) : 1 ≤ 2 ^ m - 1 := by
  have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

/-- Propositions 3.17 and 2.34 applied to the construction: the tower of finite quotients of
`Π_m`. -/
theorem exists_level_tower (hGS : GolodShafarevichHypothesis.{0}) (hm : 10529 ≤ m) :
    ∃ T : ℕ → Level P.Γ, T 0 = P.L₀ ∧
      ∃ ρ : ∀ n, (T (n + 1)).H →* (T n).H,
        (∀ n, (ρ n).comp (T (n + 1)).q.toMonoidHom = (T n).q.toMonoidHom) ∧
        (∀ n, IsCentralExtensionByTwo (ρ n)) ∧ (∀ n, ¬ Splits (ρ n)) ∧
        (∀ n, Nat.card (T n).H = 2 ^ (2 ^ m - 1 + n)) ∧ (∀ n, genRank (T n).H = 2 ^ m - 1) ∧
        (∀ n, P.Δ.map (T n).q.toMonoidHom = ⊤) := by
  exact exists_tower hGS (one_le_g (by omega)) (P.finrank_H2_lt_quarter_sq hm) P.Δ P.L₀ P.card_L₀
    P.rank_L₀ P.delta_L₀

/-- The degree of `Sₙ → S₀` is `2^n`. -/
theorem degree_eq {T : ℕ → Level P.Γ}
    (hcard : ∀ n, Nat.card (T n).H = 2 ^ (2 ^ m - 1 + n)) (n : ℕ) :
    Nat.card (T n).H / Nat.card (T 0).H = 2 ^ n := by
  rw [hcard, hcard, add_zero, Nat.pow_div (by omega) (by norm_num)]
  congr 1
  omega

/-- The degree of `Sₙ₊₁ → Sₙ` is `2`. -/
theorem degree_succ_eq {T : ℕ → Level P.Γ}
    (hcard : ∀ n, Nat.card (T n).H = 2 ^ (2 ^ m - 1 + n)) (n : ℕ) :
    Nat.card (T (n + 1)).H / Nat.card (T n).H = 2 := by
  rw [hcard, hcard, Nat.pow_div (by omega) (by norm_num)]
  have h : 2 ^ m - 1 + (n + 1) - (2 ^ m - 1 + n) = 1 := by omega
  rw [h, pow_one]

/-! ### Lifting sections along the tower -/

/-- If `Fin a` injects into the sections of `S` and every section has `d` lifts along
`π : Y ⟶ S`, then `Fin (a * d)` injects into the sections of `Y`. -/
theorem exists_injective_sections {Y S : Scheme} (π : Y ⟶ S) (f : S ⟶ SpecZ) (fY : Y ⟶ SpecZ)
    (hπ : π ≫ f = fY) {a d : ℕ} (ι : Fin a → Sections f) (hι : Function.Injective ι)
    (hlift : ∀ σ : Sections f, ∃ κ : Fin d → Lifts π σ.1, Function.Injective κ) :
    ∃ ι' : Fin (a * d) → Sections fY, Function.Injective ι' := by
  choose κ hκ using hlift
  let ι' : Fin a × Fin d → Sections fY := fun ij =>
    ⟨(κ (ι ij.1) ij.2).1, by rw [← hπ, ← Category.assoc, (κ _ _).2]; exact (ι _).2⟩
  have hι' : Function.Injective ι' := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h1 : (κ (ι i) j).1 = (κ (ι i') j').1 := congrArg Subtype.val h
    have hbase : (ι i).1 = (ι i').1 := by
      calc (ι i).1 = (κ (ι i) j).1 ≫ π := (κ _ _).2.symm
        _ = (κ (ι i') j').1 ≫ π := by rw [h1]
        _ = (ι i').1 := (κ _ _).2
    have hi : i = i' := hι (Subtype.ext hbase)
    subst hi
    have hj : j = j' := hκ (ι i) (Subtype.ext h1)
    rw [hj]
  exact ⟨ι' ∘ finProdFinEquiv.symm, hι'.comp finProdFinEquiv.symm.injective⟩

/-! ### Transport from `L₀` to the bottom of the tower -/

/-- Anything true of the distinguished level `L₀` is true of a level equal to it. -/
theorem transport_L₀
    {motive : (L : Level P.Γ) → P.Δ.map L.q.toMonoidHom = ⊤ → Prop}
    {T : ℕ → Level P.Γ} (hT0 : T 0 = P.L₀) (hΔ0 : P.Δ.map (T 0).q.toMonoidHom = ⊤)
    (h : motive P.L₀ P.delta_L₀) : motive (T 0) hΔ0 := by
  generalize hgen : T 0 = L' at hΔ0 ⊢
  rw [hT0] at hgen
  subst hgen
  exact h

/-! ### Theorem 3.18 -/

include P in
/-- **Theorem 3.18** (an infinite geometric tower over a surface with a section), relative to
the Golod–Shafarevich inequality and the geometric interface.  For `m ≥ 10529` (the paper
says `32768`) and
`g = 2^m - 1` there are a regular projective arithmetic surface `S → Spec ℤ` with a section
`s`, and a tower `Sₙ` of regular projective arithmetic surfaces with

* `πₙ : Sₙ → S` finite étale Galois of degree `2ⁿ`, with `π₀` an isomorphism,
* transition maps `Sₙ₊₁ → Sₙ` finite étale of degree two, compatible with the `πₙ`,
* `s` splitting completely in every `Sₙ`: `Sₙ ×_{S,s} Spec ℤ ≅ ∐_{2ⁿ} Spec ℤ`,
* generic fibres of genus `gₙ` with `gₙ - 1 = 2^(g+n) (g - 1)`,
* at least `2^(g+n)` sections `Spec ℤ → Sₙ` (the rational points of `Cₙ` above `P₊`). -/
theorem theorem_3_18 (hGS : GolodShafarevichHypothesis.{0}) (hm : 10529 ≤ m) :
    ∃ (S : Scheme) (f : S ⟶ SpecZ) (s : SpecZ ⟶ S),
      IsArithmeticSurface f ∧ IsRegularScheme S ∧ IsProj f ∧ s ≫ f = 𝟙 SpecZ ∧
      ∃ (Sn : ℕ → Scheme) (fn : ∀ n, Sn n ⟶ SpecZ) (π : ∀ n, Sn n ⟶ S)
        (tr : ∀ n, Sn (n + 1) ⟶ Sn n) (gen : ℕ → ℕ),
        (∀ n, IsArithmeticSurface (fn n) ∧ IsRegularScheme (Sn n) ∧ IsProj (fn n)) ∧
        (∀ n, π n ≫ f = fn n) ∧
        (∀ n, IsFinite (π n) ∧ Etale (π n) ∧ IsGal (π n) ∧ ∀ x, (π n).finrank x = 2 ^ n) ∧
        (∀ n, tr n ≫ π n = π (n + 1)) ∧
        (∀ n, IsFinite (tr n) ∧ Etale (tr n) ∧ ∀ x, (tr n).finrank x = 2) ∧
        (∀ n, SplitsCompletely (π n) s (2 ^ n)) ∧
        (∀ n, (gen n : ℤ) - 1 = 2 ^ (2 ^ m - 1 + n) * (((2 ^ m - 1 : ℕ) : ℤ) - 1)) ∧
        (∀ n, ∃ ι : Fin (2 ^ (2 ^ m - 1 + n)) → Sections (fn n), Function.Injective ι) ∧
        IsIso (π 0) := by
  obtain ⟨T, hT0, ρ, hρ, -, -, hcard, -, hΔ⟩ := exists_level_tower P hGS hm
  refine ⟨P.real (T 0) (hΔ 0), P.realf (T 0) (hΔ 0), P.reals (T 0) (hΔ 0),
    P.real_surface _ _, P.real_regular _ _, P.real_projective _ _, P.reals_realf _ _,
    fun n => P.real (T n) (hΔ n), fun n => P.realf (T n) (hΔ n),
    fun n => P.realHom (hΔ 0) (hΔ n) (compRho T ρ n) (compRho_comp_q T ρ hρ n),
    fun n => P.realHom (hΔ n) (hΔ (n + 1)) (ρ n) (hρ n),
    fun n => P.genus (T n) (hΔ n), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun n => ⟨P.real_surface _ _, P.real_regular _ _, P.real_projective _ _⟩
  · exact fun n => P.realHom_realf _ _ _ _
  · intro n
    refine ⟨P.realHom_finite _ _ _ _, P.realHom_etale _ _ _ _, P.realHom_galois _ _ _ _,
      fun x => ?_⟩
    rw [P.realHom_finrank, degree_eq P hcard]
  · intro n
    exact (P.realHom_comp (hΔ 0) (hΔ n) (hΔ (n + 1)) (compRho T ρ n) (ρ n)
      (compRho_comp_q T ρ hρ n) (hρ n)).symm
  · intro n
    refine ⟨P.realHom_finite _ _ _ _, P.realHom_etale _ _ _ _, fun x => ?_⟩
    rw [P.realHom_finrank, degree_succ_eq P hcard]
  · intro n
    have := P.realHom_split (hΔ 0) (hΔ n) (compRho T ρ n) (compRho_comp_q T ρ hρ n)
    rwa [degree_eq P hcard] at this
  · intro n
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
  · intro n
    obtain ⟨ι, hι⟩ := transport_L₀ P (motive := fun L hL =>
        ∃ ι : Fin (2 ^ (2 ^ m - 1)) → Sections (P.realf L hL), Function.Injective ι)
      hT0 (hΔ 0) P.sections_L₀
    have := exists_injective_sections
      (P.realHom (hΔ 0) (hΔ n) (compRho T ρ n) (compRho_comp_q T ρ hρ n))
      (P.realf (T 0) (hΔ 0)) (P.realf (T n) (hΔ n)) (P.realHom_realf _ _ _ _) ι hι
      (fun σ => P.sections_lift (hΔ 0) (hΔ n) _ _ σ)
    rwa [degree_eq P hcard, ← pow_add] at this
  · have h0 : P.realHom (hΔ 0) (hΔ 0) (compRho T ρ 0) (compRho_comp_q T ρ hρ 0) =
        𝟙 (P.real (T 0) (hΔ 0)) := P.realHom_id _ _
    change IsIso (P.realHom (hΔ 0) (hΔ 0) (compRho T ρ 0) (compRho_comp_q T ρ hρ 0))
    rw [h0]
    infer_instance

end GSArith.Construction

end
