/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Profinite.Lifting
public import GSArith.GroupTheory.InflationKernel
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Basic.Real.Basic

/-!
# Successive central quotients (Proposition 2.34)

The engine of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich for arithmetic surfaces*.
Let `Γ` be a topological group (in the paper, the profinite group `Π`), `Δ ≤ Γ` a subgroup,
and suppose `H²(Γ, 𝔽₂)` is finite-dimensional of dimension `< g²/4`.  Starting from a finite
quotient `q₀ : Γ ↠ H₀` with `|H₀| = 2^g`, `d(H₀) = g` and `q₀(Δ) = H₀`, the Golod–Shafarevich
inequality (Theorem 2.33) and the lifting lemma produce compatible finite quotients
`qₙ : Γ ↠ Hₙ` with

  `|Hₙ| = 2^(g+n)`,   `d(Hₙ) = g`,   `qₙ(Δ) = Hₙ`,

each `Hₙ₊₁ → Hₙ` a nonsplit central extension by `𝔽₂`.

The induction step: since `d(Hₙ) = g`, Theorem 2.33 gives `dim H²(Hₙ, 𝔽₂) > g²/4 > dim H²(Γ, 𝔽₂)`,
so inflation along `qₙ` kills a nonzero class `θₙ` (`exists_ne_zero_infl_eq_zero`); represent
`θₙ` by a normalized cocycle `c` and lift `qₙ` to the central extension `E_c`
(`CentralExt.exists_lift_iff`); the extension is nonsplit because `θₙ ≠ 0`
(`CentralExt.splits_iff`), so Proposition 2.32 makes the lift surjective, keeps `Δ` surjective,
doubles the order and preserves the generator rank.

Theorem 2.33 enters as the explicit hypothesis `GolodShafarevichHypothesis`, to be discharged
in `GSArith.GroupTheory.GolodShafarevich.Inequality`.

## Main definitions and results

* `GSArith.Profinite.Level Γ`: a finite discrete quotient `q : Γ ↠ H`.
* `GSArith.Profinite.GolodShafarevichHypothesis`: the statement of Theorem 2.33.
* `GSArith.Profinite.exists_next_level`: the induction step.
* `GSArith.Profinite.exists_tower`: Proposition 2.34.
-/

@[expose] public section

universe u v

namespace GSArith.Profinite

open TauCeti.ContCohomology GSArith.GroupTheory

attribute [local instance] trivialDistribMulAction trivialContinuousSMul

/-! ### The Golod–Shafarevich hypothesis -/

/-- **Theorem 2.33** (the Golod–Shafarevich inequality), as a hypothesis: for every nontrivial
finite `2`-group `H` (with its discrete topology), `dim_{𝔽₂} H²(H, 𝔽₂) > d(H)²/4`. -/
def GolodShafarevichHypothesis : Prop :=
  ∀ (H : Type u) [Group H] [Finite H] [TopologicalSpace H] [DiscreteTopology H]
    [ContinuousMul H], Nontrivial H → IsPGroup 2 H →
      (genRank H : ℝ) ^ 2 / 4 < Module.finrank (ZMod 2) (H2 H (ZMod 2))

/-! ### Finite quotients of `Γ` -/

variable (Γ : Type v) [Group Γ] [TopologicalSpace Γ] [ContinuousMul Γ]

/-- A finite discrete quotient of `Γ`: a finite group `H` with a continuous surjection
`q : Γ →ₜ* H`. -/
structure Level where
  /-- The finite quotient group. -/
  H : Type u
  [group : Group H]
  [finite : Finite H]
  [top : TopologicalSpace H]
  [discrete : DiscreteTopology H]
  [continuousMul : ContinuousMul H]
  /-- The quotient map. -/
  q : Γ →ₜ* H
  surjective : Function.Surjective q

attribute [instance] Level.group Level.finite Level.top Level.discrete Level.continuousMul

variable {Γ}

/-- The generator rank of a trivial group is `0`. -/
theorem genRank_eq_zero_of_subsingleton (H : Type*) [Group H] [Subsingleton H] :
    genRank H = 0 := by
  have : Subsingleton (Additive H →+ ZMod 2) :=
    ⟨fun f g => AddMonoidHom.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact Module.finrank_zero_of_subsingleton

theorem nontrivial_of_genRank_pos (H : Type*) [Group H] (h : 0 < genRank H) : Nontrivial H := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  rw [genRank_eq_zero_of_subsingleton H] at h
  exact lt_irrefl _ h

/-! ### The induction step -/

/-- **The induction step of Proposition 2.34.**  Given a level `L` with `|L.H| = 2^k`,
`d(L.H) = g ≥ 1` and `q(Δ) = L.H`, there is a level `L'` and a nonsplit central extension
`ρ : L'.H → L.H` by `𝔽₂` compatible with the quotient maps, with `q'(Δ) = L'.H`,
`|L'.H| = 2 |L.H|` and `d(L'.H) = g`. -/
theorem exists_next_level (hGS : GolodShafarevichHypothesis.{u})
    [Module.Finite (ZMod 2) (H2 Γ (ZMod 2))] {g : ℕ} (hg : 1 ≤ g)
    (hfin : (Module.finrank (ZMod 2) (H2 Γ (ZMod 2)) : ℝ) < (g : ℝ) ^ 2 / 4)
    (Δ : Subgroup Γ) (L : Level.{u} Γ) {k : ℕ} (hcard : Nat.card L.H = 2 ^ k)
    (hrank : genRank L.H = g) (hΔ : Δ.map L.q.toMonoidHom = ⊤) :
    ∃ (L' : Level.{u} Γ) (ρ : L'.H →* L.H),
      ρ.comp L'.q.toMonoidHom = L.q.toMonoidHom ∧ IsCentralExtensionByTwo ρ ∧ ¬ Splits ρ ∧
        Δ.map L'.q.toMonoidHom = ⊤ ∧ Nat.card L'.H = 2 * Nat.card L.H ∧ genRank L'.H = g := by
  -- Golod–Shafarevich at `L.H`
  have hnt : Nontrivial L.H := nontrivial_of_genRank_pos L.H (by omega)
  have hp : IsPGroup 2 L.H := IsPGroup.of_card hcard
  have hGSH := hGS L.H hnt hp
  rw [hrank] at hGSH
  have hdim : Module.finrank (ZMod 2) (H2 Γ (ZMod 2)) <
      Module.finrank (ZMod 2) (H2 L.H (ZMod 2)) := by
    exact_mod_cast hfin.trans hGSH
  -- a nonzero class killed by inflation, and a normalized cocycle representing it
  obtain ⟨θ, hθ, hinfl⟩ := exists_ne_zero_infl_eq_zero L.q hdim
  obtain ⟨c, hc⟩ := NormalizedCocycle.exists_cls_eq θ
  -- the lift
  obtain ⟨q', hq'⟩ := (CentralExt.exists_lift_iff L.q c).mpr (by rw [hc]; exact hinfl)
  have hcomp : (CentralExt.proj c).comp q'.toMonoidHom = L.q.toMonoidHom :=
    MonoidHom.ext fun γ => DFunLike.congr_fun hq' γ
  -- the extension is central by `𝔽₂` and nonsplit
  have hρ : IsCentralExtensionByTwo (CentralExt.proj c) :=
    CentralExt.isCentralExtensionByTwo c (Nat.card_zmod 2)
  have hns : ¬ Splits (CentralExt.proj c) := by
    rw [CentralExt.splits_iff, hc]; exact hθ
  -- surjectivity of the lift, from Proposition 2.32 (i)
  have hsurj : Function.Surjective q' := by
    change Function.Surjective q'.toMonoidHom
    rw [← MonoidHom.range_eq_top]
    apply hρ.eq_top_of_map_eq_top hns
    rw [eq_top_iff]
    intro h _
    obtain ⟨γ, rfl⟩ := L.surjective h
    exact Subgroup.mem_map.mpr ⟨q' γ, ⟨γ, rfl⟩, DFunLike.congr_fun hq' γ⟩
  -- `Δ` still surjects, from Proposition 2.32 (i)
  have hΔ' : Δ.map q'.toMonoidHom = ⊤ := by
    apply hρ.eq_top_of_map_eq_top hns
    rw [Subgroup.map_map, hcomp, hΔ]
  refine ⟨⟨CentralExt c, q', hsurj⟩, CentralExt.proj c, hcomp, hρ, hns, hΔ', ?_, ?_⟩
  · rw [CentralExt.card_eq, Nat.card_zmod]
  · rw [hρ.genRank_eq hns, hrank]

/-! ### The tower -/

/-- A level of the tower together with its invariants. -/
structure GoodLevel (Δ : Subgroup Γ) (g n : ℕ) extends Level.{u} Γ where
  card : Nat.card H = 2 ^ (g + n)
  rank : genRank H = g
  delta : Δ.map q.toMonoidHom = ⊤

/-- The successor of a good level, packaged with the connecting nonsplit central extension. -/
noncomputable def GoodLevel.next (hGS : GolodShafarevichHypothesis.{u})
    [Module.Finite (ZMod 2) (H2 Γ (ZMod 2))] {g : ℕ} (hg : 1 ≤ g)
    (hfin : (Module.finrank (ZMod 2) (H2 Γ (ZMod 2)) : ℝ) < (g : ℝ) ^ 2 / 4)
    {Δ : Subgroup Γ} {n : ℕ} (L : GoodLevel.{u} Δ g n) :
    { L' : GoodLevel.{u} Δ g (n + 1) //
      ∃ ρ : L'.H →* L.H, ρ.comp L'.q.toMonoidHom = L.q.toMonoidHom ∧
        IsCentralExtensionByTwo ρ ∧ ¬ Splits ρ } :=
  let e := exists_next_level hGS hg hfin Δ L.toLevel L.card L.rank L.delta
  ⟨{ e.choose with
      card := by
        rw [e.choose_spec.choose_spec.2.2.2.2.1, L.card]; ring
      rank := e.choose_spec.choose_spec.2.2.2.2.2
      delta := e.choose_spec.choose_spec.2.2.2.1 },
    e.choose_spec.choose, e.choose_spec.choose_spec.1, e.choose_spec.choose_spec.2.1,
    e.choose_spec.choose_spec.2.2.1⟩

/-- The tower of good levels, by recursion. -/
noncomputable def GoodLevel.tower (hGS : GolodShafarevichHypothesis.{u})
    [Module.Finite (ZMod 2) (H2 Γ (ZMod 2))] {g : ℕ} (hg : 1 ≤ g)
    (hfin : (Module.finrank (ZMod 2) (H2 Γ (ZMod 2)) : ℝ) < (g : ℝ) ^ 2 / 4)
    {Δ : Subgroup Γ} (L₀ : GoodLevel.{u} Δ g 0) : ∀ n, GoodLevel.{u} Δ g n
  | 0 => L₀
  | n + 1 => (GoodLevel.next hGS hg hfin (GoodLevel.tower hGS hg hfin L₀ n)).1

/-- **Proposition 2.34.**  Let `H²(Γ, 𝔽₂)` be finite-dimensional of dimension `< g²/4`, and let
`q₀ : Γ ↠ H₀` be a finite quotient with `|H₀| = 2^g`, `d(H₀) = g` and `q₀(Δ) = H₀`.  Then
there are compatible finite quotients `qₙ : Γ ↠ Hₙ` with `H₀` the given one, each
`Hₙ₊₁ → Hₙ` a nonsplit central extension by `𝔽₂`, and `|Hₙ| = 2^(g+n)`, `d(Hₙ) = g`,
`qₙ(Δ) = Hₙ` for every `n`. -/
@[gs_public]
theorem exists_tower (hGS : GolodShafarevichHypothesis.{u})
    [Module.Finite (ZMod 2) (H2 Γ (ZMod 2))] {g : ℕ} (hg : 1 ≤ g)
    (hfin : (Module.finrank (ZMod 2) (H2 Γ (ZMod 2)) : ℝ) < (g : ℝ) ^ 2 / 4)
    (Δ : Subgroup Γ) (L₀ : Level.{u} Γ) (hcard₀ : Nat.card L₀.H = 2 ^ g)
    (hrank₀ : genRank L₀.H = g) (hΔ₀ : Δ.map L₀.q.toMonoidHom = ⊤) :
    ∃ T : ℕ → Level.{u} Γ, T 0 = L₀ ∧
      ∃ ρ : ∀ n, (T (n + 1)).H →* (T n).H,
        (∀ n, (ρ n).comp (T (n + 1)).q.toMonoidHom = (T n).q.toMonoidHom) ∧
        (∀ n, IsCentralExtensionByTwo (ρ n)) ∧ (∀ n, ¬ Splits (ρ n)) ∧
        (∀ n, Nat.card (T n).H = 2 ^ (g + n)) ∧ (∀ n, genRank (T n).H = g) ∧
        (∀ n, Δ.map (T n).q.toMonoidHom = ⊤) := by
  let G₀ : GoodLevel.{u} Δ g 0 := ⟨L₀, by simpa using hcard₀, hrank₀, hΔ₀⟩
  let T := GoodLevel.tower hGS hg hfin G₀
  refine ⟨fun n => (T n).toLevel, rfl, fun n => (GoodLevel.next hGS hg hfin (T n)).2.choose,
    fun n => (GoodLevel.next hGS hg hfin (T n)).2.choose_spec.1,
    fun n => (GoodLevel.next hGS hg hfin (T n)).2.choose_spec.2.1,
    fun n => (GoodLevel.next hGS hg hfin (T n)).2.choose_spec.2.2,
    fun n => (T n).card, fun n => (T n).rank, fun n => (T n).delta⟩

end GSArith.Profinite

end
