/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.KrullDimension
public import GSArith.GroupTheory.SuccessiveQuotients
public import GSArith.Oracle.EtaleCohomology
public import GSArith.Oracle.Comparison
public import GSArith.Construction.ObstructionBound

/-!
# Interface: arithmetic surfaces and the models of Section 3

The scheme-theoretic vocabulary of Section 2.1 of Dérickx–Gillibert–Keller–Pagano,
*Golod–Shafarevich for arithmetic surfaces*, in Mathlib's language, and the geometric
interface consumed by Theorem 3.18.

## Vocabulary (Mathlib)

* `GSArith.Oracle.SpecZ` is `Spec ℤ`; a section of `f : S ⟶ Spec ℤ` is `s` with `s ≫ f = 𝟙`.
* `GSArith.Oracle.IsRegularScheme`: all local rings are regular local rings.
* `GSArith.Oracle.IsArithmeticSurface f`: integral, proper, flat over `Spec ℤ`, fibres of
  dimension one.  (The paper asks for *pure* dimension one; Krull dimension one of the fibre is
  the part expressible without an irreducible-components API and is all that is used.)
* complete splitting of a section `s` in a cover `π : Y ⟶ S` of degree `d`:
  `pullback π s ≅ ∐_{j < d} Spec ℤ`.

## The interface (Sections 3.1–3.6)

`GSArith.Oracle.PaperSetup m` bundles, for `g = 2^m - 1`, what Sections 3.1–3.5 construct
and what Theorem 3.18's proof invokes:

1. the profinite group `Π = Π_m` with the subgroup `Δ` (image of `π₁(C_ℚ̄)`), and the
   quotient `q₀ : Π ↠ G₀ ≅ 𝔽₂^g` with `q₀(Δ) = G₀` (Propositions 3.1, 3.4);
2. the obstruction situation of Proposition 3.17 and the comparison situation of
   Proposition 2.29, from which `dim H²_cts(Π, 𝔽₂) < g²/4` is *derived*
   (`PaperSetup.finrank_H2_lt_quarter_sq`), TauCeti's continuous cohomology being the
   `H²_cts`;
3. the geometric realization: to every finite quotient `q : Π ↠ H` with `q(Δ) = H` the regular
   projective arithmetic surface `S_H = 𝒯_H ×_{𝒯_m} S` with its section, to every compatible
   `ρ : H' → H` the finite étale map `S_{H'} → S_H` of degree `|H'|/|H|`, functorially, along
   which the section splits completely; and the genus of the generic fibre with the
   Riemann–Hurwitz formula (Propositions 3.2, 3.4, 2.4, 2.5, 2.7, 2.17, 2.3).

Two notions Mathlib lacks — projectivity over `Spec ℤ` (Stacks `01W7`) and Galois covers
(Stacks `0BN0`) — enter as opaque predicates carried by the class `PaperConstruction`; they
occur in the *statements* of the main theorems only through those predicates, which is
recorded for the audit (LEAN-PLAN.md P29).

Everything here is a hypothesis of the theorems that use it, never an axiom.
-/

@[expose] public section

namespace GSArith.Oracle

open AlgebraicGeometry CategoryTheory Limits GSArith.Profinite GSArith.GroupTheory
open TauCeti.ContCohomology

attribute [local instance] trivialDistribMulAction trivialContinuousSMul

/-! ### Vocabulary -/

/-- `Spec ℤ`. -/
noncomputable abbrev SpecZ : Scheme := Spec (CommRingCat.of ℤ)

/-- A scheme is regular if all its local rings are regular local rings. -/
def IsRegularScheme (X : Scheme) : Prop := ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)

/-- An arithmetic surface over `Spec ℤ`: integral, proper, flat, with fibres of dimension one. -/
structure IsArithmeticSurface {S : Scheme} (f : S ⟶ SpecZ) : Prop where
  integral : IsIntegral S
  proper : IsProper f
  flat : Flat f
  fibre_dim : ∀ y : SpecZ, topologicalKrullDim (f.fiber y) = 1

/-- The sections of `f : S ⟶ Spec ℤ`, i.e. `S(ℤ)`. -/
def Sections {S : Scheme} (f : S ⟶ SpecZ) : Type := { s : SpecZ ⟶ S // s ≫ f = 𝟙 SpecZ }

/-- The lifts of a section `σ` of the base along `π : Y ⟶ S`. -/
def Lifts {Y S : Scheme} (π : Y ⟶ S) (σ : SpecZ ⟶ S) : Type := { σ' : SpecZ ⟶ Y // σ' ≫ π = σ }

/-- A section splits completely in a cover `π` of degree `d`: the fibre product with the
section is `d` copies of `Spec ℤ`. -/
def SplitsCompletely {Y S : Scheme} (π : Y ⟶ S) (s : SpecZ ⟶ S) (d : ℕ) : Prop :=
  Nonempty (pullback π s ≅ ∐ fun _ : Fin d => SpecZ)

/-! ### The construction of Section 3 -/

/-- The data constructed in Sections 3.1–3.5 for a given `m ≥ 4`, with `g = 2^m - 1`, together
with the properties invoked in the proof of Theorem 3.18.  `IsProj` and `IsGal` are the opaque
predicates "projective over `Spec ℤ`" and "Galois cover". -/
structure PaperSetup (IsProj : ∀ {S : Scheme}, (S ⟶ SpecZ) → Prop)
    (IsGal : ∀ {X Y : Scheme}, (X ⟶ Y) → Prop) (m : ℕ) where
  /-- the Galois group `Π_m` of the compositum of admissible extensions (named `Γ`, since `Π`
  is reserved) -/
  Γ : Type
  [instGroup : Group Γ]
  [instTop : TopologicalSpace Γ]
  [instTopGroup : IsTopologicalGroup Γ]
  [instCompact : CompactSpace Γ]
  [instTotallyDisconnected : TotallyDisconnectedSpace Γ]
  /-- the image of `π₁^ét(C_ℚ̄)` in `Π_m` -/
  Δ : Subgroup Γ
  /-- the quotient `q₀ : Π ↠ G₀ = Gal(L/K)` -/
  L₀ : Level Γ
  -- OBLIGATION[paper:3.1][tier:C][crit:yes][prop:3.1] |G₀| = 2^g
  card_L₀ : Nat.card L₀.H = 2 ^ (2 ^ m - 1)
  -- OBLIGATION[paper:3.1][tier:C][crit:yes][prop:3.1] G₀ ≅ 𝔽₂^g has generator rank g
  rank_L₀ : genRank L₀.H = 2 ^ m - 1
  -- OBLIGATION[stacks:0BQ8][tier:C][crit:yes][prop:3.1] C₀ → C geometric: q₀(Δ) = G₀
  delta_L₀ : Δ.map L₀.q.toMonoidHom = ⊤
  /-- the cohomological situation of Proposition 3.17 -/
  obs : ObstructionSituation (2 ^ m - 1) m
  /-- the comparison situation of Proposition 2.29: `H²_G(T)` and the edge maps into it -/
  cmp : ComparisonSituation Γ (obs.hG 2)
  /-- the regular model of the admissible cover attached to a finite quotient (Props 3.2, 3.4) -/
  real : (L : Level Γ) → Δ.map L.q.toMonoidHom = ⊤ → Scheme
  /-- its structure map -/
  realf : ∀ (L : Level Γ) (hL : Δ.map L.q.toMonoidHom = ⊤), real L hL ⟶ SpecZ
  /-- its section extending `Q₊` (Prop 2.3) -/
  reals : ∀ (L : Level Γ) (hL : Δ.map L.q.toMonoidHom = ⊤), SpecZ ⟶ real L hL
  -- OBLIGATION[stacks:0BX5,0BX6][tier:C][crit:yes][prop:2.3] the rational point extends
  reals_realf : ∀ L hL, reals L hL ≫ realf L hL = 𝟙 SpecZ
  -- OBLIGATION[stacks:0BGP,025N,0567,0357][tier:C][crit:yes][prop:2.5] integral proper flat
  real_surface : ∀ L hL, IsArithmeticSurface (realf L hL)
  -- OBLIGATION[stacks:0BGP,025N][tier:C][crit:yes][prop:2.5] regular
  real_regular : ∀ L hL, IsRegularScheme (real L hL)
  -- OBLIGATION[stacks:01W7,0B44,0B3I][tier:C][crit:yes][prop:3.16] projective over ℤ
  real_projective : ∀ L hL, IsProj (realf L hL)
  /-- the map of models attached to a compatible map of quotients (Prop 3.4) -/
  realHom : ∀ {L L' : Level Γ} (hL : Δ.map L.q.toMonoidHom = ⊤) (hL' : Δ.map L'.q.toMonoidHom = ⊤)
    (ρ : L'.H →* L.H), ρ.comp L'.q.toMonoidHom = L.q.toMonoidHom → (real L' hL' ⟶ real L hL)
  -- OBLIGATION[paper:3.4][tier:C][crit:yes][prop:3.4] maps of models lie over Spec ℤ
  realHom_realf : ∀ {L L' : Level Γ} hL hL' ρ hρ,
    realHom (L := L) (L' := L') hL hL' ρ hρ ≫ realf L hL = realf L' hL'
  -- OBLIGATION[paper:3.4][tier:C][crit:yes][prop:3.4] functoriality: the identity
  realHom_id : ∀ L hL, realHom hL hL (MonoidHom.id L.H) (MonoidHom.id_comp _) = 𝟙 (real L hL)
  -- OBLIGATION[paper:3.4][tier:C][crit:yes][prop:3.4] functoriality: composition
  realHom_comp : ∀ {L L' L'' : Level Γ} (hL : Δ.map L.q.toMonoidHom = ⊤)
    (hL' : Δ.map L'.q.toMonoidHom = ⊤) (hL'' : Δ.map L''.q.toMonoidHom = ⊤)
    (ρ : L'.H →* L.H) (ρ' : L''.H →* L'.H)
    (hρ : ρ.comp L'.q.toMonoidHom = L.q.toMonoidHom)
    (hρ' : ρ'.comp L''.q.toMonoidHom = L'.q.toMonoidHom),
    realHom (L := L) (L' := L'') hL hL'' (ρ.comp ρ')
        (by rw [MonoidHom.comp_assoc, hρ', hρ]) =
      realHom hL' hL'' ρ' hρ' ≫ realHom hL hL' ρ hρ
  -- OBLIGATION[stacks:02GH,02GW][tier:C][crit:yes][prop:3.4] maps of models are finite
  realHom_finite : ∀ {L L' : Level Γ} hL hL' ρ hρ,
    IsFinite (realHom (L := L) (L' := L') hL hL' ρ hρ)
  -- OBLIGATION[stacks:02GH,02GW][tier:C][crit:yes][prop:3.4] maps of models are étale
  realHom_etale : ∀ {L L' : Level Γ} hL hL' ρ hρ, Etale (realHom (L := L) (L' := L') hL hL' ρ hρ)
  -- OBLIGATION[stacks:0BN0,0BQ8][tier:C][crit:yes][prop:3.4] maps of models are Galois
  realHom_galois : ∀ {L L' : Level Γ} hL hL' ρ hρ, IsGal (realHom (L := L) (L' := L') hL hL' ρ hρ)
  -- OBLIGATION[stacks:02GH][tier:C][crit:yes][prop:2.5] the degree is the index |H'|/|H|
  realHom_finrank : ∀ {L L' : Level Γ} hL hL' ρ hρ (x : real L hL),
    (realHom (L := L) (L' := L') hL hL' ρ hρ).finrank x = Nat.card L'.H / Nat.card L.H
  -- OBLIGATION[stacks:02GH][tier:C][crit:yes][prop:2.7] the section splits completely
  realHom_split : ∀ {L L' : Level Γ} hL hL' ρ hρ,
    SplitsCompletely (realHom (L := L) (L' := L') hL hL' ρ hρ) (reals L hL)
      (Nat.card L'.H / Nat.card L.H)
  -- OBLIGATION[stacks:02GH][tier:C][crit:yes][prop:2.7] every section has |H'|/|H| lifts
  sections_lift : ∀ {L L' : Level Γ} hL hL' ρ hρ (σ : Sections (realf L hL)),
    ∃ ι : Fin (Nat.card L'.H / Nat.card L.H) → Lifts (realHom (L := L) (L' := L') hL hL' ρ hρ) σ.1,
      Function.Injective ι
  -- OBLIGATION[paper:3.1][tier:C][crit:yes][prop:3.1] the 2^g rational points above P₊ extend to se
  sections_L₀ : ∃ ι : Fin (2 ^ (2 ^ m - 1)) → Sections (realf L₀ delta_L₀), Function.Injective ι
  /-- the genus of the generic fibre of `real L hL` -/
  genus : ∀ (L : Level Γ) (_hL : Δ.map L.q.toMonoidHom = ⊤), ℕ
  -- OBLIGATION[stacks:0C1B,0BXX][tier:C][crit:yes][prop:3.1] g(C₀) - 1 = 2^g (g - 1)
  genus_L₀ : (genus L₀ delta_L₀ : ℤ) - 1 = 2 ^ (2 ^ m - 1) * ((2 ^ m - 1 : ℕ) - 1 : ℤ)
  -- OBLIGATION[stacks:0C1A,0C1B][tier:C][crit:yes][prop:2.17] Riemann–Hurwitz for étale covers
  genus_formula : ∀ {L L' : Level Γ} hL hL' (ρ : L'.H →* L.H)
    (_hρ : ρ.comp L'.q.toMonoidHom = L.q.toMonoidHom),
    (genus L' hL' : ℤ) - 1 = (Nat.card L'.H / Nat.card L.H : ℕ) * ((genus L hL : ℤ) - 1)

attribute [instance] PaperSetup.instGroup PaperSetup.instTop PaperSetup.instTopGroup
  PaperSetup.instCompact PaperSetup.instTotallyDisconnected

namespace PaperSetup

variable {IsProj : ∀ {S : Scheme}, (S ⟶ SpecZ) → Prop} {IsGal : ∀ {X Y : Scheme}, (X ⟶ Y) → Prop}
  {m : ℕ} (P : PaperSetup IsProj IsGal m)

-- DISCHARGED[paper:3.17][tier:B][crit:yes][prop:3.17] H²_cts(Π_m,𝔽₂) is finite-dimensional
/-- `H²_cts(Π_m, 𝔽₂)` is finite-dimensional: `ComparisonSituation.finite_H2`. -/
instance finiteH2 : Module.Finite (ZMod 2) (H2 P.Γ (ZMod 2)) := P.cmp.finite_H2

-- DISCHARGED[stacks:03AG,03RV,025P][tier:C][crit:yes][prop:2.29] dim H²_cts(Π,𝔽₂) ≤ h²_G(T)
/-- **Proposition 2.29 in dimensions**: `dim H²_cts(Π_m, 𝔽₂) ≤ h²_{G₀}(𝒯_m)`. -/
theorem finrank_H2_le_hG2 : Module.finrank (ZMod 2) (H2 P.Γ (ZMod 2)) ≤ P.obs.hG 2 :=
  P.cmp.finrank_H2_le

/-- **Proposition 3.17, sharpened.**  `dim H²_cts(Π_m, 𝔽₂) ≤ (328g + 327) t + (45g + 13)/2`
with `g = 2^m - 1` and `t` the number of odd primes `≤ 2g + 1`: the paper's bound with the exact
dyadic component count, and no `m`. -/
theorem finrank_H2_le_b' :
    (Module.finrank (ZMod 2) (H2 P.Γ (ZMod 2)) : ℝ) ≤
      (328 * ((2 ^ m - 1 : ℕ) : ℝ) + 327) * Numeric.oddPrimeCount (2 ^ m - 1) +
        (45 * ((2 ^ m - 1 : ℕ) : ℝ) + 13) / 2 := by
  have hm : 4 ≤ m := P.obs.dyadic.hm.1
  have hg1 : 1 ≤ 2 ^ m - 1 := by
    have : 2 ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [← Numeric.b'_eq (by omega) rfl]
  exact (Nat.cast_le.mpr P.finrank_H2_le_hG2).trans (P.obs.hG2_le_b' hg1)

/-- **Proposition 3.17.**  For `m ≥ 10529`, `dim H²_cts(Π_m, 𝔽₂) < g²/4` with `g = 2^m - 1`.
(The paper states this for `m ≥ 32768`.) -/
theorem finrank_H2_lt_quarter_sq (hm : 10529 ≤ m) :
    (Module.finrank (ZMod 2) (H2 P.Γ (ZMod 2)) : ℝ) < ((2 ^ m - 1 : ℕ) : ℝ) ^ 2 / 4 :=
  (Nat.cast_le.mpr P.finrank_H2_le_hG2).trans_lt (P.obs.hG2_lt_quarter_sq hm rfl)

end PaperSetup

/-- **The geometric interface.**  Projectivity over `Spec ℤ` and the Galois property as opaque
predicates, and the construction of Section 3 for every `m ≥ 4`. -/
class PaperConstruction where
  /-- projective over `Spec ℤ` (Stacks `01W7`) -/
  IsProjective : ∀ {S : Scheme}, (S ⟶ SpecZ) → Prop
  /-- Galois cover: a finite étale torsor under a finite group (Stacks `0BN0`) -/
  IsGaloisCover : ∀ {X Y : Scheme}, (X ⟶ Y) → Prop
  -- OBLIGATION[paper:3.16][tier:C][crit:yes][prop:3.16] the construction of Sections 3.1–3.5
  setup : ∀ m : ℕ, 4 ≤ m → PaperSetup @IsProjective @IsGaloisCover m

end GSArith.Oracle

end
