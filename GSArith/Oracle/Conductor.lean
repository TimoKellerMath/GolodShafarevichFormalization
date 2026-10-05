/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Oracle.Surfaces
public import GSArith.Numeric.TowerArithmetic

/-!
# Interface: conductors (Lemmas 3.22, 3.23 and Corollary 3.24)

The conductor `𝔑(D) = ∏_p p^{a_p(D)}` of a smooth projective curve `D/ℚ` (Section 3.7) enters
only through two facts, both taken from the literature:

* outside the fixed finite set `Σ` of bad primes of the initial curve the tower has good
  reduction, so `a_p = 0` there (smooth proper base change, Stacks `095T`, `0EYU`);
* at `p ∈ Σ` a single Galois extension `E_p/ℚ_p` gives regular semistable models of every
  curve in the tower (Lemmas 3.22, 3.23: purity `0BMB` and semistable reduction `0CDN`,
  `0CDB`), so by the semistable monodromy theorem (Illusie, §6.3) the wild inertia of
  `E_p` acts trivially on `H¹`, whence `a_p(Cₙ) ≤ 2 (1 + B_p) g(Cₙ)` with `B_p` a bound on the
  upper ramification breaks of `E_p/ℚ_p` (Serre, *Local Fields*, IV and VI).

These are the fields of `GSArith.Oracle.ConductorData`; the summation that turns them into
`log 𝔑(Cₙ) ≤ A_m · g(Cₙ)` is `GSArith.Numeric.conductor_sum_bound`, and the divergence of the
genus is `GSArith.Numeric.genus_tendsto_atTop`.
-/

@[expose] public section

namespace GSArith.Oracle

open GSArith.Profinite

/-- Conductor data for the tower attached to a `PaperSetup`: the bad primes `Σ`, the
ramification-break bounds `B_p`, the local exponents `a_p(C_L)` and the conductor `𝔑(C_L)` of
the generic fibre of each level, with the two inputs above. -/
structure ConductorData {IsProj : ∀ {S : AlgebraicGeometry.Scheme}, (S ⟶ SpecZ) → Prop}
    {IsGal : ∀ {X Y : AlgebraicGeometry.Scheme}, (X ⟶ Y) → Prop} {m : ℕ}
    (P : PaperSetup IsProj IsGal m) where
  /-- the bad primes `Σ` -/
  bad : Finset ℕ
  bad_pos : ∀ p ∈ bad, 1 ≤ p
  /-- a bound on the upper ramification breaks of `E_p/ℚ_p` -/
  B : ℕ → ℕ
  /-- the local conductor exponent `a_p(C_L)` -/
  exponent : (p : ℕ) → (L : Level P.Γ) → P.Δ.map L.q.toMonoidHom = ⊤ → ℕ
  /-- the conductor `𝔑(C_L)` -/
  conductor : (L : Level P.Γ) → P.Δ.map L.q.toMonoidHom = ⊤ → ℕ
  -- OBLIGATION[stacks:095T,0EYU][tier:C][crit:yes][prop:3.24] good reduction outside Σ
  conductor_eq : ∀ L hL, conductor L hL = ∏ p ∈ bad, p ^ exponent p L hL
  -- OBLIGATION[stacks:0CDN,0CDB,0BMB][tier:C][crit:yes][prop:3.23] a_p ≤ 2(1+B_p)g (Illusie 6.3)
  exponent_le : ∀ p ∈ bad, ∀ L hL, exponent p L hL ≤ 2 * (1 + B p) * P.genus L hL

/-- The conductor interface: conductor data for every setup of the construction. -/
class ConductorOracle [PaperConstruction] where
  -- OBLIGATION[lit:Serre-LocalFields-IV-VI][tier:C][crit:yes][prop:3.24] conductor data
  data : ∀ (m : ℕ) (hm : 4 ≤ m), ConductorData (PaperConstruction.setup m hm)

end GSArith.Oracle

end
