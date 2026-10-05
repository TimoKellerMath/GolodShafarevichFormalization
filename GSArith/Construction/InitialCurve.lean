/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import GSArith.Ledger

/-!
# The initial curve and its regular model (Propositions 3.1–3.3)

The group-theoretic content of Proposition 3.1 — `Gal(L/K) ≅ 𝔽₂^g` of order `2^g` and
generator rank `g`, with `C₀ → C` geometrically connected (`q₀(Δ) = G₀`) — is carried by the
fields `card_L₀`, `rank_L₀`, `delta_L₀` of `GSArith.Oracle.PaperSetup`; the genus
`g(C₀) - 1 = 2^g (g - 1)` by `genus_L₀`; the `2^g` rational points above `P₊` by
`sections_L₀`.  Propositions 3.2 and 3.3 are absorbed into the realization fields of the same
record.  The independence of the Kummer classes `uᵢ` (the square-class half of Proposition 2.16,
LEAN-PLAN.md P15) is deferred to the enrichment pass.

What is recorded here is the one explicit computation of Proposition 3.1: in the coordinate
`t = 1/x`, every `uᵢ = (1 - i t)(1 - (i + ℓ) t)/(1 - g t)²` takes the value `1` at `t = 0`, and
the equation at infinity `w² = ∏ (1 - i t)(1 - (i + ℓ) t)` has the two solutions `w = ±1`
there — so all `2^g` lifts of each point at infinity are rational.
-/

@[expose] public section

namespace GSArith.Construction

/-- `uᵢ(∞) = 1`: the Kummer functions of Proposition 3.1 take the value `1` at `t = 0`. -/
theorem kummer_at_infinity {K : Type*} [Field K] (i l g : K) :
    (1 - i * 0) * (1 - (i + l) * 0) / (1 - g * 0) ^ 2 = 1 := by simp

/-- The equation at infinity `w² = ∏ (1 - i t)(1 - (i + ℓ) t)` has the solutions `w = ±1` at
`t = 0`. -/
theorem equation_at_infinity {K : Type*} [Field K] (S : Finset K) (l : K) (w : K) :
    w ^ 2 = ∏ i ∈ S, ((1 - i * 0) * (1 - (i + l) * 0)) ↔ w = 1 ∨ w = -1 := by
  simp only [mul_zero, sub_zero, one_mul, Finset.prod_const_one]
  constructor
  · intro h
    have h' : (w - 1) * (w + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linear_combination h1
    · right; linear_combination h1
  · rintro (rfl | rfl) <;> ring

end GSArith.Construction

