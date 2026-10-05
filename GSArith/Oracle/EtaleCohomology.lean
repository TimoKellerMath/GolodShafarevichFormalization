/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Arithmetic.LocalSquareClasses
public import GSArith.Numeric.ObstructionBound
public import GSArith.Combinatorics.DyadicTree

/-!
# Interface: étale cohomology of the local models

The cohomological inputs of §2.4–2.5 and §3.3–3.4 of Dérickx–Gillibert–Keller–Pagano,
*Golod–Shafarevich for arithmetic surfaces*, as **situation records**: each record bundles the
dimensions of the étale and equivariant cohomology groups of one local model together with the
inequalities among them that the paper takes from the Stacks Project (normalization sequence
of a nodal curve, constructible sheaves on a nodal curve, the stabilizer spectral sequence,
proper base change over a henselian trait, the Kummer sequence, Leray).  Every such
inequality is a field carrying an `OBLIGATION` tag; the *combinations* the paper performs —
Propositions 3.12, 3.15, 2.22, 2.23 and the summation of Proposition 3.17 — are theorems.

Following LEAN-PLAN.md (P21): the interface is deliberately **numerical**.  It speaks of
dimensions `h : ℕ → ℕ`, never of cohomology groups, because every downstream use is an
inequality between dimensions.  The records are hypotheses of the theorems that use them, not
axioms; their existence for the paper's models is the content of the geometric interface
`GSArith.Oracle.Surfaces`.
-/

@[expose] public section

namespace GSArith.Oracle

open TauCeti

/-! ### The odd-prime local situation (Propositions 3.11 and 3.12) -/

/-- The cohomological data of the situation of Proposition 3.12: a henselian DVR `R` with
finite residue field of odd characteristic, a regular proper flat curve `X/R` whose reduced
special fibre is strict normal crossings, with reduced geometric special fibre of at most `7N`
components, `8N` nodes and total normalization genus `2N`; a geometrically connected finite
étale Galois cover `D → X_{Frac R}` with elementary abelian `2`-group `G`, and `T` its
normalization over `X`.  `Y = (X_k̄)_red` is the quotient's reduced special fibre. -/
structure OddLocalSituation (N : ℕ) where
  /-- component count of `Y` -/
  c : ℕ
  /-- node count of `Y` -/
  s : ℕ
  /-- total normalization genus of `Y` -/
  a : ℕ
  -- OBLIGATION[paper:3.11][tier:C][crit:yes][prop:3.11] quadratic model: ≤ 7N components
  c_le : c ≤ 7 * N
  -- OBLIGATION[paper:3.11][tier:C][crit:yes][prop:3.11] quadratic model: ≤ 8N nodes
  s_le : s ≤ 8 * N
  -- OBLIGATION[paper:3.11][tier:C][crit:yes][prop:3.11] quadratic model: genus ≤ 2N
  a_le : a ≤ 2 * N
  /-- `hⁱ(Y, 𝔽₂)` -/
  hY : ℕ → ℕ
  /-- `hⁱ(Y, ℋ¹)`, the degree-one stabilizer sheaf -/
  hH1 : ℕ → ℕ
  /-- `hⁱ(Y, ℋ²)`, the degree-two stabilizer sheaf -/
  hH2 : ℕ → ℕ
  /-- `hⁱ_G(T_k̄)` -/
  hGbar : ℕ → ℕ
  /-- `hⁱ_G(T)` -/
  hG : ℕ → ℕ
  -- OBLIGATION[stacks:03QP,03RQ][tier:C][crit:yes][prop:2.18] nodal curve, h¹ ≤ 2a + s
  h1Y_le : hY 1 ≤ 2 * a + s
  -- OBLIGATION[stacks:03QP,03RQ][tier:C][crit:yes][prop:2.18] nodal curve, h² = c
  h2Y_le : hY 2 ≤ c
  -- OBLIGATION[stacks:03RY,03S2][tier:C][crit:yes][prop:2.19] ℋ¹ of rank ≤ 2, h⁰
  h0H1_le : hH1 0 ≤ 2 * (c + s)
  -- OBLIGATION[stacks:03RY,03S2][tier:C][crit:yes][prop:2.19] ℋ¹ of rank ≤ 2, h¹
  h1H1_le : hH1 1 ≤ 2 * (2 * a + 2 * s + 2 * c)
  -- OBLIGATION[stacks:03RY,03S2][tier:C][crit:yes][prop:2.19] ℋ² of rank ≤ 3, h⁰
  h0H2_le : hH2 0 ≤ 3 * (c + s)
  -- OBLIGATION[stacks:015J,04GK,03QO][tier:C][crit:yes][prop:2.27] stabilizer sequence, degree 1
  hGbar1_le : hGbar 1 ≤ hY 1 + hH1 0
  -- OBLIGATION[stacks:015J,04GK,03QO][tier:C][crit:yes][prop:2.27] stabilizer sequence, degree 2
  hGbar2_le : hGbar 2 ≤ hY 2 + hH1 1 + hH2 0
  -- OBLIGATION[stacks:095T,03QO,03QQ][tier:C][crit:yes][prop:2.25] henselian trait, degree 2
  hG2_le : hG 2 ≤ hGbar 2 + hGbar 1

/-! ### The dyadic local situation (Propositions 3.13–3.15) -/

/-- The cohomological data of the dyadic fibre: the model `𝒫₂`, its quadratic normalization
`𝒞₂` with reduced geometric special fibre `Y₂`, and the multiquadratic normalization `T₂`
with its `G₀`-action. -/
structure DyadicLocalSituation (g m : ℕ) where
  /-- number of geometric special-fibre components of `𝒫₂` -/
  n₂ : ℕ
  -- OBLIGATION[paper:3.13][tier:C][crit:yes][prop:3.13] depth-k components ↔ classes mod 2^k
  n₂_eq : n₂ = 2 ^ (m - 1) - 1
  -- OBLIGATION[paper:3.13][tier:C][crit:yes][prop:3.13] g = 2^m - 1 and m ≥ 4
  hm : 4 ≤ m ∧ g = 2 ^ m - 1
  /-- `h¹(Y₂, 𝔽₂)` -/
  h : ℕ
  -- OBLIGATION[stacks:0A3J,0A3L,03OY,02UU][tier:C][crit:yes][prop:3.13] h¹(Y₂) ≤ 5n₂ + 4g + 4
  h_le : h ≤ 5 * n₂ + 4 * g + 4
  /-- number of closed points of `Y₂` above which the geometric inertia is nontrivial -/
  s : ℕ
  -- OBLIGATION[stacks:0AG0,04GK,0BSD][tier:C][crit:yes][prop:3.14] inertia isolated at ≤ 2g points
  s_le : s ≤ 2 * g
  /-- `hⁱ_G(T_k̄)` -/
  hGbar : ℕ → ℕ
  /-- `hⁱ_G(T)` -/
  hG : ℕ → ℕ
  -- OBLIGATION[stacks:03SI,015J][tier:C][crit:yes][prop:3.15] isolated inertia, degree 1
  hGbar1_le : hGbar 1 ≤ h + 2 * s
  -- OBLIGATION[stacks:03SI,015J][tier:C][crit:yes][prop:3.15] isolated inertia, degree 2
  hGbar2_le : hGbar 2 ≤ 3 * s
  -- OBLIGATION[stacks:095T,03QO,03QQ][tier:C][crit:yes][prop:2.25] henselian trait at 2
  hG2_le : hG 2 ≤ hGbar 2 + hGbar 1

-- DISCHARGED[paper:3.13][tier:A][crit:yes][prop:3.13] n₂ ≤ 2gm, from the verified count
/-- `n₂ ≤ 2gm`, from `GSArith.Combinatorics.dyadic_component_le`. -/
theorem DyadicLocalSituation.n₂_le {g m : ℕ} (S : DyadicLocalSituation g m) :
    S.n₂ ≤ 2 * g * m := by
  obtain ⟨hm, hg⟩ := S.hm
  rw [S.n₂_eq, hg]
  exact (Combinatorics.dyadic_component_le m hm).1.trans
    (Combinatorics.dyadic_component_le m hm).2

/-! ### The good locus (Propositions 2.21, 2.22, 2.24) -/

/-- The cohomological data over `U = Spec ℤ[1/∏_{p ∈ Σ} p]`, `|Σ| = t + 1`: the base `U` and the
smooth proper curve `X = 𝒞_{m,U}` with `R¹f_*𝔽₂` constant of rank `2g`.  By free descent
(Proposition 2.24) `hⁱ(X) = hⁱ_{G}(T_U)`. -/
structure GoodLocusSituation (g t : ℕ) where
  /-- `hⁱ(U, 𝔽₂)` -/
  hU : ℕ → ℕ
  /-- `hⁱ(X, 𝔽₂) = hⁱ_G(T_U)` -/
  hX : ℕ → ℕ
  -- OBLIGATION[stacks:03PK,03P8][tier:C][crit:yes][prop:2.21] h¹(U) = t + 2 (Kummer)
  h1U : hU 1 = t + 2
  -- OBLIGATION[stacks:03Q9,03Q5][tier:C][crit:yes][prop:2.21] h²(U) ≤ t + 1 (BHN)
  h2U_le : hU 2 ≤ t + 1
  -- OBLIGATION[stacks:03QC,095T,0EYU][tier:C][crit:yes][prop:2.22] Leray + free descent
  leray : hX 2 ≤ hU 2 + 2 * g * hU 1 + 1

/-! ### The generic overlaps (Proposition 2.23) -/

/-- The cohomological data of the curve `C/K_p` over a local field, `K_p = ℚ_p` or the fraction
field of the henselization, with a rational point and `J(C)[2](K_p) ≅ 𝔽₂^{2g}`. -/
structure GenericOverlapSituation (g p : ℕ) [Fact p.Prime] where
  /-- `hⁱ(C_{K_p}, 𝔽₂) = hⁱ_G(T_{K_p})` -/
  hK : ℕ → ℕ
  -- OBLIGATION[stacks:03PK,03RN,04GE][tier:C][crit:yes][prop:2.23] h¹(C) = dim K^×/K^×2 + 2g
  h1 : hK 1 = Module.finrank (ZMod 2) (SquareClassGroup ℚ_[p]) + 2 * g

/-! ### The bad primes -/

/-- The primes `p ≤ 2g + 1`, i.e. `Σ`. -/
def badPrimes (g : ℕ) : Finset ℕ := (Finset.range (2 * g + 2)).filter Nat.Prime

/-- The odd primes `p ≤ 2g + 1`. -/
def oddBadPrimes (g : ℕ) : Finset ℕ := (badPrimes g).filter (· ≠ 2)

theorem prime_of_mem_badPrimes {g p : ℕ} (h : p ∈ badPrimes g) : p.Prime :=
  (Finset.mem_filter.mp h).2

theorem prime_of_mem_oddBadPrimes {g p : ℕ} (h : p ∈ oddBadPrimes g) : p.Prime :=
  prime_of_mem_badPrimes (Finset.mem_filter.mp h).1

theorem ne_two_of_mem_oddBadPrimes {g p : ℕ} (h : p ∈ oddBadPrimes g) : p ≠ 2 :=
  (Finset.mem_filter.mp h).2

theorem two_mem_badPrimes {g : ℕ} (hg : 1 ≤ g) : 2 ∈ badPrimes g := by
  rw [badPrimes, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, Nat.prime_two⟩

theorem card_badPrimes (g : ℕ) : (badPrimes g).card = Nat.primeCounting (2 * g + 1) := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rfl

theorem card_oddBadPrimes {g : ℕ} (hg : 1 ≤ g) :
    (oddBadPrimes g).card = Numeric.oddPrimeCount g := by
  rw [oddBadPrimes, Finset.filter_ne', Finset.card_erase_of_mem (two_mem_badPrimes hg),
    card_badPrimes]
  rfl

/-! ### The global situation (Propositions 2.26, 3.16) -/

/-- The cohomological data of the global model `T = 𝒯_m` with its `G₀`-action: the henselian
excision of Proposition 2.26, assembled from the good locus, the odd bad primes, the dyadic prime
and the generic overlaps.  The comparison with `H²_cts(Π_m, 𝔽₂)` (Proposition 2.29) is the
separate interface `GSArith.Oracle.ComparisonSituation`, whose Tier-A half is proved there. -/
structure ObstructionSituation (g m : ℕ) where
  /-- `hⁱ_{G₀}(T)` -/
  hG : ℕ → ℕ
  /-- the good locus -/
  good : GoodLocusSituation g (Numeric.oddPrimeCount g)
  /-- the odd bad primes -/
  odd : (p : ℕ) → p ∈ oddBadPrimes g → OddLocalSituation (2 * g + 2)
  /-- the dyadic prime -/
  dyadic : DyadicLocalSituation g m
  /-- the generic overlaps at the odd bad primes -/
  overlapOdd : (p : ℕ) → (hp : p ∈ oddBadPrimes g) →
    @GenericOverlapSituation g p ⟨prime_of_mem_oddBadPrimes hp⟩
  /-- the generic overlap at `2` -/
  overlapTwo : GenericOverlapSituation g 2
  -- OBLIGATION[stacks:08GS,09YQ][tier:C][crit:yes][prop:2.26] henselian excision (2)
  excision : hG 2 ≤ good.hX 2 + dyadic.hG 2 + (∑ p ∈ (oddBadPrimes g).attach, (odd p p.2).hG 2) +
    overlapTwo.hK 1 + ∑ p ∈ (oddBadPrimes g).attach,
      @GenericOverlapSituation.hK g p ⟨prime_of_mem_oddBadPrimes p.2⟩ (overlapOdd p p.2) 1

end GSArith.Oracle

end
