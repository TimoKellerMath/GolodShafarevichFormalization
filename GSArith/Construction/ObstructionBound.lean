/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Construction.OddPrimes
public import GSArith.Construction.Dyadic

/-!
# Dimension of the obstruction space (Proposition 3.17)

The assembly of Proposition 3.17 of Dérickx–Gillibert–Keller–Pagano, over the record
`GSArith.Oracle.ObstructionSituation`:

  `h²_G(T) ≤ h²_G(T_U) + Σ_p h²_G(T_{B_p}) + Σ_p h¹_G(T_{K_p})`      (2.26)
  `h²_G(T_U) ≤ (2g+1)(t+2)`                                       (2.22, 2.24)
  `h²_G(T_{B_p}) ≤ 324g + 324` for odd `p`                        (3.12)
  `h²_G(T_{B_2}) ≤ 5 (2^(m-1) - 1) + 14g + 4 ≤ 10gm + 14g + 4`   (3.13–3.15)
  `h¹_G(T_{K_p}) = 2g + 2` for odd `p`, `2g + 3` at `2`           (2.23, with Proposition 2.23's
                                                                    local computation)
  ⟹ `h²_G(T) ≤ (328g + 327)t + 5 (2^(m-1) - 1) + 20g + 9 = b'(g, m) ≤ b(g, m)`,

where `b(g, m) = (328g + 327)t + (10m + 20)g + 9` is the paper's bound and `b'` its `m`-free
sharpening (`b'(g, m) = (328g + 327)t + (45g + 13)/2` for `g = 2^m - 1`), and, with
`GSArith.Numeric.b_lt_quarter_sq`, `h²_G(T) < g²/4` for `m ≥ 10529`.  The step
`dim H²_cts(Π_m, 𝔽₂) ≤ h²_G(T)` (Proposition 2.29) is
`GSArith.Oracle.ComparisonSituation.finrank_H2_le` and is composed with these bounds in
`GSArith.Oracle.PaperSetup.finrank_H2_lt_quarter_sq`.
The final summation is checked symbolically (`ring`), not numerically.
-/

@[expose] public section

namespace GSArith.Oracle

open Finset

/-- Proposition 2.22: `h²(X, 𝔽₂) ≤ (2g + 1)(t + 2)`. -/
theorem GoodLocusSituation.hX2_le {g t : ℕ} (S : GoodLocusSituation g t) :
    S.hX 2 ≤ (2 * g + 1) * (t + 2) := by
  have h1 := S.leray
  have h2 := S.h2U_le
  rw [S.h1U] at h1
  calc S.hX 2 ≤ S.hU 2 + 2 * g * (t + 2) + 1 := h1
    _ ≤ (t + 1) + 2 * g * (t + 2) + 1 := by omega
    _ = (2 * g + 1) * (t + 2) := by ring

/-- Proposition 2.23: `h¹(C_{K_p}, 𝔽₂) = 2g + 2` for odd `p` and `2g + 3` for `p = 2`. -/
theorem GenericOverlapSituation.h1_eq {g p : ℕ} [Fact p.Prime] (S : GenericOverlapSituation g p) :
    S.hK 1 = if p = 2 then 2 * g + 3 else 2 * g + 2 := by
  rw [S.h1, Arithmetic.finrank_squareClassGroup_padic]
  split_ifs <;> ring

namespace ObstructionSituation

variable {g m : ℕ} (S : ObstructionSituation g m)

theorem sum_odd_le (hg : 1 ≤ g) :
    ∑ p ∈ (oddBadPrimes g).attach, (S.odd p p.2).hG 2 ≤
      Numeric.oddPrimeCount g * (162 * (2 * g + 2)) := by
  calc ∑ p ∈ (oddBadPrimes g).attach, (S.odd p p.2).hG 2
      ≤ (oddBadPrimes g).attach.card • (162 * (2 * g + 2)) :=
        sum_le_card_nsmul _ _ _ (fun p _ => (S.odd p p.2).hG2_le')
    _ = Numeric.oddPrimeCount g * (162 * (2 * g + 2)) := by
        rw [card_attach, card_oddBadPrimes hg, smul_eq_mul]

theorem sum_overlap_le (hg : 1 ≤ g) :
    ∑ p ∈ (oddBadPrimes g).attach,
        @GenericOverlapSituation.hK g p ⟨prime_of_mem_oddBadPrimes p.2⟩ (S.overlapOdd p p.2) 1 ≤
      Numeric.oddPrimeCount g * (2 * g + 2) := by
  calc _ ≤ (oddBadPrimes g).attach.card • (2 * g + 2) :=
        sum_le_card_nsmul _ _ _ (fun p _ => by
          rw [@GenericOverlapSituation.h1_eq g p ⟨prime_of_mem_oddBadPrimes p.2⟩]
          simp [ne_two_of_mem_oddBadPrimes p.2])
    _ = Numeric.oddPrimeCount g * (2 * g + 2) := by
        rw [card_attach, card_oddBadPrimes hg, smul_eq_mul]

theorem overlapTwo_eq : S.overlapTwo.hK 1 = 2 * g + 3 := by
  rw [S.overlapTwo.h1_eq]
  simp

/-- **Proposition 3.17, the bound, sharpened.**  `h²_G(T) ≤ b'(g, m)`, with the exact dyadic
component count. -/
theorem hG2_le_b' (hg : 1 ≤ g) : (S.hG 2 : ℝ) ≤ Numeric.b' g m := by
  have hexc := S.excision
  have hgood := S.good.hX2_le
  have hdy := S.dyadic.hG2_le_exact
  have hodd := S.sum_odd_le hg
  have hover := S.sum_overlap_le hg
  have htwo := S.overlapTwo_eq
  set t := Numeric.oddPrimeCount g with ht
  set X := 2 ^ (m - 1) - 1 with hX
  have key : (2 * g + 1) * (t + 2) + (5 * X + 14 * g + 4) + t * (162 * (2 * g + 2)) +
      (2 * g + 3) + t * (2 * g + 2) = (328 * g + 327) * t + 5 * X + 20 * g + 9 := by ring
  have hnat : S.hG 2 ≤ (328 * g + 327) * t + 5 * X + 20 * g + 9 := by
    rw [← key]
    linarith
  unfold Numeric.b'
  rw [← ht, ← hX]
  exact_mod_cast hnat

/-- **Proposition 3.17, the bound.**  `h²_G(T) ≤ b(g, m)`, the paper's form. -/
theorem hG2_le_b (hg : 1 ≤ g) : (S.hG 2 : ℝ) ≤ Numeric.b g m :=
  (S.hG2_le_b' hg).trans (Numeric.b'_le_b S.dyadic.hm.1 S.dyadic.hm.2)

/-- **Proposition 3.17, the equivariant bound.**  For `m ≥ 10529` and `g = 2^m - 1`,
`h²_G(T) < g²/4`. -/
theorem hG2_lt_quarter_sq (hm : 10529 ≤ m) (hg : g = 2 ^ m - 1) :
    (S.hG 2 : ℝ) < (g : ℝ) ^ 2 / 4 := by
  have hg1 : 1 ≤ g := by
    have : 2 ^ 15 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (S.hG2_le_b hg1).trans_lt (Numeric.b_lt_quarter_sq hm hg)

end ObstructionSituation

end GSArith.Oracle

end
