/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Oracle.EtaleCohomology
public import GSArith.Combinatorics.DyadicTree

/-!
# The dyadic model: the equivariant bound (Propositions 3.13–3.15)

The bookkeeping of Propositions 3.13–3.15 of Dérickx–Gillibert–Keller–Pagano, over the record
`GSArith.Oracle.DyadicLocalSituation`:

  `h²_G(T) ≤ h + 5s ≤ 5n₂ + 14g + 4 = 5 (2^(m-1) - 1) + 14g + 4 ≤ 10gm + 14g + 4`.

The exact form (`hG2_le_exact`) keeps the paper's count `n₂ = 2^(m-1) - 1`, which with
`g = 2^m - 1` reads `h²_G(T_{B₂}) ≤ (33g + 3)/2`; the paper rounds it to `10gm + 14g + 4`
(`hG2_le'`).  The counts `n₂ = 2^(m-1) - 1 ≤ 2gm` are
`GSArith.Combinatorics.dyadic_component_le`; the
Artin–Schreier identity behind "total normalization genus zero" is
`GSArith.Combinatorics.four_term_identity`.
-/

@[expose] public section

namespace GSArith.Oracle.DyadicLocalSituation

variable {g m : ℕ} (S : DyadicLocalSituation g m)

/-- `h²_G(T) ≤ h + 5s` (Proposition 3.15). -/
theorem hG2_le_h_add : S.hG 2 ≤ S.h + 5 * S.s := by
  have := S.hG2_le; have := S.hGbar1_le; have := S.hGbar2_le; omega

/-- `h²_G(T_{B₂}) ≤ 5n₂ + 14g + 4`. -/
theorem hG2_le_n₂ : S.hG 2 ≤ 5 * S.n₂ + 14 * g + 4 := by
  have := S.hG2_le_h_add; have := S.h_le; have := S.s_le; omega

/-- **Propositions 3.13–3.15, exact form.**  `h²_G(T_{B₂}) ≤ 5 (2^(m-1) - 1) + 14g + 4`. -/
theorem hG2_le_exact : S.hG 2 ≤ 5 * (2 ^ (m - 1) - 1) + 14 * g + 4 := by
  have h := S.hG2_le_n₂
  rw [S.n₂_eq] at h
  exact h

/-- **Propositions 3.13–3.15**, as rounded in the paper.  `h²_G(T_{B₂}) ≤ 10gm + 14g + 4`. -/
theorem hG2_le' : S.hG 2 ≤ 10 * g * m + 14 * g + 4 := by
  have h1 := S.hG2_le_n₂
  have h2 := S.n₂_le
  have h3 : 5 * S.n₂ ≤ 5 * (2 * g * m) := Nat.mul_le_mul_left 5 h2
  have h4 : 5 * (2 * g * m) = 10 * g * m := by ring
  omega

end GSArith.Oracle.DyadicLocalSituation

end
