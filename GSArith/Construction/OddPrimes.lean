/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Oracle.EtaleCohomology

/-!
# Models at odd primes: the equivariant bound (Proposition 3.12)

The bookkeeping of Proposition 3.12 of Dérickx–Gillibert–Keller–Pagano, *Golod–Shafarevich
for arithmetic surfaces*, over the situation record `GSArith.Oracle.OddLocalSituation`:

  `h¹(Y) ≤ 12N`, `h²(Y) ≤ 7N`, `h⁰(ℋ¹) ≤ 30N`, `h¹(ℋ¹) ≤ 68N`, `h⁰(ℋ²) ≤ 45N`,
  `h¹_G(T_k̄) ≤ 42N`, `h²_G(T_k̄) ≤ 120N`, `h²_G(T) ≤ 162N`.

One lemma per displayed inequality, as LEAN-PLAN.md (P25) asks, so that a constant that
changes in a revision produces one failing lemma.  The counting core of Proposition 3.10 is
`GSArith.Combinatorics.two_mul_centreCount_lt`; the geometric bounds of Proposition 3.11
(`c ≤ 7N`, `s ≤ 8N`, `a ≤ 2N`) are fields of the record.
-/

@[expose] public section

namespace GSArith.Oracle.OddLocalSituation

variable {N : ℕ} (S : OddLocalSituation N)

theorem h1Y_le' : S.hY 1 ≤ 12 * N := by
  have := S.h1Y_le; have := S.a_le; have := S.s_le; omega

theorem h2Y_le' : S.hY 2 ≤ 7 * N := by
  have := S.h2Y_le; have := S.c_le; omega

theorem h0H1_le' : S.hH1 0 ≤ 30 * N := by
  have := S.h0H1_le; have := S.c_le; have := S.s_le; omega

theorem h1H1_le' : S.hH1 1 ≤ 68 * N := by
  have := S.h1H1_le; have := S.a_le; have := S.s_le; have := S.c_le; omega

theorem h0H2_le' : S.hH2 0 ≤ 45 * N := by
  have := S.h0H2_le; have := S.c_le; have := S.s_le; omega

/-- `h¹_G(T_k̄) ≤ 42N`. -/
theorem hGbar1_le' : S.hGbar 1 ≤ 42 * N := by
  have := S.hGbar1_le; have := S.h1Y_le'; have := S.h0H1_le'; omega

/-- `h²_G(T_k̄) ≤ 120N`. -/
theorem hGbar2_le' : S.hGbar 2 ≤ 120 * N := by
  have := S.hGbar2_le; have := S.h2Y_le'; have := S.h1H1_le'; have := S.h0H2_le'; omega

/-- **Proposition 3.12.**  `h²_G(T) ≤ 162N`. -/
theorem hG2_le' : S.hG 2 ≤ 162 * N := by
  have := S.hG2_le; have := S.hGbar1_le'; have := S.hGbar2_le'; omega

end GSArith.Oracle.OddLocalSituation

end
