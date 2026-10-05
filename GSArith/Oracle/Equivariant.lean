/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

/-!
# Interface: equivariant cohomology

Merged into `GSArith.Oracle.EtaleCohomology`: the equivariant inputs of Propositions 2.24–2.28
(free descent, the henselian trait, henselian excision, the stabilizer spectral sequence, the
reduction of a `2`-group quotient) are fields of the situation records `OddLocalSituation`,
`DyadicLocalSituation`, `GoodLocusSituation` and `ObstructionSituation` there, and the
combinations the paper performs are theorems in `GSArith.Construction.OddPrimes`,
`GSArith.Construction.Dyadic` and `GSArith.Construction.ObstructionBound`.  The
`H^*(𝔽₂^r, 𝔽₂)` computation of Proposition 3.12 (`h¹(I) ≤ 2`, `h²(I) ≤ 3` for `r ≤ 2`) is
absorbed into the constructible-sheaf bounds `h0H1_le`, `h1H1_le`, `h0H2_le`.
-/
