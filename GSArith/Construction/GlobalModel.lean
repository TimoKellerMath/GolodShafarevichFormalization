/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

/-!
# The global normalization model (Proposition 3.16)

Proposition 3.16 — the models `𝒫_m`, `𝒞_m`, `𝒯_m` and their local descriptions — is the content
of the interface field `GSArith.Oracle.PaperConstruction.setup`, whose value
`GSArith.Oracle.PaperSetup m` bundles the group `Π_m`, the obstruction situation of Proposition
3.17 and the realization of finite quotients as regular projective arithmetic surfaces.  Nothing
of Proposition 3.16 is expressible without blow-ups and normalizations of schemes, which Mathlib
lacks (LEAN-PLAN.md §1).
-/
