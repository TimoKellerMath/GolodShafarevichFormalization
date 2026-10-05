/-
Copyright (c) 2026 Timo Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timo Keller
-/
module

public import GSArith.Arithmetic.BranchClasses
public import GSArith.Arithmetic.LocalSquareClasses
public import GSArith.Arithmetic.UnramifiedZ
public import GSArith.Combinatorics.DigitSeparation
public import GSArith.Combinatorics.DyadicTree
public import GSArith.Construction.Dyadic
public import GSArith.Construction.GlobalModel
public import GSArith.Construction.InitialCurve
public import GSArith.Construction.ObstructionBound
public import GSArith.Construction.OddPrimes
public import GSArith.Construction.Tower
public import GSArith.GroupTheory.CentralExtension
public import GSArith.GroupTheory.GolodShafarevich.Filtration
public import GSArith.GroupTheory.GolodShafarevich.Inequality
public import GSArith.GroupTheory.GolodShafarevich.Presentation
public import GSArith.GroupTheory.GolodShafarevich.Series
public import GSArith.GroupTheory.InflationKernel
public import GSArith.GroupTheory.SuccessiveQuotients
public import GSArith.Ledger
public import GSArith.LinearAlgebra.FrobeniusFixed
public import GSArith.LinearAlgebra.Telescope
public import GSArith.Main
public import GSArith.Numeric.Chebyshev
public import GSArith.Numeric.ObstructionBound
public import GSArith.Numeric.TowerArithmetic
public import GSArith.Oracle.Comparison
public import GSArith.Oracle.Conductor
public import GSArith.Oracle.Equivariant
public import GSArith.Oracle.EtaleCohomology
public import GSArith.Oracle.Surfaces
public import GSArith.Profinite.FieldEmbedding
public import GSArith.Profinite.LiftDescent
public import GSArith.Profinite.Lifting

/-!
# `GSArith`: Golod–Shafarevich for arithmetic surfaces, in Lean

Root module: re-exports every file of the library.  See `LEAN-PLAN.md` (one directory up)
for the plan and `LEDGER.md` for the list of assumed statements.
-/
