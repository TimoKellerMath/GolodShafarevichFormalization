module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.DegreeTwoDescent
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini
public import TauCeti.GroupTheory.GroupExtension.Cohomology
public import Mathlib.NumberTheory.Primorial
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.GroupTheory.Frattini
public import GSArith.Ledger
public import Mathlib.NumberTheory.Chebyshev
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiniteQuotient.Colimit
public import TauCeti.FieldTheory.SquareClassGroup.Basic
public import TauCeti.NumberTheory.Multiquadratic.SquareClass.Independence
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Anchor regression test

Every declaration of Mathlib or TauCeti that `LEAN-PLAN.md` names as a load-bearing anchor is
`#check`ed here, so that a dependency bump which renames or removes one fails loudly.
Run with `lake env lean test/Anchors.lean` (after `lake build`). -/

#check TauCeti.ContCohomology.H2
#check TauCeti.ContCohomology.Z2
#check TauCeti.ContCohomology.d1_apply
#check @TauCeti.ContCohomology.exists_explicitInfl2_eq
#check @TauCeti.proPFrattini
#check @TauCeti.FactorSet.cohomologyClass_eq_zero_iff
#check primorial_lt_four_pow
#check @NumberField.abs_discr_gt_two
#check @frattini
#check @Chebyshev.theta_le_log4_mul_x
#check @Chebyshev.pi_le_log4_mul_div
#check @TauCeti.ContCohomology.explicitInfl2_explicitFiniteQuotientTransition2
#check @TauCeti.linearIndependent_squareClass_iff
#check @TauCeti.Multiquadratic.finrank_adjoin_range_of_linearIndependent
#check @X_pow_sub_C_irreducible_iff_of_prime
#check @AdjoinRoot.mk_eq_mk
#check @rank_le
#check @Rat.ringOfIntegersEquiv
#check @NumberField.RingOfIntegers.mapRingEquiv

public section
@[gs_public] theorem smoke_public : (1 : ℕ) + 1 = 2 := rfl
end
#print axioms smoke_public
