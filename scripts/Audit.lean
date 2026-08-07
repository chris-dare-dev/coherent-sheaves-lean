/-
Axiom audit. Run with:  lake env lean scripts/Audit.lean

Every line must print either "does not depend on any axioms" or exactly
`[propext, Classical.choice, Quot.sound]`. Any occurrence of `sorryAx` is a
failure: this library has no `sorry`, and the trust boundary is carried by the
*fields* of `NumericalVariety`, which are visible in its type, not by holes.
-/
import CohLean

open AlgebraicGeometry AlgebraicGeometry.Numerical

-- Layer A: the general Riemann-Roch expansion and its surface specialisation.
#print axioms NumericalVariety.degree_ch_mul_todd
#print axioms NumericalVariety.chi_eq_sum
#print axioms NumericalVariety.chComp_eq_zero_of_lt
#print axioms NumericalVariety.toddComp_eq_zero_of_lt
#print axioms Surface.chi_eq
#print axioms Surface.discriminant_mem_piece_two
#print axioms Surface.degree_discriminant

-- Layer A: the K3 specialisation.
#print axioms K3.chi_eq
#print axioms K3.chi_eq_rank_add_mukaiS
#print axioms K3.mukaiSelfPairing_eq
#print axioms K3.mukaiSelfPairing_of_rank_eq_zero

-- Layer A: the consistency witness. If this depended on `sorryAx` the whole
-- interface would be unmodelled.
#print axioms Examples.instNumericalRingPoint
#print axioms Examples.instNumericalVarietyPoint
#print axioms Examples.pointPiece_isInternal

-- Layer B stage 1.
#print axioms Scheme.Modules.IsCoherent
#print axioms Coh
#print axioms Coh.ι
