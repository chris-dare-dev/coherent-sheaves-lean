/-
Axiom audit. Run with:  lake env lean scripts/Audit.lean

Every line must print either "does not depend on any axioms" or exactly
`[propext, Classical.choice, Quot.sound]`. Any occurrence of `sorryAx` is a
failure: this library has no `sorry`, and the trust boundary is carried by the
*fields* of `NumericalVariety`, which are visible in its type, not by holes.
-/
import CohLean

open AlgebraicGeometry AlgebraicGeometry.Numerical

-- Layer A: the graded-basis constructor. `ofGradedBasis` is what every concrete model
-- goes through, so a sorry here would silently contaminate every instance in the repo.
#print axioms gradedPiece
#print axioms gradedPiece_eq_bot
#print axioms gradedPiece_iSupIndep
#print axioms gradedPiece_iSup_eq_top
#print axioms gradedPiece_isInternal
#print axioms gradedPiece_mul_mem
#print axioms NumericalRing.ofGradedBasis

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

-- Layer A: the K3 model. If these carried a sorry the K3 theorems would still be
-- conditional, which is exactly what this model exists to stop being true.
#print axioms Examples.K3Ring
#print axioms Examples.H_pow_three
#print axioms Examples.k3NumericalRing
#print axioms Examples.k3Degree_normalForm
#print axioms Examples.k3NumericalVariety
#print axioms Examples.k3_isK3

-- Layer B stage 1.
#print axioms Scheme.Modules.IsCoherent
#print axioms Coh
#print axioms Coh.ι
