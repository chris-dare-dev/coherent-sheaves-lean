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

-- Layer A: the threefold and fourfold specialisations. These are the check that
-- degree_ch_mul_todd is dimension-general, so they must not acquire axioms that the
-- n = 2 case does not have.
#print axioms Threefold.chi_eq
#print axioms CalabiYauThreefold.chi_eq
#print axioms CalabiYauThreefold.chi_eq_of_chComp_eq
#print axioms Fourfold.chi_eq

-- Layer A: the dual involution and the Euler pairing. chi2 is what Bridgeland stability
-- is defined against, so a sorry here would contaminate the downstream repos.
#print axioms NumericalRingWithDual
#print axioms NumericalVariety.dual_ch
#print axioms NumericalVariety.chDual_add
#print axioms NumericalVariety.chi₂_eq_sum
#print axioms NumericalVariety.chi₂_eq_degree_dual_ch
#print axioms NumericalVariety.chi₂_add_left
#print axioms NumericalVariety.chi₂_add_right
#print axioms Surface.chi₂_eq
#print axioms Surface.chi₂_eq_chi_of_isStructureSheafLike
#print axioms Surface.chi₂_sub_chi₂_swap
#print axioms Surface.chi₂_symm_of_toddComp_one_eq_zero
#print axioms K3.mukaiPairing_self
#print axioms K3.chi₂_eq_neg_mukaiPairing
#print axioms K3.chi₂_self

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
#print axioms Examples.SurfaceRing
#print axioms Examples.H_pow_three
#print axioms Examples.surfaceNumericalRing
#print axioms Examples.surfaceDegree_normalForm
#print axioms Examples.surfaceDegree_ch_mul_todd
#print axioms Examples.k3NumericalVariety
#print axioms Examples.k3_isK3

-- Layer A: the projective plane. Its td1 is nonzero, so it is the model that can
-- detect an error in the c1.td1 term of Surface.chi_eq.
#print axioms Examples.p2NumericalVariety
#print axioms Examples.p2_chi_structureSheaf
#print axioms Examples.p2Chi_lineBundle
#print axioms Examples.p2ChCoeff_lineBundle

-- Layer B: the Mathlib gap that blocks the local-to-global criterion for coherence.
#print axioms SheafOfModules.Presentation.isFinite_of_isIso
#print axioms SheafOfModules.Presentation.isFinite_map
#print axioms SheafOfModules.Presentation.isFinitePresentation_quasicoherentData
#print axioms SheafOfModules.IsFinitePresentation.of_presentation

-- Layer B stage 1.
#print axioms Scheme.Modules.IsCoherent
#print axioms Coh
#print axioms Coh.ι
#print axioms SheafOfModules.QuasicoherentData.ofIso
#print axioms SheafOfModules.QuasicoherentData.isFinitePresentation_ofIso
#print axioms SheafOfModules.IsFinitePresentation.of_iso
#print axioms SheafOfModules.isFinitePresentation_isClosedUnderIsomorphisms
#print axioms Scheme.coherent_isClosedUnderIsomorphisms
#print axioms SheafOfModules.QuasicoherentData.presentationOver
#print axioms SheafOfModules.QuasicoherentData.presentationOver_generators_I
#print axioms SheafOfModules.QuasicoherentData.presentationOver_relations_I
#print axioms SheafOfModules.QuasicoherentData.over
#print axioms SheafOfModules.QuasicoherentData.isFinitePresentation_over
#print axioms SheafOfModules.IsFinitePresentation.over
#print axioms SheafOfModules.IsFinitePresentation.of_coversTop
#print axioms TopCat.Opens.grothendieckTopology_coversTop
#print axioms Scheme.Hom.opensRangeEquivalence
#print axioms Scheme.Hom.opensRangeModulesEquivalence
#print axioms Scheme.Hom.restrictFunctorIsoOver
#print axioms Scheme.Hom.isFinitePresentation_restrict
#print axioms Scheme.Modules.IsCoherent.restrict_of_isOpenImmersion
#print axioms Scheme.Modules.IsCoherent.of_affineOpenCover
#print axioms Scheme.Modules.isCoherent_iff_of_affineOpenCover
#print axioms Scheme.Modules.IsCoherent.restrict_affineOpenCover
