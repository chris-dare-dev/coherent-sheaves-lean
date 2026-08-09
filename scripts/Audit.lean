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
#print axioms basicOpen_coversTop_of_span_eq_top
#print axioms Scheme.Hom.opensRangeEquivalence
#print axioms Scheme.Hom.opensRangeModulesEquivalence
#print axioms Scheme.Hom.restrictFunctorIsoOver
#print axioms Scheme.Hom.isFinitePresentation_restrict

-- Layer B stage 1: the reverse transport, making finite presentation invariant under the
-- open-immersion/slice equivalence rather than merely carried one way.
#print axioms Scheme.Hom.presentationOverOfEq
#print axioms Scheme.Hom.presentationOverOfEq_isFinite
#print axioms Scheme.Hom.overQuasicoherentData
#print axioms Scheme.Hom.overQuasicoherentData_isFinitePresentation
#print axioms Scheme.Hom.isFinitePresentation_over_of_restrict
#print axioms Scheme.Hom.isFinitePresentation_over_iff_restrict
#print axioms Scheme.Modules.IsCoherent.restrict_of_isOpenImmersion
#print axioms Scheme.Modules.IsCoherent.of_affineOpenCover
#print axioms Scheme.Modules.isCoherent_iff_of_affineOpenCover
#print axioms Scheme.Modules.IsCoherent.restrict_affineOpenCover

-- Layer B stage 1: the scheme-level affine-local criterion, stated without `Over`.
#print axioms Scheme.Modules.isCoherent_iff_restrict_affineOpenCover
-- Layer B stage 1: finite limits on the site, which is what lets a global presentation
-- be turned into finite presentation on a scheme at all. One file, replacing the two
-- independent workarounds that preceded it.
#print axioms TopologicalSpace.Opens.hasBinaryProducts
#print axioms TopologicalSpace.Opens.hasFiniteLimits

-- Layer B stage 1: the affine comparison, forward direction. The converse is not
-- proved -- see the module docstring of CohLean/Coh/Affine.lean.
#print axioms isFinitePresentation_tilde
#print axioms isCoherent_tilde
#print axioms isCoherent_tilde_of_finite
-- Layer B stage 1: the geometric half of the affine comparison theorem. The first two
-- are general sheaf theory; the rest reduce `IsIso fromTildeΓ` to a statement about
-- localisation of modules. The remaining half -- that quasi-coherence supplies that
-- statement -- is NOT proved; see CohLean/ForMathlib/AffineComparison.lean.
#print axioms TopCat.Presheaf.stalkFunctor_map_surjective_of_isBasis
#print axioms TopCat.Sheaf.isIso_of_isIso_app_of_isBasis
#print axioms Scheme.Modules.basicOpenRestriction
#print axioms Scheme.Modules.toOpen_comp_fromTildeΓ_app
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_tilde
#print axioms isIso_fromTildeΓ_app_basicOpen
#print axioms isIso_fromTildeΓ_of_isLocalizedModule

-- Layer B stage 1: the converse, making the affine comparison a characterisation. What
-- remains of the theorem is exactly the quasi-coherent case of the right-hand side.
#print axioms Scheme.Modules.basicOpenRestriction_naturality
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isIso
#print axioms Scheme.Modules.isIso_fromTildeΓ_iff_isLocalizedModule

-- Layer B stage 1: a quasi-coherent sheaf on an affine scheme has presentations on a
-- basic-open cover. The first declaration is the reusable iterated-slice restriction step.
#print axioms SheafOfModules.Presentation.over
#print axioms Scheme.Modules.exists_basicOpen_presentation_cover

-- Layer B stage 3: exactness of the bridge from sheaves of modules to abelian sheaves.
-- This is what lets a short exact sequence in `X.Modules` reach `Ext`, and hence the
-- cohomology long exact sequence. The first two are general category theory and have
-- nothing to do with sheaves.
#print axioms CategoryTheory.Adjunction.preservesColimit_comp_left
#print axioms CategoryTheory.Adjunction.preservesColimitsOfShape_of_comp_left
#print axioms SheafOfModules.preservesFiniteColimits_toSheaf
#print axioms SheafOfModules.preservesFiniteColimits_toSheaf'
#print axioms SheafOfModules.preservesEpimorphisms_toSheaf
#print axioms SheafOfModules.shortExact_map_toSheaf

-- Layer B stage 3: the link between cosimplicial (Cech) and simplicial (extra degeneracy)
-- machinery. Not the whole of the Cech vanishing chain -- see the module docstring of
-- CohLean/ForMathlib/ExtraCodegeneracy.lean for what is still missing.
#print axioms AlgebraicTopology.AlternatingCofaceMapComplex.opIso
#print axioms AlgebraicTopology.AlternatingCofaceMapComplex.opIso_hom_f
#print axioms AlgebraicTopology.AlternatingCofaceMapComplex.opIso_inv_f
#print axioms AlgebraicTopology.exactAt_succ_of_extraDegeneracy
#print axioms AlgebraicTopology.exactAt_succ_of_extraDegeneracy_map

-- Layer B stage 3: positive-degree exactness of the explicit Cech complex for a module
-- sheaf on a finite distinguished-open cover of an affine scheme. This is the affine Cech
-- vanishing theorem, not a comparison with derived-functor sheaf cohomology.
#print axioms CategoryTheory.cechComplex_exactAt_succ_of_isTerminal
#print axioms AlgebraicGeometry.tilde_cechComplex_exactAt_succ
#print axioms AlgebraicGeometry.tilde_cechComplex_exactAt_of_pos

-- Layer B stage 3: the same results reached from the `X.Modules` wrapper, which instance
-- search does not see through on its own. `Scheme.Modules.toSheaf` is the retyped functor
-- downstream work should use; the two transfer instances cover the goals that still arrive
-- on the wrong side.
#print axioms Scheme.Modules.epi_sheafOfModules
#print axioms Scheme.Modules.mono_sheafOfModules
#print axioms Scheme.Modules.toSheaf
#print axioms Scheme.Modules.additive_toSheaf
#print axioms Scheme.Modules.preservesFiniteLimits_toSheaf
#print axioms Scheme.Modules.preservesFiniteColimits_toSheaf
#print axioms Scheme.Modules.preservesEpimorphisms_toSheaf
#print axioms Scheme.Modules.shortExact_map_toSheaf

-- Layer B stage 3: `CohLean/Cohomology/Strategy.lean` contributes nothing here on
-- purpose. It is the compile-only API map for the B3 route decision and declares only
-- `example`s, which are anonymous and cannot be audited. Its guarantee is that it builds:
-- if an upstream declaration it names moves, `lake build` fails. The first real B3
-- theorem goes below this line.
