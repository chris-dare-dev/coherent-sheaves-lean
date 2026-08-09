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

-- Layer B stage 1: the affine comparison, forward direction.
#print axioms isFinitePresentation_tilde
#print axioms isCoherent_tilde
#print axioms isCoherent_tilde_of_finite
-- Layer B stage 1: the geometric half of the affine comparison theorem. The first two
-- are general sheaf theory; the rest reduce `IsIso fromTildeΓ` to a statement about
-- localisation of modules.
#print axioms TopCat.Presheaf.stalkFunctor_map_surjective_of_isBasis
#print axioms TopCat.Sheaf.isIso_of_isIso_app_of_isBasis
#print axioms Scheme.Modules.basicOpenRestriction
#print axioms Scheme.Modules.toOpen_comp_fromTildeΓ_app
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_tilde
#print axioms isIso_fromTildeΓ_app_basicOpen
#print axioms isIso_fromTildeΓ_of_isLocalizedModule

-- Layer B stage 1: the converse, making the affine comparison a characterisation.
#print axioms Scheme.Modules.basicOpenRestriction_naturality
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isIso
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_presentation
#print axioms Scheme.Modules.isIso_fromTildeΓ_iff_isLocalizedModule

-- Layer B stage 1: a quasi-coherent sheaf on an affine scheme has presentations on a
-- basic-open cover. The first declaration is the reusable iterated-slice restriction step.
#print axioms SheafOfModules.Presentation.over
#print axioms Scheme.Modules.exists_basicOpen_presentation_cover
#print axioms Scheme.Hom.opensRangeModulesEquivalenceInverseUnitIso
#print axioms Scheme.Hom.restrictPresentation

-- Layer B stage 1: Hartshorne II.5.1. Presentations on a basic-open cover supply uniform
-- exponents for both localisation clauses; the sheaf axiom glues the normalized lifts.
#print axioms IsLocalizedModule.restrictScalars_algebraMapSubmonoid
#print axioms Scheme.Modules.basicOpenRestrictionOver
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestrictionOver_of_presentation
#print axioms Scheme.Modules.exists_power_smul_eq_of_basicOpenRestriction_eq_of_cover
#print axioms Scheme.Modules.exists_power_smul_eq_basicOpenRestriction_of_cover
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_cover
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent
#print axioms Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent

-- Layer B stage 1: the finiteness corollaries of the affine comparison. Finite local
-- generators and presentations are transported to affine basic opens, where the comparison
-- turns them into finite modules; localisation patching then returns to `Spec R`.
#print axioms SheafOfModules.GeneratingSections.map
#print axioms SheafOfModules.GeneratingSections.isFiniteType_map
#print axioms SheafOfModules.GeneratingSections.over
#print axioms SheafOfModules.GeneratingSections.isFiniteType_over
#print axioms Scheme.Modules.basicOpenSpecMap
#print axioms Scheme.Modules.basicOpenSpecMap_opensRange
#print axioms Scheme.Modules.restrictBasicOpenTopLinearEquiv
#print axioms Scheme.Modules.GeneratingSections.restrictBasicOpen
#print axioms Scheme.Modules.GeneratingSections.isFiniteType_restrictBasicOpen
#print axioms Scheme.Modules.QuasicoherentData.restrictBasicOpen
#print axioms Scheme.Modules.exists_basicOpen_presentation_cover_of_quasicoherentData
#print axioms Scheme.Modules.isIso_fromTildeΓ_of_quasicoherentData
#print axioms Scheme.Modules.isIso_fromTildeΓ_restrictBasicOpen_of_quasicoherentData
#print axioms Scheme.Modules.moduleFinite_globalSections_of_generatingSections
#print axioms Scheme.Modules.moduleFinite_globalSections_of_presentation
#print axioms Scheme.Modules.exists_basicOpen_finiteGenerating_cover
#print axioms Scheme.Modules.moduleFinite_globalSections_of_isFiniteType
#print axioms Scheme.Modules.moduleFinite_globalSections
#print axioms moduleFinite_globalSections_of_isFiniteType
#print axioms moduleFinitePresentation_globalSections_of_isCoherent

-- Layer B stage 1: the affine equivalence. The two objectwise finiteness directions
-- restrict Mathlib's tilde-global-sections adjunction to the corresponding full
-- subcategories; its unit and counit are then pointwise isomorphisms.
#print axioms Coh.affineGlobalSections
#print axioms FGModuleCat.affineTilde
#print axioms Coh.affineAdjunction
#print axioms Coh.affineEquivalence
#print axioms Coh.affineEquivalence_functor
#print axioms Coh.affineEquivalence_inverse

-- Layer B stage 1: kernels and cokernels. Restriction along open immersions is left exact,
-- localization commutes with kernels, and the affine comparison transports both ambient
-- (co)kernels to finite modules. The final instances create (co)kernels in `Coh X`.
#print axioms AlgebraicGeometry.modulesSpecToSheaf_preservesFiniteLimits
#print axioms Scheme.Modules.restrictFunctor_preservesFiniteLimits
#print axioms LinearMap.kerMap
#print axioms IsLocalizedModule.kerMap
#print axioms IsLocalizedModule.kernelMap
#print axioms IsLocalizedModule.kernelNatTrans
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_kernel
#print axioms Scheme.Modules.isCoherent_kernel_affine
#print axioms Scheme.Modules.isCoherent_cokernel_affine
#print axioms Scheme.Modules.restrictKernelIso
#print axioms Scheme.Modules.restrictCokernelIso
#print axioms Scheme.Modules.isCoherent_kernel
#print axioms Scheme.Modules.isCoherent_cokernel
#print axioms Scheme.coherent_isClosedUnderKernels
#print axioms Scheme.coherent_isClosedUnderCokernels

-- Layer B stage 1: extensions. Local lifts of finite generators and relations produce a
-- finite horseshoe presentation of the middle term, without a noetherian hypothesis.
#print axioms SheafOfModules.IsFinitePresentation.middle_of_shortExact
#print axioms SheafOfModules.isFinitePresentation_isClosedUnderExtensions
#print axioms Scheme.coherent_isClosedUnderExtensions

-- Layer B stage 1: abelianity and the exact inclusion. The full subcategory contains zero
-- and finite products; kernel/cokernel closure then supplies the abelian structure and makes
-- the inclusion preserve all finite limits and colimits.
#print axioms SheafOfModules.isFinitePresentation_containsZero
#print axioms Scheme.coherent_containsZero
#print axioms Scheme.coherent_isClosedUnderBinaryProducts
#print axioms Scheme.coherent_isClosedUnderFiniteProducts
#print axioms Coh.preadditive
#print axioms Coh.abelian
#print axioms Coh.ι_preservesZeroMorphisms
#print axioms Coh.ι_additive
#print axioms Coh.ι_preservesFiniteLimits
#print axioms Coh.ι_preservesFiniteColimits
#print axioms Coh.exactInclusion
#print axioms Coh.shortExact_map_ι

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
