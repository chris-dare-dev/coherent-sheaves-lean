/-
Axiom audit. First build the optional specialization and development modules listed in
`README.md`, then run: `lake env lean scripts/Audit.lean`.

Every line must print either "does not depend on any axioms" or exactly
`[propext, Classical.choice, Quot.sound]`. Any occurrence of `sorryAx` is a
failure: this library has no `sorry`, and the trust boundary is carried by the
*fields* of `NumericalVariety`, which are visible in its type, not by holes.
-/
import CohLean
import CohLean.Intersection.ChernCharacter.Basic
import CohLean.Numerical.Specializations.Surface
import CohLean.Numerical.Specializations.Threefold
import CohLean.Numerical.Specializations.Fourfold
import CohLean.Development.AlgebraicGeometry.Divisors.API

open AlgebraicGeometry AlgebraicGeometry.Numerical

-- Proj foundations: degree-zero homogeneous module localization is a submodule of Mathlib's
-- ordinary localized module; every homogeneous and denominator certificate remains explicit.
#print axioms CohLean.AlgebraicGeometry.Proj.NumDenSameDeg
#print axioms CohLean.AlgebraicGeometry.Proj.degreeZeroSubmodule
#print axioms CohLean.AlgebraicGeometry.Proj.DegreeZeroLocalization.mk_surjective
#print axioms CohLean.AlgebraicGeometry.Proj.DegreeZeroLocalization.mk_eq_mk_iff
#print axioms CohLean.AlgebraicGeometry.Proj.DegreeZeroLocalization.mapOfLE
#print axioms CohLean.AlgebraicGeometry.Proj.DegreeZeroLocalization.awayMk
#print axioms CohLean.AlgebraicGeometry.Proj.GradedLinearMap
#print axioms CohLean.AlgebraicGeometry.Proj.GradedLinearMap.map
#print axioms CohLean.AlgebraicGeometry.Proj.GradedLinearMap.map_mk
#print axioms CohLean.AlgebraicGeometry.Proj.DegreeZeroLocalization.selfLinearEquiv
#print axioms CohLean.AlgebraicGeometry.Proj.DegreeZeroLocalization.natShiftSelfLinearEquiv
#print axioms CohLean.AlgebraicGeometry.Proj.DegreeZeroLocalization.natShiftAwayLinearEquiv
#print axioms CohLean.AlgebraicGeometry.Proj.DegreeZeroLocalization.natShiftLinearEquivOfMem
#print axioms CohLean.AlgebraicGeometry.Proj.isLocallyFraction
#print axioms CohLean.AlgebraicGeometry.Proj.associatedSheaf
#print axioms CohLean.AlgebraicGeometry.Proj.stalkEquiv
#print axioms CohLean.AlgebraicGeometry.Proj.moduleAwayToSection
#print axioms CohLean.AlgebraicGeometry.Proj.moduleAwayToSection_unique
#print axioms CohLean.AlgebraicGeometry.Proj.associatedSheafSelfIso
#print axioms CohLean.AlgebraicGeometry.Proj.moduleAwayToSection_self_bijective
#print axioms CohLean.AlgebraicGeometry.Proj.associatedMap
#print axioms CohLean.AlgebraicGeometry.Proj.associatedIsoOfPiecewiseIff
#print axioms CohLean.AlgebraicGeometry.Proj.natShift
#print axioms CohLean.AlgebraicGeometry.Proj.intShift
#print axioms CohLean.AlgebraicGeometry.Proj.mem_intShift_ofNat_iff
#print axioms CohLean.AlgebraicGeometry.Proj.sheafTwist
#print axioms CohLean.AlgebraicGeometry.Proj.sheafTwistZeroIso
#print axioms CohLean.AlgebraicGeometry.Proj.sheafNatTwistAddIso
#print axioms CohLean.AlgebraicGeometry.Proj.twistingSheaf
#print axioms CohLean.AlgebraicGeometry.Proj.twistingSheafOfNatIso
#print axioms CohLean.AlgebraicGeometry.Proj.AffineComparisonData
#print axioms CohLean.AlgebraicGeometry.Proj.localizedNatShiftDegreeOneIso
#print axioms CohLean.AlgebraicGeometry.Proj.natShiftSectionLinearEquiv
#print axioms CohLean.AlgebraicGeometry.Proj.moduleAwayToSection_natShift_degreeOne_bijective
#print axioms CohLean.AlgebraicGeometry.Proj.affineComparisonDataSelf
#print axioms CohLean.AlgebraicGeometry.Proj.associatedSheaf_self_isQuasicoherent
#print axioms CohLean.AlgebraicGeometry.Proj.AffineComparisonData.quasicoherentData
#print axioms CohLean.AlgebraicGeometry.Proj.AffineComparisonData.associatedSheaf_isQuasicoherent
#print axioms CohLean.AlgebraicGeometry.Proj.associatedSheaf_isCoherent_of_finitePresentation
#print axioms CohLean.AlgebraicGeometry.Proj.associatedSheaf_self_isCoherent
#print axioms CohLean.AlgebraicGeometry.Proj.associatedSheaf_isCoherent_of_noetherian_finite
#print axioms CohLean.AlgebraicGeometry.Proj.BasicOpenSectionData
#print axioms CohLean.AlgebraicGeometry.Proj.basicOpenSectionDataSelf
#print axioms CohLean.AlgebraicGeometry.Proj.basicOpenSectionEquiv
#print axioms CohLean.AlgebraicGeometry.Proj.TwistingSectionRange
#print axioms CohLean.AlgebraicGeometry.Proj.TwistingSectionRange.globalSections_finite
#print axioms CohLean.AlgebraicGeometry.Proj.projectiveSpace_globalSections_finite
#print axioms CohLean.AlgebraicGeometry.Proj.projectiveSpace_variableSection_bijective
#print axioms CohLean.AlgebraicGeometry.Proj.polynomialVariableBasicOpen_cover
#print axioms CohLean.AlgebraicGeometry.Proj.polynomialToNatGlobalSections_injective
#print axioms CohLean.AlgebraicGeometry.Proj.polynomialToNatGlobalSections_surjective
#print axioms CohLean.AlgebraicGeometry.Proj.polynomialNatGlobalSectionsAddEquiv
#print axioms CohLean.AlgebraicGeometry.Proj.polynomialTwistingGlobalSectionsAddEquiv
#print axioms CohLean.AlgebraicGeometry.Proj.polynomialTwistingGlobalSectionsModuleIso
#print axioms CohLean.AlgebraicGeometry.Proj.polynomialVariableCechDenominator_mem
#print axioms CohLean.AlgebraicGeometry.Proj.basicOpen_polynomialVariableCechDenominator

-- The geometric source object is a bundle of explicit data, not an axiom identifying schemes
-- with their numerical realizations.
#print axioms Variety
#print axioms SmoothProperVariety
#print axioms ChernClassData.chernCharacterFour
#print axioms ChernClassData.toddFour
#print axioms ChernClassData.chernCharacterComponent
#print axioms ChernClassData.toddComponent
#print axioms Variety.NumericalData.toNumericalVariety
#print axioms Variety.NumericalData.toNumericalVariety_chComp_four
#print axioms Variety.NumericalData.toNumericalVariety_toddComp_four
#print axioms Variety.NumericalData.chernCharacter_classOf
#print axioms Variety.NumericalData.chi_classOf
#print axioms Variety.NumericalData.coherentChernCharacter_shortExact
#print axioms Variety.NumericalData.coherentEulerCharacteristic_shortExact
#print axioms Cohomology.coherentH
#print axioms Cohomology.globalSectionSmul
#print axioms Cohomology.globalSectionSmul_naturality
#print axioms Cohomology.varietyScalarAction
#print axioms Cohomology.coherentScalarAction
#print axioms Cohomology.coherentHScalarAction
#print axioms Cohomology.coherentH_map_smul
#print axioms Cohomology.linearCoherentH
#print axioms Cohomology.linearCoherentHComparison
#print axioms Cohomology.canonicalLinearCohomology
#print axioms Cohomology.LinearCohomology
#print axioms Cohomology.FiniteDimensionalCohomology
#print axioms Cohomology.FiniteDimensionalCohomology.dimension_iso

-- Canonical-sheaf data is built from explicit cotangent/determinant certificates. The
-- canonical line is coherent, and the derived object is constructed as `ω_X[n]`.
#print axioms SheafOfModules.IsInvertible.isFinitePresentation
#print axioms Scheme.Modules.LineBundleData.isCoherent
#print axioms Scheme.Modules.LineBundleData.finiteLocallyFree
#print axioms Scheme.Modules.LineBundleData.unit
#print axioms Variety.baseFieldPresheaf
#print axioms Variety.baseFieldToGlobalSections
#print axioms Variety.baseFieldToStructurePresheaf
#print axioms Variety.relativeDifferentialsPresheaf
#print axioms Variety.relativeDifferentials
#print axioms Variety.relativeDerivationPresheaf
#print axioms Variety.relativeDifferentialsSheafification
#print axioms Variety.relativeDerivation
#print axioms Variety.relativeDifferentialsDesc
#print axioms Variety.relativeDifferentialsDesc_fac
#print axioms Variety.relativeDifferentialsDesc_unique
#print axioms Variety.relativeDifferentials_hom_ext
#print axioms Variety.relativeDifferentialsPresheaf_obj
#print axioms Variety.relativeDerivationPresheaf_d
#print axioms Variety.relativeDifferentialsPresheaf_obj_free
#print axioms Variety.relativeDifferentialsPresheaf_obj_rank
#print axioms Scheme.Modules.FixedRankTrivializations
#print axioms Scheme.Modules.FixedRankTrivializations.localGenerators
#print axioms Scheme.Modules.FixedRankTrivializations.localGenerators_isLocallyFreeData
#print axioms Scheme.Modules.FixedRankTrivializations.finiteLocallyFree
#print axioms Scheme.Modules.FixedRankTrivializations.isLocallyFree
#print axioms Variety.SmoothChart
#print axioms Variety.SmoothChart.ofSmooth
#print axioms Variety.SmoothCotangentTrivializations
#print axioms Variety.SmoothCotangentTrivializations.chartSources_coversTop
#print axioms Variety.SmoothCotangentTrivializations.fixedRankTrivializations
#print axioms Variety.SmoothCotangentTrivializations.finiteLocallyFree
#print axioms Variety.SmoothCotangentTrivializations.relativeDifferentials_isLocallyFree
#print axioms SmoothProperVariety.finiteCohomology
#print axioms SmoothProperVariety.point
#print axioms SmoothProperVariety.CanonicalSheafData
#print axioms SmoothProperVariety.CanonicalSheafData.ofRelativeDifferentials
#print axioms SmoothProperVariety.CanonicalSheafData.ofRelativeDifferentials_cotangent
#print axioms SmoothProperVariety.CanonicalSheafData.canonicalClass
#print axioms SmoothProperVariety.CanonicalSheafData.antiCanonicalClass
#print axioms SmoothProperVariety.CanonicalSheafData.canonicalClass_eq_of_iso
#print axioms SmoothProperVariety.CanonicalSheafData.CanonicalDivisorData
#print axioms SmoothProperVariety.CanonicalSheafData.CanonicalDivisorData.toPic_eq_canonicalClass
#print axioms SmoothProperVariety.CanonicalSheafData.CanonicalDivisorData.classToPic_eq_canonicalClass
#print axioms SmoothProperVariety.CanonicalSheafData.DualizingSheafComparison
#print axioms SmoothProperVariety.CanonicalSheafData.DualizingSheafComparison.candidateClass_eq
#print axioms SmoothProperVariety.CanonicalSheafData.canonicalCohObject
#print axioms SmoothProperVariety.CanonicalSheafData.dualizingComplex
#print axioms SmoothProperVariety.CanonicalSheafData.dualizingComplexIso
#print axioms SmoothProperVariety.CanonicalSheafData.pointCanonicalSheafData
#print axioms SmoothProperVariety.CanonicalSheafData.pointCanonicalSheafData_canonicalSheaf
#print axioms SmoothProperVariety.CanonicalSheafData.pointDualizingComplexIso

-- Layer B stage 5: Serre duality remains an explicit geometric realization. The derived
-- statement uses Mathlib's derived category, while the cohomological comparison targets its
-- actual Ext groups. Euler symmetry is proved from perfect pairings and dimension vanishing.
#print axioms CohLean.Duality.Serre.DerivedStatement
#print axioms CohLean.Duality.Serre.DerivedStatement.dualizingObject
#print axioms CohLean.Duality.Serre.DerivedStatement.canonicalShiftIso
#print axioms CohLean.Duality.Serre.Data
#print axioms CohLean.Duality.Serre.Data.pairing
#print axioms CohLean.Duality.Serre.Data.dimension_eq_ext
#print axioms CohLean.Duality.Serre.Data.LocallyFreeSpecialization
#print axioms CohLean.Duality.Serre.Data.LocallyFreeSpecialization.dimension_symmetry
#print axioms CohLean.Duality.Serre.Data.LocallyFreeSpecialization.eulerCharacteristic_eq_sum_dimension
#print axioms CohLean.Duality.Serre.Data.LocallyFreeSpecialization.eulerCharacteristic_symmetry
#print axioms CohLean.Duality.Serre.Data.LocallyFreeSpecialization.surface_eulerCharacteristic_symmetry
#print axioms CohLean.Duality.Serre.Data.SurfaceLineBundleFamily
#print axioms CohLean.Duality.Serre.Data.SurfaceLineBundleFamily.toSurfacePicardSymmetry
#print axioms CohLean.Duality.Serre.Data.SurfacePicardSymmetry
#print axioms CohLean.Duality.Serre.Data.SurfacePicardSymmetry.canonical
#print axioms CohLean.Duality.Serre.Data.SurfacePicardSymmetry.k3
#print axioms Cohomology.FiniteCohomology
#print axioms Cohomology.FiniteCohomology.eulerCharacteristic
#print axioms Cohomology.FiniteCohomology.finrankSupport_subset_range
#print axioms Cohomology.FiniteCohomology.eulerCharacteristic_eq_sum
#print axioms Cohomology.FiniteCohomology.eulerCharacteristic_eq_sum_of_bound
#print axioms Cohomology.FiniteCohomology.dimension_iso
#print axioms Cohomology.FiniteCohomology.eulerCharacteristic_iso
#print axioms Cohomology.coherentConnectingMap
#print axioms Cohomology.FiniteCohomology.LinearConnectingMaps
#print axioms Cohomology.FiniteCohomology.exact₂
#print axioms Cohomology.FiniteCohomology.LinearConnectingMaps.exact₃
#print axioms Cohomology.FiniteCohomology.LinearConnectingMaps.exact₁
#print axioms Cohomology.FiniteCohomology.alternating_finrank_eq_zero_of_exact
#print axioms Cohomology.FiniteCohomology.eulerCharacteristic_additive
#print axioms Cohomology.FiniteCohomology.eulerCharacteristic_additive_modules
#print axioms Cohomology.CoherentGrothendieckRelation
#print axioms Cohomology.FiniteCohomology.coherentGrothendieckRelations_le_ker
#print axioms Cohomology.FiniteCohomology.grothendieckEulerHom
#print axioms Cohomology.FiniteCohomology.grothendieckEulerHom_class

-- Layer B stage 5: dimension-independent descent of additive coherent-sheaf invariants through
-- K₀. Surface compatibility aliases are audited immediately afterward.
#print axioms CohLean.RiemannRoch.CoherentAdditiveInvariant
#print axioms CohLean.RiemannRoch.CoherentAdditiveInvariant.freeHom
#print axioms CohLean.RiemannRoch.CoherentAdditiveInvariant.coherentGrothendieckRelations_le_ker
#print axioms CohLean.RiemannRoch.CoherentAdditiveInvariant.grothendieckHom
#print axioms CohLean.RiemannRoch.CoherentAdditiveInvariant.grothendieckHom_class
#print axioms CohLean.RiemannRoch.coherentGrothendieckGroup_hom_ext

-- Layer B stage 5: the scheme-derived surface numerical-variety assembly. The geometric HRR
-- input is stated on coherent sheaves; the audited theorem below descends it to every K₀ class.
#print axioms CohLean.RiemannRoch.Surface.CoherentAdditiveInvariant
#print axioms CohLean.RiemannRoch.Surface.CoherentAdditiveInvariant.freeHom
#print axioms CohLean.RiemannRoch.Surface.CoherentAdditiveInvariant.coherentGrothendieckRelations_le_ker
#print axioms CohLean.RiemannRoch.Surface.CoherentAdditiveInvariant.grothendieckHom
#print axioms CohLean.RiemannRoch.Surface.CoherentAdditiveInvariant.grothendieckHom_class
#print axioms CohLean.RiemannRoch.Surface.coherentGrothendieckGroup_hom_ext
#print axioms CohLean.RiemannRoch.Surface.ReconstructionSystem
#print axioms CohLean.RiemannRoch.Surface.ReconstructionSystem.rankInvariant
#print axioms CohLean.RiemannRoch.Surface.ReconstructionSystem.chernCharacterInvariant
#print axioms CohLean.RiemannRoch.Surface.ReconstructionSystem.rankHom
#print axioms CohLean.RiemannRoch.Surface.ReconstructionSystem.chernCharacterHom
#print axioms CohLean.RiemannRoch.Surface.ReconstructionSystem.rankHom_class
#print axioms CohLean.RiemannRoch.Surface.ReconstructionSystem.chernCharacterHom_class
#print axioms CohLean.RiemannRoch.Surface.ReconstructionSystem.chernCharacterHom_mem
#print axioms CohLean.RiemannRoch.Surface.ReconstructionSystem.intAlgebraMap
#print axioms CohLean.RiemannRoch.Surface.ReconstructionSystem.chernCharacterHom_zero
#print axioms CohLean.RiemannRoch.Surface.ReconstructionSystem.chernCharacterHom_add
#print axioms CohLean.RiemannRoch.Surface.GeometricData
#print axioms CohLean.RiemannRoch.Surface.GeometricData.totalChernCharacterHom
#print axioms CohLean.RiemannRoch.Surface.GeometricData.totalTodd
#print axioms CohLean.RiemannRoch.Surface.GeometricData.riemannRochHom
#print axioms CohLean.RiemannRoch.Surface.GeometricData.rationalEulerHom
#print axioms CohLean.RiemannRoch.Surface.GeometricData.totalChernCharacterHom_class
#print axioms CohLean.RiemannRoch.Surface.GeometricData.riemannRochHom_class
#print axioms CohLean.RiemannRoch.Surface.GeometricData.rationalEulerHom_class
#print axioms CohLean.RiemannRoch.Surface.GeometricData.hirzebruch_riemannRoch
#print axioms CohLean.RiemannRoch.Surface.GeometricData.toNumericalVariety
#print axioms CohLean.RiemannRoch.Surface.GeometricData.toNumericalVariety_rank_class
#print axioms CohLean.RiemannRoch.Surface.GeometricData.toNumericalVariety_chComp_class
#print axioms CohLean.RiemannRoch.Surface.GeometricData.toNumericalVariety_toddComp
#print axioms CohLean.RiemannRoch.Surface.GeometricData.toNumericalVariety_chi_class
#print axioms CohLean.RiemannRoch.Surface.GeometricData.surface_chi_class_eq
#print axioms CohLean.RiemannRoch.Surface.GeometricData.toIsK3
#print axioms CohLean.RiemannRoch.Surface.GeometricData.k3_eulerCharacteristic_eq
#print axioms CohLean.RiemannRoch.Surface.GeometricData.numericalClass

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
#print axioms NumericalVariety.discriminant_mem_piece_two
#print axioms NumericalVariety.degree_discriminant
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

-- Layer A: the numerical Grothendieck quotient and lattice. The pairing is descended only
-- under explicit symmetry, and the finite/free conclusion must retain its finiteness and
-- torsion-freeness hypotheses.
#print axioms ZLattice
#print axioms ZLattice.ofFiniteTorsionFree
#print axioms NumericalVariety.eulerPairingRow
#print axioms NumericalVariety.eulerPairing
#print axioms NumericalVariety.eulerPairingFlip
#print axioms NumericalVariety.eulerPairing_apply
#print axioms NumericalVariety.eulerPairingFlip_apply
#print axioms NumericalVariety.leftRadical
#print axioms NumericalVariety.rightRadical
#print axioms NumericalVariety.mem_leftRadical_iff
#print axioms NumericalVariety.mem_rightRadical_iff
#print axioms NumericalVariety.IsEulerPairingSymmetric
#print axioms NumericalVariety.leftRadical_eq_rightRadical
#print axioms NumericalVariety.NumericalQuotient
#print axioms NumericalVariety.eulerPairingDescendRight
#print axioms NumericalVariety.eulerPairingDescendRight_mk
#print axioms NumericalVariety.eulerPairingToQuotient
#print axioms NumericalVariety.eulerPairingToQuotient_mk
#print axioms NumericalVariety.numericalPairing
#print axioms NumericalVariety.numericalPairing_mk
#print axioms NumericalVariety.numericalPairing_symm
#print axioms NumericalVariety.numericalPairing_left_nondegenerate
#print axioms NumericalVariety.numericalPairing_right_nondegenerate
#print axioms NumericalVariety.numericalPairing_ker_eq_bot
#print axioms NumericalVariety.numericalZLattice
#print axioms K3.isEulerPairingSymmetric
#print axioms K3.leftRadical_eq_rightRadical
#print axioms K3.numericalPairing_mk_eq_neg_mukaiPairing

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

-- Layer B stage 1: Mathlib v4.32 provides Hartshorne II.5.1 upstream; retain the
-- compatibility exports consumed by the affine comparison layer.
#print axioms Scheme.Modules.isLocalizedModule_basicOpenRestriction_of_isQuasicoherent
#print axioms Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent

-- Layer B stage 1: the finiteness corollaries of the affine comparison. Finite local
-- generators and presentations are transported to affine basic opens, where the comparison
-- turns them into finite modules; localisation patching then returns to `Spec R`.
#print axioms SheafOfModules.GeneratingSections.map
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

-- Layer B stage 2: Cartier divisors as locally representable sections of
-- `K(X)ˣ / 𝒪_{X,x}ˣ`, principal equivalence, codimension-one coefficients,
-- and pullback from explicit compatible function-field data.
#print axioms Scheme.localCartierClass_eq_iff
#print axioms Scheme.isCartier_zero
#print axioms Scheme.IsCartier.add
#print axioms Scheme.IsCartier.neg
#print axioms Scheme.CartierDivisor.ext
#print axioms Scheme.CartierDivisor.zero_apply
#print axioms Scheme.CartierDivisor.add_apply
#print axioms Scheme.CartierDivisor.neg_apply
#print axioms Scheme.CartierDivisor.exists_localEquation
#print axioms Scheme.CartierDivisor.toClass_eq_iff
#print axioms Scheme.CartierDivisor.toClass_eq_iff_exists
#print axioms Scheme.CartierDivisor.toClass_principal
#print axioms Scheme.CartierDivisor.ordUnitHom_eq_zero_of_mem_localUnits
#print axioms Scheme.CartierDivisor.localOrder_localCartierClass
#print axioms Scheme.CartierDivisor.coefficient_add
#print axioms Scheme.CartierDivisor.coefficient_principal
#print axioms Scheme.CartierDivisor.coefficient_eq_zero_of_coheight_ne_one
#print axioms Scheme.CartierPullbackData.localMap_localCartierClass
#print axioms Scheme.CartierPullbackData.pullback_principal

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
-- CohLean/Cohomology/Simplicial/ExtraCodegeneracy.lean for what is still missing.
#print axioms AlgebraicTopology.AlternatingCofaceMapComplex.opIso
#print axioms AlgebraicTopology.AlternatingCofaceMapComplex.opIso_hom_f
#print axioms AlgebraicTopology.AlternatingCofaceMapComplex.opIso_inv_f
#print axioms AlgebraicTopology.exactAt_succ_of_extraDegeneracy
#print axioms AlgebraicTopology.exactAt_succ_of_extraDegeneracy_map

-- Layer B stage 3: Mathlib's construction assembling a spectral object into a spectral
-- sequence, including its page-homology and first-page comparison isomorphisms.
#print axioms CategoryTheory.Abelian.SpectralObject.SpectralSequence.HomologyData.isColimitCc
#print axioms CategoryTheory.Abelian.SpectralObject.SpectralSequence.homologyData
#print axioms CategoryTheory.Abelian.SpectralObject.spectralSequence
#print axioms CategoryTheory.Abelian.SpectralObject.spectralSequencePageXIso
#print axioms CategoryTheory.Abelian.SpectralObject.spectralSequence_page_d_eq
#print axioms CategoryTheory.Abelian.SpectralObject.spectralSequenceFirstPageXIso
#print axioms CategoryTheory.Abelian.SpectralObject.spectralSequence_first_page_d_eq

-- Layer B stage 3: filtered complexes and column-filtered total complexes now feed the
-- spectral-object constructor above.  The last declaration is the packaged E₂ sequence.
#print axioms CategoryTheory.Triangulated.SpectralObject.mapHomologicalFunctor
#print axioms HomotopyCategory.filteredComplexSpectralObject
#print axioms CategoryTheory.Abelian.SpectralObject.coreE₂CohomologicalInt
#print axioms CategoryTheory.Abelian.SpectralObject.coreE₂ColumnFilteredCohomologicalInt
#print axioms HomologicalComplex.stupidTruncGEι
#print axioms HomologicalComplex.stupidTruncGEMap
#print axioms HomologicalComplex₂.columnFiltrationBicomplex
#print axioms HomologicalComplex₂.columnFilteredTotalComplex
#print axioms HomologicalComplex₂.columnFilteredTotalι
#print axioms HomologicalComplex₂.columnFilteredTotal_map_comp_ι
#print axioms HomologicalComplex₂.columnFilteredTotalιNat
#print axioms HomologicalComplex₂.columnFilteredTotalSpectralObject
#print axioms HomologicalComplex₂.columnFilteredTotalSpectralSequence

-- Layer B stage 3: consecutive column truncations form a degreewise split short exact
-- sequence. Its totalized mapping cone is quasi-isomorphic to the newly added shifted column,
-- which identifies an adjacent filtration layer with fixed-column homology.
#print axioms HomologicalComplex₂.truncatedBicomplex
#print axioms HomologicalComplex₂.singleColumnBicomplex
#print axioms HomologicalComplex₂.singleColumnXIso
#print axioms HomologicalComplex₂.singleColumnXIso_hom_inv_f
#print axioms HomologicalComplex₂.singleColumnXIso_inv_hom_f
#print axioms HomologicalComplex₂.adjacentColumnInclusion
#print axioms HomologicalComplex₂.adjacentColumnProjection
#print axioms HomologicalComplex₂.adjacentColumnBicomplexShortComplex
#print axioms HomologicalComplex₂.totalFunctor_additive
#print axioms HomologicalComplex₂.adjacentColumnTotalShortComplex
#print axioms HomologicalComplex₂.stupidTruncGEXIso
#print axioms HomologicalComplex₂.stupidTruncXIso_eq_stupidTruncGEXIso
#print axioms HomologicalComplex₂.stupidTruncGEXIso_inv_hom_f
#print axioms HomologicalComplex₂.stupidTruncGEXIso_hom_inv_f
#print axioms HomologicalComplex₂.complexIso_inv_hom_f
#print axioms HomologicalComplex₂.complexIso_hom_inv_f
#print axioms HomologicalComplex₂.adjacentColumnTotalRetraction
#print axioms HomologicalComplex₂.adjacentColumnTotalSection
#print axioms HomologicalComplex₂.adjacentColumnTotalDegreewiseSplitting
#print axioms HomologicalComplex₂.singleZeroBicomplex
#print axioms HomologicalComplex₂.singleZeroXIso
#print axioms HomologicalComplex₂.singleZeroTotalXIso
#print axioms HomologicalComplex₂.singleZeroTotalIso
#print axioms HomologicalComplex₂.singleColumnShiftIso
#print axioms HomologicalComplex₂.singleColumnTotalIso
#print axioms HomologicalComplex₂.adjacentColumnTotalShortExact
#print axioms HomologicalComplex₂.adjacentColumnConeToShift
#print axioms HomologicalComplex₂.adjacentColumnConeToShift_quasiIso
#print axioms HomologicalComplex₂.columnFilteredAdjacentLayerComplex
#print axioms HomologicalComplex₂.columnFilteredAdjacentLayerComplex_eq
#print axioms HomologicalComplex₂.columnFilteredAdjacentLayerConeToShift
#print axioms HomologicalComplex₂.columnFilteredAdjacentLayerConeToShift_quasiIso
#print axioms HomologicalComplex₂.columnFilteredAdjacentLayerHomologyIso
#print axioms HomologicalComplex₂.columnFilteredStageIso
#print axioms HomologicalComplex₂.columnFilteredAdjacentLayerIso
#print axioms HomologicalComplex₂.columnFilteredInitialPageColumnHomologyIso
#print axioms HomologicalComplex₂.columnFilteredFirstPage_d_eq
#print axioms HomologicalComplex₂.columnFilteredInitialPage_d_eq_horizontalHomologyMap

-- Layer B stage 3: an explicit injective resolution now produces the augmented Cech
-- bicomplex, its total complex, the column-filtered spectral sequence, and the formal
-- initial-page identification. The pin still has no EnoughInjectives instance for sheaves
-- and no convergence/abutment field in SpectralSequence; neither gap is hidden by an axiom.
#print axioms CategoryTheory.Limits.FormalCoproduct.evalOp_additive
#print axioms CategoryTheory.Sheaf.cechComplexFunctor_additive
#print axioms CategoryTheory.Sheaf.cechCochainFunctorInt
#print axioms CategoryTheory.Sheaf.cechResolutionBicomplexUnflipped
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplex
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexXXIso
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexAugmentation
#print axioms CategoryTheory.Sheaf.cechInjectiveTotalComplex
#print axioms CategoryTheory.Sheaf.cechInjectiveFilteredToTotal
#print axioms CategoryTheory.Sheaf.cechInjectiveFilteredToTotalNat
#print axioms CategoryTheory.Sheaf.cechInjectiveSpectralObject
#print axioms CategoryTheory.Sheaf.cechInjectiveSpectralSequence
#print axioms CategoryTheory.Sheaf.cechInjectiveInitialPageXIso
#print axioms CategoryTheory.Sheaf.cechInjectiveAdjacentLayerComplex
#print axioms CategoryTheory.Sheaf.cechInjectiveAdjacentLayerHomologyIso
#print axioms CategoryTheory.Sheaf.cechInjectiveInitialPageColumnHomologyIso

-- Layer B stage 3: the initial page's degree-zero row, including its horizontal
-- differential, is the ordinary Cech complex. Consequently the following page is
-- ordinary Cech cohomology along that row.
#print axioms CategoryTheory.Sheaf.cechInjectiveColumnAugmentationHomologyIso
#print axioms CategoryTheory.Sheaf.cechInjectiveInitialPageZeroRowXIso
#print axioms CategoryTheory.Sheaf.cechInjectiveInitialPageZeroRow_d
#print axioms CategoryTheory.Sheaf.cechInjectiveInitialPageZeroRowIso
#print axioms CategoryTheory.Sheaf.cechInjectiveFollowingPageCechCohomologyIso

-- Layer B stage 3: first-quadrant total comparison and the Cech augmentation into the total
-- complex of an explicit injective resolution. The general engine uses finite column tails;
-- local Cech acyclicity supplies the columnwise quasi-isomorphisms.
#print axioms CochainComplex.mappingCone.quasiIso_compMap
#print axioms CochainComplex.mappingCone.quasiIsoAt_inr_of_isZero_X
#print axioms HomologicalComplex.HomologySequence.quasiIso_τ₂
#print axioms HomologicalComplex₂.IsVerticallyConnective
#print axioms HomologicalComplex₂.IsHorizontallyConnective
#print axioms HomologicalComplex₂.totalMap_quasiIso
#print axioms CategoryTheory.Sheaf.cechInjectiveColumnAugmentation_quasiIso
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexAugmentationSource_verticallyConnective
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexAugmentationSource_horizontallyConnective
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplex_verticallyConnective
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplex_horizontallyConnective
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexAugmentation_total_quasiIso
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexAugmentationSourceTotalIso
#print axioms CategoryTheory.Sheaf.cechToInjectiveTotalMap
#print axioms CategoryTheory.Sheaf.cechToInjectiveTotalMap_quasiIso
#print axioms CategoryTheory.Sheaf.cechCohomologyIsoInjectiveTotalHomology

-- Layer B stage 3: the global-sections edge of the Cech bicomplex. Sheaf gluing proves
-- exactness at degree zero, injectivity proves positive row exactness, and the resulting
-- rowwise quasi-isomorphism passes to first-quadrant totals. Together with local Cech
-- acyclicity this gives the full Cech-to-derived comparison for open covers.
#print axioms CategoryTheory.Sheaf.globalSectionsToCechZero_exact
#print axioms CategoryTheory.Sheaf.globalSectionsToCechZero_mono
#print axioms CategoryTheory.Sheaf.globalSectionsToCechRowMap_quasiIso
#print axioms CategoryTheory.Sheaf.globalSectionsToCechBicomplexMap
#print axioms CategoryTheory.Sheaf.injectiveResolutionSectionsToCechTotalMap
#print axioms CategoryTheory.Sheaf.injectiveResolutionSectionsToCechTotalMap_quasiIso
#print axioms CategoryTheory.Sheaf.cechCochainFunctorIntHomologyIso
#print axioms CategoryTheory.Sheaf.injectiveResolutionSectionsComplexUnliftedIso
#print axioms CategoryTheory.Sheaf.isCechAcyclicCover_cechComputesDerivedCohomology
#print axioms AlgebraicGeometry.Cohomology.AffineTildeCechDerivedComparisonAt
#print axioms AlgebraicGeometry.Cohomology.AffineTildeCechDerivedComparison
#print axioms AlgebraicGeometry.Cohomology.affineTildeCechDerivedComparisonAt_of_pos
#print axioms AlgebraicGeometry.Cohomology.tilde_H_subsingleton_of_comparisonAt
#print axioms AlgebraicGeometry.Cohomology.tilde_H_subsingleton_of_comparison
#print axioms AlgebraicGeometry.Cohomology.H_subsingleton_of_iso_tilde_of_comparisonAt
#print axioms AlgebraicGeometry.Cohomology.modules_H_subsingleton_of_iso_tilde_of_comparisonAt
#print axioms AlgebraicGeometry.Cohomology.tilde_H_subsingleton
#print axioms AlgebraicGeometry.Cohomology.H_subsingleton_of_iso_tilde
#print axioms AlgebraicGeometry.Cohomology.modules_H_subsingleton_of_iso_tilde
#print axioms AlgebraicGeometry.Cohomology.modules_H_subsingleton_of_isQuasicoherent

-- Layer B stage 3: the non-circular compact-basis comparison (Stacks, Tag 01EW).
-- Compact refinements and Cech correction make the acyclicity condition stable under
-- injective quotients, so dimension shifting kills positive derived cohomology.
#print axioms CategoryTheory.Sheaf.CompactOpenBasis
#print axioms CategoryTheory.Sheaf.CompactOpenBasis.ofIsBasis
#print axioms CategoryTheory.Sheaf.CompactOpenBasis.exists_finite_refinement
#print axioms CategoryTheory.Sheaf.IsCechAcyclicOnCompactBasis
#print axioms CategoryTheory.Sheaf.isCechAcyclicOnCompactBasis_of_injective
#print axioms CategoryTheory.Sheaf.epi_app_of_isCechAcyclicOnCompactBasis
#print axioms CategoryTheory.Sheaf.isCechAcyclicOnCompactBasis_quotient
#print axioms CategoryTheory.Sheaf.HPrime_subsingleton_of_isCechAcyclicOnCompactBasis
#print axioms CategoryTheory.Sheaf.H_subsingleton_of_isCechAcyclicOnCompactBasis

-- Layer B stage 3: positive-degree exactness of the explicit Cech complex for a module
-- sheaf on a finite distinguished-open cover of an affine scheme. This is the affine Cech
-- vanishing theorem, not a comparison with derived-functor sheaf cohomology.
#print axioms CategoryTheory.Sheaf.cechComplex_exactAt_succ_of_injective'
#print axioms CategoryTheory.cechComplex_exactAt_succ_of_isTerminal
#print axioms PrimeSpectrum.basicOpen_prod_eq_pi
#print axioms AlgebraicGeometry.tilde_cechComplex_exactAt_succ
#print axioms AlgebraicGeometry.tilde_cechComplex_exactAt_succ_of_eq_iSup
#print axioms AlgebraicGeometry.tilde_cechComplex_exactAt_of_pos

-- Layer B stage 3: bridge the relative distinguished-open calculation through the
-- underlying additive-group functor and specialize the compact-basis criterion to affine
-- schemes.
#print axioms CategoryTheory.evalOpForget₂AddCommGrpIso
#print axioms CategoryTheory.map_alternatingCofaceMapComplex
#print axioms CategoryTheory.cechComplexForget₂AddCommGrpIso
#print axioms CategoryTheory.cechComplex_exactAt_forget₂AddCommGrp_of_exactAt
#print axioms AlgebraicGeometry.Cohomology.affineBasicOpenBasis
#print axioms AlgebraicGeometry.Cohomology.top_mem_affineBasicOpenBasis
#print axioms AlgebraicGeometry.Cohomology.underlyingTilde_isCechAcyclicOnCompactBasis

-- Layer B stage 3: finite-cover cohomological boundedness. Local compact-basis dimension
-- shifting proves ambient `H'`-vanishing on affine opens; affine diagonal makes every finite
-- intersection affine; Mayer--Vietoris then gives a numerical bound for actual `Sheaf.H`.
#print axioms CategoryTheory.Sheaf.opensUnion
#print axioms CategoryTheory.Sheaf.IntersectionAcyclic
#print axioms CategoryTheory.Sheaf.HPrime_subsingleton_opensUnion_of_intersectionAcyclic
#print axioms AlgebraicGeometry.Cohomology.affineBasicOpenBasisAt
#print axioms AlgebraicGeometry.Cohomology.mem_affineBasicOpenBasisAt
#print axioms AlgebraicGeometry.Cohomology.modulesSpec_isCechAcyclicOnCompactBasis
#print axioms AlgebraicGeometry.Cohomology.modules_isCechAcyclicOn_affineBasicOpenBasisAt
#print axioms AlgebraicGeometry.Cohomology.modules_HPrime_subsingleton_of_isAffineOpen
#print axioms AlgebraicGeometry.Cohomology.modules_intersectionAcyclic_of_forall_isAffineOpen
#print axioms AlgebraicGeometry.Cohomology.finiteAffineCoverOpens
#print axioms AlgebraicGeometry.Cohomology.opensUnion_finiteAffineCoverOpens
#print axioms AlgebraicGeometry.Cohomology.isAffineOpen_of_mem_finiteAffineCoverOpens
#print axioms AlgebraicGeometry.Cohomology.cohomologicalBound
#print axioms AlgebraicGeometry.Cohomology.modules_H_subsingleton_of_cohomologicalBound
#print axioms AlgebraicGeometry.Cohomology.coherent_H_subsingleton_of_cohomologicalBound
#print axioms AlgebraicGeometry.Cohomology.FiniteDimensionalCohomology.toFiniteCohomology

-- Layer B stage 3: the first Cech-to-derived comparison layer. The terminal-object
-- natural isomorphism closes the explicit TODO in Mathlib's sheaf-cohomology API; the
-- singleton theorem is the first positive-degree case of the Leray comparison.
#print axioms CategoryTheory.cechCohomology_isZero_of_exactAt
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaPresheafIsoConstant
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaSheafIsoConstant
#print axioms CategoryTheory.Sheaf.HPrimeNatIsoH
#print axioms CategoryTheory.Sheaf.HPrimeAddEquivH
#print axioms CategoryTheory.Sheaf.subsingleton_HPrime_iff_H
#print axioms CategoryTheory.Sheaf.cechComputesDerivedCohomologyAt_singleton_terminal_of_pos

-- Layer B stage 3: sections of an explicit injective resolution compute the local `H'`
-- groups, and a fixed Cech column is their product over finite intersections. Local
-- acyclicity therefore kills every positive-resolution-degree column homology object.
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaPresheafHomAddEquiv
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaSheafHomAddEquiv
#print axioms CategoryTheory.Sheaf.sectionsAtFunctor
#print axioms CategoryTheory.Sheaf.injectiveResolutionSectionsComplex
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaHomComplexIsoSections
#print axioms CategoryTheory.Sheaf.injectiveResolutionSectionsCohomologyAddEquivHPrime
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexColumnXIso
#print axioms CategoryTheory.Sheaf.cechColumnSectionsComplex
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexColumnIsoSectionsComplex
#print axioms CategoryTheory.Sheaf.cechColumnSectionsComplex_exactAt
#print axioms CategoryTheory.Sheaf.cechInjectiveBicomplexColumn_exactAt_of_isCechAcyclicFor
#print axioms CategoryTheory.Sheaf.subsingleton_cechInjectiveBicomplexColumnHomology_of_isCechAcyclicFor
#print axioms CategoryTheory.Sheaf.isZero_cechInjectiveInitialPage_of_isCechAcyclicFor
#print axioms CategoryTheory.Sheaf.subsingleton_cechInjectiveInitialPage_of_isCechAcyclicFor

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

-- Layer B stage 2: invertible sheaves and the raw sheafified tensor product. The final
-- Picard group law waits on tensor/sheafification coherence; these declarations expose the
-- complete foundation without postulating that missing theorem.
#print axioms SheafOfModules.freePUnitIsoUnit
#print axioms SheafOfModules.LocalGeneratorsData.isRankOne_ofIso
#print axioms SheafOfModules.IsInvertible.ofIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorUnitLeftIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorUnitRightIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorCommIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorTripleAssocIso
#print axioms AlgebraicGeometry.Scheme.Modules.PicardClass.mk_eq_mk_iff

-- Layer B stage 2: tensor/sheafification descent for invertible sheaves. Local rank-one
-- trivializations make tensor preserve locally bijective maps; this supplies both comparison
-- orientations, restriction compatibility, tensor closure, and the sheafified associator.
#print axioms CategoryTheory.Presheaf.isLocallyInjective_of_coversTop
#print axioms SheafOfModules.LocalGeneratorsData.rankOneTrivialization
#print axioms SheafOfModules.isLocallySurjective_whiskerLeft
#print axioms SheafOfModules.isLocallyInjective_whiskerLeft_of_isoUnit
#print axioms SheafOfModules.isLocallyInjective_whiskerLeft_of_rankOneData
#print axioms SheafOfModules.W_whiskerLeft_of_rankOneData
#print axioms SheafOfModules.isIso_sheafification_map_whiskerLeft_of_rankOneData
#print axioms SheafOfModules.isIso_sheafification_map_whiskerRight_of_rankOneData
#print axioms SheafOfModules.isIso_sheafification_map_whiskerLeft_unit_of_rankOneData
#print axioms SheafOfModules.isIso_sheafification_map_whiskerRight_unit_of_rankOneData
#print axioms SheafOfModules.LocalGeneratorsData.rankOneTrivializationOver
#print axioms SheafOfModules.IsInvertible.of_trivializations
#print axioms AlgebraicGeometry.Scheme.Modules.overSheafificationComparison
#print axioms AlgebraicGeometry.Scheme.Modules.isIso_overSheafificationComparison
#print axioms AlgebraicGeometry.Scheme.Modules.overTensorPresheafIso
#print axioms AlgebraicGeometry.Scheme.Modules.tensorOverIsoOfTrivializations
#print axioms AlgebraicGeometry.Scheme.Modules.isInvertible_tensorObj
#print axioms AlgebraicGeometry.Scheme.Modules.tensorSheafificationComparisonLeft
#print axioms AlgebraicGeometry.Scheme.Modules.tensorSheafificationComparisonRight
#print axioms AlgebraicGeometry.Scheme.Modules.isIso_tensorSheafificationComparisonLeft
#print axioms AlgebraicGeometry.Scheme.Modules.isIso_tensorSheafificationComparisonRight
#print axioms AlgebraicGeometry.Scheme.Modules.tensorAssocIso

-- Layer B stage 2: the descended tensor product is coherently symmetric monoidal on
-- invertible sheaves, and its skeleton yields the Picard group. Pentagon and both hexagons
-- reduce to the corresponding presheaf identities; no coherence law is postulated.
#print axioms AlgebraicGeometry.Scheme.Modules.tensorSheafificationComparisonRight_naturality
#print axioms AlgebraicGeometry.Scheme.Modules.tensorSheafificationComparisonLeft_naturality
#print axioms AlgebraicGeometry.Scheme.Modules.tensorAssocIso_naturality
#print axioms AlgebraicGeometry.Scheme.Modules.tensorHom_id_id
#print axioms AlgebraicGeometry.Scheme.Modules.tensorHom_comp_tensorHom
#print axioms AlgebraicGeometry.Scheme.Modules.tensorSheafificationComparisonRight_comp_tensorAssocIso
#print axioms AlgebraicGeometry.Scheme.Modules.invertibleSheafMonoidalCategoryStruct
#print axioms AlgebraicGeometry.Scheme.Modules.invertibleSheafMonoidalCategory
#print axioms AlgebraicGeometry.Scheme.Modules.tensorCommIso_naturality
#print axioms AlgebraicGeometry.Scheme.Modules.tensorCommIso_symmetry
#print axioms AlgebraicGeometry.Scheme.Modules.tensorCommIso_inv
#print axioms AlgebraicGeometry.Scheme.Modules.invertibleSheafBraidedCategory
#print axioms AlgebraicGeometry.Scheme.Modules.invertibleSheafSymmetricCategory
#print axioms AlgebraicGeometry.Scheme.Modules.picardClassCommMonoid
#print axioms AlgebraicGeometry.Scheme.Modules.PicardClass.one_eq_one
#print axioms AlgebraicGeometry.Scheme.Modules.PicardClass.mk_mul_mk
#print axioms AlgebraicGeometry.Scheme.Modules.Pic.mkOfTensorInverse
#print axioms AlgebraicGeometry.Scheme.Modules.Pic.coe_mkOfTensorInverse
#print axioms AlgebraicGeometry.Scheme.Modules.Pic.coe_one

-- Layer B stage 2: the fractional presheaf and associated invertible sheaf of a Cartier
-- divisor. Local equations give the trivializations; multiplication of rational functions
-- is a locally bijective map and therefore an isomorphism after module sheafification.
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.IsEquationOn
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.IsEquationOn.mono
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.fractionalPresheaf
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.associatedSheaf
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.equationIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.equationTransitionIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.equationTransitionIso_trans
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.associatedSheaf_isInvertible
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.multiplicationHom
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.fractionalTensorAddIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.associatedTensorAddIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.globalEquationIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.associatedSheafZeroIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.associatedSheafPrincipalIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.associatedTensorInverseIso
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.toPic
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.coe_toPic
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.divisorToPicAdd
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.divisorToPicAdd_apply
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.divisorToPicAdd_principal
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.classToPicAdd
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.classToPic
#print axioms AlgebraicGeometry.Scheme.CartierDivisor.classToPic_toClass

-- Layer B stage 2: effective Cartier divisors and their fundamental exact sequences.
-- Tensoring by an invertible sheaf is exact, so the normalized twist is directly reusable
-- as `O_X(E-D) → O_X(E) → O_X(E) ⊗ i_* O_D`; both sequences lift to `Coh X`
-- under explicit coherence hypotheses.
#print axioms AlgebraicGeometry.Scheme.IdealSheafData.quotientMap
#print axioms AlgebraicGeometry.Scheme.Modules.tensorLeftFunctor
#print axioms AlgebraicGeometry.Scheme.Modules.mono_tensorHom_id_of_invertible
#print axioms AlgebraicGeometry.Scheme.Modules.shortExact_map_tensorLeft_of_invertible
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.structureSheaf
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.quotient
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.idealInclusion
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.fundamentalSequence
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.fundamentalSequence_shortExact
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.cokernelIsoStructureSheaf
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistedStructureSheaf
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistSourceIso
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistMiddleIso
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistedIdealInclusion
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistedQuotient
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistSequence
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistSequence_shortExact
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistCokernelIso
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.structureSheaf_isCoherent
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.cohFundamentalSequence
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.cohFundamentalSequence_shortExact
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.twistedStructureSheaf_isCoherent
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.cohTwistSequence
#print axioms AlgebraicGeometry.Scheme.EffectiveCartierDivisor.cohTwistSequence_shortExact

-- Layer B stage 2: determinant lines and first Chern classes. Mathlib supplies the local
-- module exterior power but not exterior powers of sheaves, so global descent and exact
-- comparison are explicit certificates. The coherent extension requires either finite locally
-- free determinant data or a visible two-term finite locally free resolution.
#print axioms Module.finrank_topExteriorPower
#print axioms AlgebraicGeometry.Scheme.Modules.FiniteLocallyFreeData
#print axioms AlgebraicGeometry.Scheme.Modules.FiniteLocallyFreeData.isLocallyFree
#print axioms AlgebraicGeometry.Scheme.Modules.FiniteLocallyFreeData.ofIso
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.toPic
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.coe_toPic
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.toPic_eq_of_iso
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.dual
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.tensor
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.toPic_dual
#print axioms AlgebraicGeometry.Scheme.Modules.LineBundleData.toPic_tensor
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.isLocallyFree
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.ofIso
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.firstChernClass
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.firstChernClassAdd
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.firstChernClass_ofIso
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.firstChernClassAdd_ofIso
#print axioms AlgebraicGeometry.Scheme.Modules.DeterminantData.firstChernClass_eq_of_lineIso
#print axioms AlgebraicGeometry.Scheme.Modules.DirectSumDeterminantData
#print axioms AlgebraicGeometry.Scheme.Modules.DirectSumDeterminantData.firstChernClass_eq_mul
#print axioms AlgebraicGeometry.Scheme.Modules.DirectSumDeterminantData.firstChernClassAdd_eq_add
#print axioms AlgebraicGeometry.Scheme.Modules.ShortExactDeterminantData
#print axioms AlgebraicGeometry.Scheme.Modules.ShortExactDeterminantData.firstChernClass_eq_mul
#print axioms AlgebraicGeometry.Scheme.Modules.ShortExactDeterminantData.firstChernClassAdd_eq_add
#print axioms AlgebraicGeometry.Coh.ShortExactDeterminantData
#print axioms AlgebraicGeometry.Coh.ShortExactDeterminantData.toModules
#print axioms AlgebraicGeometry.Coh.ShortExactDeterminantData.firstChernClassAdd_eq_add
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData.determinantLine
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData.firstChernClass
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData.firstChernClassAdd
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData.firstChernClass_eq
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData.ofIso
#print axioms AlgebraicGeometry.Coh.TwoTermPerfectDeterminantData.firstChernClass_ofIso
#print axioms AlgebraicGeometry.Coh.PerfectShortExactDeterminantData
#print axioms AlgebraicGeometry.Coh.PerfectShortExactDeterminantData.firstChernClassAdd_eq_add

-- Layer B stage 4: dimension-general numerical-polynomial algebra and its geometric Snapper
-- bridge. The geometric induction and missing closure theorem are visible structure fields,
-- never hidden axioms.
#print axioms CohLean.Intersection.NumericalPolynomial.difference
#print axioms CohLean.Intersection.NumericalPolynomial.difference_comm
#print axioms CohLean.Intersection.NumericalPolynomial.difference_add_direction
#print axioms CohLean.Intersection.NumericalPolynomial.coordinateDifference
#print axioms CohLean.Intersection.NumericalPolynomial.mixedDifference
#print axioms CohLean.Intersection.NumericalPolynomial.mixedDifference_difference
#print axioms CohLean.Intersection.NumericalPolynomial.mixedDifference_eq_of_perm
#print axioms CohLean.Intersection.NumericalPolynomial.DegreeLE
#print axioms CohLean.Intersection.NumericalPolynomial.degreeLE_iff_fin
#print axioms CohLean.Intersection.NumericalPolynomial.DegreeLE.add
#print axioms CohLean.Intersection.NumericalPolynomial.DegreeLE.succ
#print axioms CohLean.Intersection.NumericalPolynomial.DegreeLE.mono
#print axioms CohLean.Intersection.NumericalPolynomial.DegreeLE.difference
#print axioms CohLean.Intersection.NumericalPolynomial.coefficient
#print axioms CohLean.Intersection.NumericalPolynomial.coefficient_eq_of_perm
#print axioms CohLean.Intersection.NumericalPolynomial.topCoefficient
#print axioms CohLean.Intersection.NumericalPolynomial.topCoefficient_comp_perm
#print axioms CohLean.Intersection.NumericalPolynomial.coordinateDirections
#print axioms CohLean.Intersection.NumericalPolynomial.newtonCoefficient
#print axioms CohLean.Intersection.NumericalPolynomial.mixedDifference_eq_coefficient_of_degreeLE
#print axioms CohLean.Intersection.NumericalPolynomial.coefficient_cons_add
#print axioms CohLean.Intersection.NumericalPolynomial.coefficient_middle_add
#print axioms CohLean.Intersection.NumericalPolynomial.coefficientAddHom
#print axioms CohLean.Intersection.NumericalPolynomial.coefficient_middle_zsmul
#print axioms CohLean.Intersection.NumericalPolynomial.mixedDifference_oneVariable
#print axioms CohLean.Intersection.NumericalPolynomial.oneVariable_fwdDiff_vanishes
#print axioms CohLean.Intersection.NumericalPolynomial.coefficient_oneVariable
#print axioms CohLean.Intersection.NumericalPolynomial.surfacePairing
#print axioms CohLean.Intersection.NumericalPolynomial.surfacePairing_symm
#print axioms CohLean.Intersection.Snapper.picardPower
#print axioms CohLean.Intersection.Snapper.linePower
#print axioms CohLean.Intersection.Snapper.linePower_picardClass
#print axioms CohLean.Intersection.Snapper.twistModules
#print axioms CohLean.Intersection.Snapper.CoherentTwistFamily
#print axioms CohLean.Intersection.Snapper.eulerFunction
#print axioms CohLean.Intersection.Snapper.GeometricInduction
#print axioms CohLean.Intersection.Snapper.GeometricInduction.difference_descendedEuler
#print axioms CohLean.Intersection.Snapper.GeometricInduction.mixedDifference_eulerFunction
#print axioms CohLean.Intersection.Snapper.eulerCharacteristic_isZero
#print axioms CohLean.Intersection.Snapper.snapper
#print axioms CohLean.Intersection.Snapper.mixedDifference_eq_euler_descended
#print axioms CohLean.Intersection.Snapper.coefficient_eq_euler_descended
#print axioms CohLean.Intersection.Snapper.eulerFunction_eq_of_coherentSheafIso
#print axioms CohLean.Intersection.Snapper.eulerFunction_eq_of_lineBundleIso
#print axioms CohLean.Intersection.Snapper.oneVariable_fwdDiff_euler_vanishes
#print axioms CohLean.Intersection.Number.picardDifference
#print axioms CohLean.Intersection.Number.picardMixedDifference
#print axioms CohLean.Intersection.Number.picardCoefficient
#print axioms CohLean.Intersection.Number.PicardDegreeLE
#print axioms CohLean.Intersection.Number.picardCoefficient_middle_mul
#print axioms CohLean.Intersection.Number.picardCoefficientAddHom
#print axioms CohLean.Intersection.Number.picardMonomial
#print axioms CohLean.Intersection.Number.mixedDifference_picardPolynomial
#print axioms CohLean.Intersection.Number.TwistContext
#print axioms CohLean.Intersection.Number.TwistContext.picardDegreeLE
#print axioms CohLean.Intersection.Number.IntersectionContext
#print axioms CohLean.Intersection.Number.IntersectionContext.picardIntersectionNumber
#print axioms CohLean.Intersection.Number.IntersectionContext.picardIntersectionNumber_eq_coefficient
#print axioms CohLean.Intersection.Number.IntersectionContext.picardIntersectionNumber_comp_perm
#print axioms CohLean.Intersection.Number.IntersectionContext.picardIntersectionList_middle_mul
#print axioms CohLean.Intersection.Number.IntersectionContext.cartierClassIntersectionNumber
#print axioms CohLean.Intersection.Number.IntersectionContext.cartierDivisorIntersectionNumber_eq_picard
#print axioms CohLean.Intersection.Number.IntersectionContext.surfaceIntersectionPairing
#print axioms CohLean.Intersection.Number.IntersectionContext.surfaceIntersectionPairing_symm

-- Layer B stage 5: geometric surface divisor Riemann--Roch. These declarations use Serre
-- symmetry, Snapper intersections, and #25's effective sequence, never Layer A's HRR field.
#print axioms CohLean.RiemannRoch.Surface.correctionNumerator
#print axioms CohLean.RiemannRoch.Surface.twice_eulerPic_sub
#print axioms CohLean.RiemannRoch.Surface.correctionNumerator_even
#print axioms CohLean.RiemannRoch.Surface.eulerPic_eq
#print axioms CohLean.RiemannRoch.Surface.cartierEulerCharacteristic
#print axioms CohLean.RiemannRoch.Surface.cartierCorrectionNumerator
#print axioms CohLean.RiemannRoch.Surface.cartier_eulerCharacteristic_eq
#print axioms CohLean.RiemannRoch.Surface.cartierCorrectionNumerator_even
#print axioms CohLean.RiemannRoch.Surface.cartierEulerCharacteristic_eq_of_principalEquivalent
#print axioms CohLean.RiemannRoch.Surface.cartier_formula_eq_of_principalEquivalent
#print axioms CohLean.RiemannRoch.Surface.EffectiveSequenceRealization
#print axioms CohLean.RiemannRoch.Surface.EffectiveSequenceRealization.euler_additivity
#print axioms CohLean.RiemannRoch.Surface.EffectiveSequenceRealization.effective_euler_additivity
#print axioms CohLean.RiemannRoch.Surface.EffectiveSequenceRealization.effective_divisor_formula
#print axioms CohLean.RiemannRoch.Surface.EffectiveSequenceRealization.quotient_eulerCharacteristic_eq_half_correction
#print axioms CohLean.RiemannRoch.Surface.eulerPic_one
#print axioms CohLean.RiemannRoch.Surface.eulerPic_canonical
#print axioms CohLean.RiemannRoch.Surface.k3_eulerPic_eq
#print axioms CohLean.RiemannRoch.Surface.k3_eulerPic_eq_two

-- Layer B stage 5: surface Todd reconstruction. The top representative comes from the
-- structure-sheaf twist polynomial, and the first component is the explicit class -K/2.
#print axioms CohLean.RiemannRoch.Surface.ToddData.Data
#print axioms CohLean.RiemannRoch.Surface.ToddData.numericalCanonicalClass
#print axioms CohLean.RiemannRoch.Surface.ToddData.homogeneousPicardCoefficient_nil
#print axioms CohLean.RiemannRoch.Surface.ToddData.homogeneousPicardCoefficient_singleton
#print axioms CohLean.RiemannRoch.Surface.ToddData.toddComponent
#print axioms CohLean.RiemannRoch.Surface.ToddData.toddComponent_mem
#print axioms CohLean.RiemannRoch.Surface.ToddData.degree_toddTwo_eq_eulerPic_one
#print axioms CohLean.RiemannRoch.Surface.ToddData.degree_toddTwo_eq_structureSheafEulerCharacteristic
#print axioms CohLean.RiemannRoch.Surface.ToddData.degree_toddOne_mul_divisorClass
#print axioms CohLean.RiemannRoch.Surface.ToddData.structureToddOne_eq_toddOne
#print axioms CohLean.RiemannRoch.Surface.ToddData.toddOne_eq_zero
#print axioms CohLean.RiemannRoch.Surface.ToddData.degree_toddTwo_eq_two
#print axioms CohLean.RiemannRoch.Surface.ToddData.NumericalVarietyComparison.toIsK3

-- Layer B stage 5: finite locally free and explicitly perfect surface dévissage. Arbitrary
-- coherent sheaves receive no hidden resolution instance.
#print axioms CohLean.RiemannRoch.Surface.Devissage.locallyFreeCh2Degree
#print axioms CohLean.RiemannRoch.Surface.Devissage.locallyFreeC2Degree
#print axioms CohLean.RiemannRoch.Surface.Devissage.locallyFree_eulerCharacteristic_eq
#print axioms CohLean.RiemannRoch.Surface.Devissage.locallyFreeCh2Degree_shortExact
#print axioms CohLean.RiemannRoch.Surface.Devissage.locallyFreeC2Degree_shortExact
#print axioms CohLean.RiemannRoch.Surface.Devissage.eulerCharacteristic_eq_middle_sub_left
#print axioms CohLean.RiemannRoch.Surface.Devissage.chernCharacterTwoDegree_eq_middle_sub_left
#print axioms CohLean.RiemannRoch.Surface.Devissage.perfectC2Degree
#print axioms CohLean.RiemannRoch.Surface.Devissage.perfect_eulerCharacteristic_eq
#print axioms CohLean.RiemannRoch.Surface.Devissage.discriminantDegree_eq_c2
#print axioms CohLean.RiemannRoch.Surface.Devissage.coherentGrothendieckClass_shortExact
#print axioms CohLean.RiemannRoch.Surface.Devissage.grothendieckEulerHom_class_eq_perfect_formula
#print axioms CohLean.RiemannRoch.Surface.Devissage.NumericalVarietyComparison.chi_eq_geometric_terms
#print axioms CohLean.RiemannRoch.Surface.Devissage.NumericalVarietyComparison.chi_eq_classical

-- Layer B stage 5: final geometric assembly. Reconstruction proves HRR for every coherent
-- sheaf; the classical rank/c₁/c₂ interpretation remains conditional on an explicitly
-- supplied two-term finite locally free resolution.
#print axioms CohLean.RiemannRoch.Surface.Assembly.reconstruction_eulerPic_one
#print axioms CohLean.RiemannRoch.Surface.Assembly.degree_tauComponent_two_eq_eulerCharacteristic
#print axioms CohLean.RiemannRoch.Surface.Assembly.sheaf_hirzebruch_riemannRoch
#print axioms CohLean.RiemannRoch.Surface.Assembly.toGeometricData
#print axioms CohLean.RiemannRoch.Surface.Assembly.toNumericalVariety
#print axioms CohLean.RiemannRoch.Surface.Assembly.PerfectReconstructionComparison
#print axioms CohLean.RiemannRoch.Surface.Assembly.perfect_rank_eq
#print axioms CohLean.RiemannRoch.Surface.Assembly.perfect_toddTwo_degree
#print axioms CohLean.RiemannRoch.Surface.Assembly.perfect_toddOne_degree
#print axioms CohLean.RiemannRoch.Surface.Assembly.perfect_chTwo_degree
#print axioms CohLean.RiemannRoch.Surface.Assembly.perfect_surface_expansion
#print axioms CohLean.RiemannRoch.Surface.Assembly.perfect_chi_eq_classical
#print axioms CohLean.RiemannRoch.Surface.Assembly.toIsK3
#print axioms CohLean.RiemannRoch.Surface.Assembly.k3_eulerCharacteristic_eq

-- Layer B stage 5: numerical HRR in positive dimensions through four. Representability and
-- divisor-pairing separation remain visible in `PairingContext`; no cycle-valued GRR theorem is
-- assumed. The dimension-three and dimension-four constructors discharge the Layer A HRR field.
#print axioms CohLean.RiemannRoch.HigherDimension.reconstruction_eulerPic_one
#print axioms CohLean.RiemannRoch.HigherDimension.degree_tauComponent_top_eq_eulerCharacteristic
#print axioms CohLean.RiemannRoch.HigherDimension.ReconstructionSystem
#print axioms CohLean.RiemannRoch.HigherDimension.ReconstructionSystem.rankInvariant
#print axioms CohLean.RiemannRoch.HigherDimension.ReconstructionSystem.chernCharacterInvariant
#print axioms CohLean.RiemannRoch.HigherDimension.ReconstructionSystem.rankHom
#print axioms CohLean.RiemannRoch.HigherDimension.ReconstructionSystem.chernCharacterHom
#print axioms CohLean.RiemannRoch.HigherDimension.ReconstructionSystem.chernCharacterHom_zero
#print axioms CohLean.RiemannRoch.HigherDimension.reconstructedToddComponent
#print axioms CohLean.RiemannRoch.HigherDimension.reconstructedToddComponent_mem
#print axioms CohLean.RiemannRoch.HigherDimension.sheaf_hirzebruch_riemannRoch
#print axioms CohLean.RiemannRoch.HigherDimension.hirzebruch_riemannRoch
#print axioms CohLean.RiemannRoch.HigherDimension.toNumericalVariety
#print axioms CohLean.RiemannRoch.HigherDimension.numericalClass
#print axioms CohLean.RiemannRoch.HigherDimension.toThreefoldNumericalVariety
#print axioms CohLean.RiemannRoch.HigherDimension.toFourfoldNumericalVariety
#print axioms CohLean.RiemannRoch.HigherDimension.threefold_eulerCharacteristic_eq
#print axioms CohLean.RiemannRoch.HigherDimension.fourfold_eulerCharacteristic_eq

-- Layer B stage 4: degree-level surface Chern data. The construction uses determinants,
-- Picard intersections, and Euler characteristics; it does not postulate a Chow-valued class
-- or a perfect numerical pairing.
#print axioms CohLean.Intersection.ChernCharacterSurface.virtualRank
#print axioms CohLean.Intersection.ChernCharacterSurface.picardFirstChernClass
#print axioms CohLean.Intersection.ChernCharacterSurface.numericalFirstChernClass
#print axioms CohLean.Intersection.ChernCharacterSurface.toddOnePairing
#print axioms CohLean.Intersection.ChernCharacterSurface.toddTwoDegree
#print axioms CohLean.Intersection.ChernCharacterSurface.chernCharacterTwoDegree
#print axioms CohLean.Intersection.ChernCharacterSurface.surfaceChernCharacter
#print axioms CohLean.Intersection.ChernCharacterSurface.eulerCharacteristic_eq_rank_mul_toddTwo_add_toddOne_add_chernCharacterTwo
#print axioms CohLean.Intersection.ChernCharacterSurface.chernCharacterTwoDegree_ofIso
#print axioms CohLean.Intersection.ChernCharacterSurface.picardFirstChernClass_shortExact
#print axioms CohLean.Intersection.ChernCharacterSurface.numericalFirstChernClass_shortExact
#print axioms CohLean.Intersection.ChernCharacterSurface.chernCharacterTwoDegree_shortExact
#print axioms CohLean.Intersection.ChernCharacterSurface.chernCharacterTwoDegree_structureSheaf
#print axioms CohLean.Intersection.ChernCharacterSurface.eulerPic_one_eq_eulerCharacteristic_structureSheaf
#print axioms CohLean.Intersection.ChernCharacterSurface.toddTwoDegree_eq_eulerPic_one
#print axioms CohLean.Intersection.ChernCharacterSurface.chernCharacterTwoDegree_lineBundle
#print axioms CohLean.Intersection.ChernCharacterSurface.discriminantDegree
#print axioms CohLean.Intersection.ChernCharacterSurface.discriminantDegree_eq_numericalVariety

-- Layer B stage 4: bounded numerical-ring reconstruction. Existence of representatives and
-- separation by divisor products are fields of the input structures, not hidden axioms.
#print axioms CohLean.Intersection.ChernCharacter.homogeneousPicardCoefficient
#print axioms CohLean.Intersection.ChernCharacter.picardMixedDifference_add
#print axioms CohLean.Intersection.ChernCharacter.picardCoefficient_add
#print axioms CohLean.Intersection.ChernCharacter.scaledPicardCoefficient_add
#print axioms CohLean.Intersection.ChernCharacter.interpolatingPolynomial_add
#print axioms CohLean.Intersection.ChernCharacter.homogeneousPicardCoefficient_add
#print axioms CohLean.Intersection.ChernCharacter.scaledPicardCoefficient_eq_of_perm
#print axioms CohLean.Intersection.ChernCharacter.homogeneousPicardCoefficient_eq_of_perm
#print axioms CohLean.Intersection.ChernCharacter.divisorProduct_nil
#print axioms CohLean.Intersection.ChernCharacter.PairingContext
#print axioms CohLean.Intersection.ChernCharacter.PairingContext.ReconstructionData
#print axioms CohLean.Intersection.ChernCharacter.PairingContext.ReconstructionData.tauComponent
#print axioms CohLean.Intersection.ChernCharacter.PairingContext.ReconstructionData.tauComponent_mem
#print axioms CohLean.Intersection.ChernCharacter.PairingContext.ReconstructionData.degree_tauComponent_mul_divisorProduct
#print axioms CohLean.Intersection.ChernCharacter.PairingContext.ReconstructionData.tauComponent_eq_of_twistPairing_eq
#print axioms CohLean.Intersection.ChernCharacter.PairingContext.ReconstructionData.tauComponent_eq_of_eulerPic_eq
#print axioms CohLean.Intersection.ChernCharacter.PairingContext.ReconstructionData.tauComponent_add
#print axioms CohLean.Intersection.ChernCharacter.toddComponent
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent_zero
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent_one
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent_two
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent_three
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent_four
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent_of_five_le
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent_mem
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent_eq_zero_of_dimension_lt
#print axioms CohLean.Intersection.ChernCharacter.tauComponent_one_eq
#print axioms CohLean.Intersection.ChernCharacter.tauComponent_two_eq
#print axioms CohLean.Intersection.ChernCharacter.tauComponent_three_eq
#print axioms CohLean.Intersection.ChernCharacter.tauComponent_four_eq
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent_eq_of_eulerPic_eq
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent_iso
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent_add
#print axioms CohLean.Intersection.ChernCharacter.LineBundleComparison
#print axioms CohLean.Intersection.ChernCharacter.tauComponent_eq_lineTauCandidate
#print axioms CohLean.Intersection.ChernCharacter.chernCharacterComponent_lineBundle
#print axioms CohLean.Intersection.ChernCharacter.degree_chernCharacterComponent_two_eq_surface
#print axioms CohLean.Intersection.ChernCharacter.toChernClassData

-- Cohomology strategy: `CohLean/Development/Cohomology/Strategy.lean` contributes nothing here on
-- purpose. It is the compile-only API map for the B3 route decision and declares only
-- `example`s, which are anonymous and cannot be audited. Its guarantee is that it builds:
-- if an upstream declaration it names moves, `lake build` fails. The first real B3
-- theorem goes below this line.
#print axioms CategoryTheory.Sheaf.isFlasque_of_injective
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaSheafMap_stalk_isIso
#print axioms CategoryTheory.Sheaf.freeAbelianYonedaSheaf_stalk_isZero_of_not_mem
#print axioms CategoryTheory.Sheaf.cechComplex_exactAt_succ_of_injective
