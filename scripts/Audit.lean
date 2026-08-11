/-
Axiom + sorry audit over every declaration this project introduces.

Run: `lake env lean scripts/Audit.lean` (to read the output), or `lake build`
(to check it still elaborates).

Part of the library build since 2026-08-04: `[[lean_lib]] name = "Audit"` with
`srcDir = "scripts"`, in `defaultTargets`. Its output backs the `fidelity`
block of `formalization.yaml`; re-run it before editing that block, and paste
what it actually prints.

Being in the build is not the same as being a gate. `#print axioms` prints
`[sorryAx]` and exits 0, so a sorry-backed declaration builds green here. What
the build now catches is this file falling behind the source tree in one
direction only -- see below.

Reading the output: a declaration is clean iff its axiom list is a subset of
[propext, Classical.choice, Quot.sound]. Any other name -- above all
`sorryAx` -- is a failure, not a note.

Adding a declaration to the library means adding it here. This file is not
derived from the source tree, so it can silently fall behind; `#print axioms`
on a name that no longer exists is a hard error, but a name never added is
invisible.
-/
import BridgelandStabLean

open BridgelandStabLean

/-! ## ForMathlib — results Mathlib lacks at the pin -/

#print axioms Matrix.polarFactor
#print axioms Matrix.polarFactor_posSemidef
#print axioms Matrix.polarFactor_mul_self
#print axioms Matrix.polarFactor_isHermitian
#print axioms Matrix.det_polarFactor_ne_zero
#print axioms Matrix.polarFactor_posDef
#print axioms Matrix.polarUnitary
#print axioms Matrix.polarUnitary_mul_polarFactor
#print axioms Matrix.polarUnitary_mem_unitaryGroup
#print axioms Matrix.exists_polarDecomposition
#print axioms Matrix.eq_polarFactor_of_mul
#print axioms Matrix.eq_polarUnitary_of_mul
#print axioms Matrix.existsUnique_polarDecomposition

/-! ## Lattice lane -/

#print axioms Lattice.eq_zero_of_zsmul_eq_zero
#print axioms Lattice.eq_zero_of_two_zsmul_eq_zero
#print axioms Lattice.zsmul_injective
#print axioms Lattice.zsmul_left_cancel
#print axioms Lattice.finrank_numLattice
#print axioms Lattice.ne_zero_of_apply_ne_zero
#print axioms Lattice.eq_zero_of_two_zsmul_eq_zero_num

/-! ## GroupAction lane — NormalizedShift (step 1) -/

#print axioms GroupAction.NormalizedShift
#print axioms GroupAction.NormalizedShift.toOrderIso_injective
#print axioms GroupAction.NormalizedShift.ext'
#print axioms GroupAction.NormalizedShift.symm_map_add_one
#print axioms GroupAction.NormalizedShift.group
#print axioms GroupAction.NormalizedShift.mul_apply
#print axioms GroupAction.NormalizedShift.one_apply
#print axioms GroupAction.NormalizedShift.inv_apply

/-! ## GroupAction lane — ShiftAnalysis (step 3c groundwork) -/

#print axioms GroupAction.NormalizedShift.map_add_nat
#print axioms GroupAction.NormalizedShift.map_sub_nat
#print axioms GroupAction.NormalizedShift.map_add_int
#print axioms GroupAction.NormalizedShift.uniformContinuous
#print axioms GroupAction.NormalizedShift.exists_radius

/-! ## GroupAction lane — GLTilde (step 2) -/

#print axioms GroupAction.rayVec
#print axioms GroupAction.rayVec_add_one
#print axioms GroupAction.rayVec_ne_zero
#print axioms GroupAction.OnRay
#print axioms GroupAction.OnRay.refl
#print axioms GroupAction.OnRay.trans
#print axioms GroupAction.toMat
#print axioms GroupAction.toMat_mul
#print axioms GroupAction.toMat_one
#print axioms GroupAction.Compatible
#print axioms GroupAction.compat_one
#print axioms GroupAction.compat_mul
#print axioms GroupAction.compat_inv
#print axioms GroupAction.GLTilde
#print axioms GroupAction.GLTilde.ext'
#print axioms GroupAction.GLTilde.group
#print axioms GroupAction.GLTilde.mul_mat
#print axioms GroupAction.GLTilde.mul_shift
#print axioms GroupAction.GLTilde.one_mat
#print axioms GroupAction.GLTilde.one_shift
#print axioms GroupAction.GLTilde.inv_mat
#print axioms GroupAction.GLTilde.inv_shift
#print axioms GroupAction.GLTilde.toMatHom
#print axioms GroupAction.GLTilde.toShiftHom

/-! ## GroupAction lane — ComplexBridge (step 3 groundwork) -/

#print axioms GroupAction.cplxCoord
#print axioms GroupAction.cplxCoord_exp
#print axioms GroupAction.compat_exp
#print axioms GroupAction.actC
#print axioms GroupAction.actC_apply
#print axioms GroupAction.actC_one
#print axioms GroupAction.actC_mul
#print axioms GroupAction.actC_exp

/-! ## GroupAction lane — SlicingAction (step 3a) -/

#print axioms GroupAction.relabel
#print axioms GroupAction.relabel_P
#print axioms GroupAction.slicingMulAction
#print axioms GroupAction.smul_slicing_P
#print axioms GroupAction.gltildeSlicingMulAction
#print axioms GroupAction.gltilde_smul_slicing_P
#print axioms GroupAction.relabel_intervalProp_iff
#print axioms GroupAction.relabel_intervalProp

/-! ## GroupAction lane — PreStabilityAction (step 3b) -/

#print axioms GroupAction.actPre
#print axioms GroupAction.actPre_slicing
#print axioms GroupAction.actPre_Z
#print axioms GroupAction.preMulAction
#print axioms GroupAction.smul_pre_slicing
#print axioms GroupAction.smul_pre_Z

/-! ## GroupAction lane — StabilityAction (step 3c) -/

#print axioms GroupAction.relabel_isLocallyFinite
#print axioms GroupAction.actStab
#print axioms GroupAction.actStab_slicing
#print axioms GroupAction.actStab_Z
#print axioms GroupAction.stabMulAction
#print axioms GroupAction.smul_stab_slicing
#print axioms GroupAction.smul_stab_Z

/-! ## AutAction — transport along a triangulated auto-equivalence

These extend the foundational library's own namespace, since they are API for its types. -/

#print axioms CategoryTheory.Triangulated.PostnikovTower.mapF
#print axioms CategoryTheory.Triangulated.HNFiltration.mapF
#print axioms CategoryTheory.Triangulated.Slicing.mapEquiv
#print axioms CategoryTheory.Triangulated.Slicing.mapEquiv_P

/-! ## StrictAutAction — a strict subgroup of autoequivalences -/

#print axioms GroupAction.StrictAut
#print axioms GroupAction.StrictAut.comp_inv
#print axioms GroupAction.StrictAut.inv_comp
#print axioms GroupAction.StrictAut.obj_inv
#print axioms GroupAction.StrictAut.obj_self
#print axioms GroupAction.StrictAut.F_inv_one
#print axioms GroupAction.StrictAut.F_inv_mul
#print axioms GroupAction.StrictAut.equiv
#print axioms GroupAction.StrictAut.equiv_functor
#print axioms GroupAction.StrictAut.equiv_inverse
#print axioms GroupAction.StrictAut.actSlicing
#print axioms GroupAction.StrictAut.actSlicing_P
#print axioms GroupAction.StrictAut.mulActionSlicing

/-! ## QuotAutAction — Aut(D) as an honest group, by quotienting -/

#print axioms GroupAction.TriEquiv
#print axioms GroupAction.TriEquiv.id
#print axioms GroupAction.TriEquiv.comp
#print axioms GroupAction.TriEquiv.symm
#print axioms GroupAction.TriEquiv.act
#print axioms GroupAction.TriEquiv.act_P
#print axioms GroupAction.TriEquiv.act_id
#print axioms GroupAction.TriEquiv.act_comp
#print axioms GroupAction.TriEquiv.act_congr
#print axioms GroupAction.TriEquiv.setoid
#print axioms GroupAction.AutQuot
#print axioms GroupAction.AutQuot.group
#print axioms GroupAction.AutQuot.mulActionSlicing
#print axioms GroupAction.AutQuot.mk
#print axioms GroupAction.AutQuot.mk_smul_P

/-! ## K0Functor — K₀ is functorial in triangulated functors -/

#print axioms CategoryTheory.Triangulated.isTriangleAdditive_of_isTriangulated
#print axioms CategoryTheory.Triangulated.K₀.mapF
#print axioms CategoryTheory.Triangulated.K₀.mapF_of
#print axioms CategoryTheory.Triangulated.K₀.mapF_id
#print axioms CategoryTheory.Triangulated.K₀.mapF_comp
#print axioms CategoryTheory.Triangulated.K₀.mapF_congr

/-! ## StrictFiniteLength — general strict-hypothesis transfer -/

#print axioms CategoryTheory.Triangulated.strictImage
#print axioms CategoryTheory.Triangulated.strictImage_monotone
#print axioms CategoryTheory.Triangulated.strictImage_injective
#print axioms CategoryTheory.Triangulated.strictImage_strictMono
#print axioms CategoryTheory.Triangulated.isStrictArtinian_of_faithful_strict
#print axioms CategoryTheory.Triangulated.isStrictNoetherian_of_faithful_strict
#print axioms CategoryTheory.Triangulated.mapEquiv_intervalProp_iff

/-! ## AutStabilityAction — the Aut action on stability conditions -/

#print axioms CategoryTheory.Triangulated.autIntervalFunctor
#print axioms CategoryTheory.Triangulated.autFunctor_strictMono
#print axioms CategoryTheory.Triangulated.mapEquiv_isLocallyFinite
#print axioms CategoryTheory.Triangulated.actStabAut
#print axioms CategoryTheory.Triangulated.actStabAut_slicing
#print axioms CategoryTheory.Triangulated.actStabAut_Z

/-! ## GLTildeFibre — the fibre of the projection is Z -/

#print axioms BridgelandStabLean.GroupAction.rayVec_eq_iff
#print axioms BridgelandStabLean.GroupAction.rayVec_eq_of_onRay
#print axioms BridgelandStabLean.GroupAction.deckShift
#print axioms BridgelandStabLean.GroupAction.compat_one_deckShift
#print axioms BridgelandStabLean.GroupAction.deck
#print axioms BridgelandStabLean.GroupAction.exists_deckShift_of_mat_eq_one
#print axioms BridgelandStabLean.GroupAction.deckHom
#print axioms BridgelandStabLean.GroupAction.deckHom_injective
#print axioms BridgelandStabLean.GroupAction.range_deckHom_eq_ker
#print axioms BridgelandStabLean.GroupAction.kerEquiv

/-! ## GLTildeSurj — the projection is surjective -/

#print axioms BridgelandStabLean.GroupAction.cexpI
#print axioms BridgelandStabLean.GroupAction.cplxCoord_apply
#print axioms BridgelandStabLean.GroupAction.cA
#print axioms BridgelandStabLean.GroupAction.cB
#print axioms BridgelandStabLean.GroupAction.mulVec_rayVec_eq
#print axioms BridgelandStabLean.GroupAction.normSq_cA_sub_normSq_cB
#print axioms BridgelandStabLean.GroupAction.norm_cB_lt_norm_cA
#print axioms BridgelandStabLean.GroupAction.Wmap
#print axioms BridgelandStabLean.GroupAction.Wmap_re_pos
#print axioms BridgelandStabLean.GroupAction.Wmap_add_one
#print axioms BridgelandStabLean.GroupAction.lift
#print axioms BridgelandStabLean.GroupAction.mulVec_rayVec_lift
#print axioms BridgelandStabLean.GroupAction.compatible_lift
#print axioms BridgelandStabLean.GroupAction.lift_add_one
#print axioms BridgelandStabLean.GroupAction.cross
#print axioms BridgelandStabLean.GroupAction.cross_rayVec
#print axioms BridgelandStabLean.GroupAction.cross_mulVec
#print axioms BridgelandStabLean.GroupAction.lift_lt_lift_of_lt_of_sub_lt_one
#print axioms BridgelandStabLean.GroupAction.lift_strictMono
#print axioms BridgelandStabLean.GroupAction.lift_continuous
#print axioms BridgelandStabLean.GroupAction.lift_surjective
#print axioms BridgelandStabLean.GroupAction.liftShift
#print axioms BridgelandStabLean.GroupAction.compatible_liftShift
#print axioms BridgelandStabLean.GroupAction.toMatHom_surjective
#print axioms BridgelandStabLean.GroupAction.sect
#print axioms BridgelandStabLean.GroupAction.toMatHom_comp_sect
#print axioms BridgelandStabLean.GroupAction.deck_injective
#print axioms BridgelandStabLean.GroupAction.existsUnique_deck_mul_sect
#print axioms BridgelandStabLean.GroupAction.exact_deckHom_toMatHom

/-! ## GLTildeTopology — topology and simple connectedness -/

#print axioms BridgelandStabLean.GroupAction.rotationMatrix
#print axioms BridgelandStabLean.GroupAction.rotationMatrix_det
#print axioms BridgelandStabLean.GroupAction.rotationMatrix_mulVec_rayVec
#print axioms BridgelandStabLean.GroupAction.rotationMatrix_neg_mul
#print axioms BridgelandStabLean.GroupAction.rotationMatrix_mul_neg
#print axioms BridgelandStabLean.GroupAction.rotationGLPos
#print axioms BridgelandStabLean.GroupAction.rotationGLPos_mat
#print axioms BridgelandStabLean.GroupAction.phaseTranslation
#print axioms BridgelandStabLean.GroupAction.phaseTranslation_apply
#print axioms BridgelandStabLean.GroupAction.compatible_rotation
#print axioms BridgelandStabLean.GroupAction.liftedRotation
#print axioms BridgelandStabLean.GroupAction.liftedRotation_mat
#print axioms BridgelandStabLean.GroupAction.liftedRotation_shift_zero
#print axioms BridgelandStabLean.GroupAction.GLTilde.ext_mat_shift_zero
#print axioms BridgelandStabLean.GroupAction.PositiveReal
#print axioms BridgelandStabLean.GroupAction.GLTildeCoordinates
#print axioms BridgelandStabLean.GroupAction.upperMatrix
#print axioms BridgelandStabLean.GroupAction.upperMatrix_det
#print axioms BridgelandStabLean.GroupAction.upperMatrixInv
#print axioms BridgelandStabLean.GroupAction.upperMatrix_mul_inv
#print axioms BridgelandStabLean.GroupAction.upperMatrix_inv_mul
#print axioms BridgelandStabLean.GroupAction.upperGLPos
#print axioms BridgelandStabLean.GroupAction.upperGLPos_mat
#print axioms BridgelandStabLean.GroupAction.alignedMatrix
#print axioms BridgelandStabLean.GroupAction.alignedMatrix_zero_zero_pos
#print axioms BridgelandStabLean.GroupAction.alignedMatrix_one_zero
#print axioms BridgelandStabLean.GroupAction.alignedMatrix_one_one_pos
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinates
#print axioms BridgelandStabLean.GroupAction.matrixOfCoordinates
#print axioms BridgelandStabLean.GroupAction.matrixOfCoordinates_apply
#print axioms BridgelandStabLean.GroupAction.upperDeckIndex
#print axioms BridgelandStabLean.GroupAction.upperDeckIndex_spec
#print axioms BridgelandStabLean.GroupAction.upperSectionZero
#print axioms BridgelandStabLean.GroupAction.upperSectionZero_mat
#print axioms BridgelandStabLean.GroupAction.upperSectionZero_shift_zero
#print axioms BridgelandStabLean.GroupAction.glTildeOfCoordinates
#print axioms BridgelandStabLean.GroupAction.glTildeOfCoordinates_shift_zero
#print axioms BridgelandStabLean.GroupAction.glTildeOfCoordinates_mat
#print axioms BridgelandStabLean.GroupAction.alignedMatrix_glTildeOfCoordinates
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinates_ofCoordinates
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinates_injective
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinates_surjective
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinateEquiv
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinateEquiv_apply
#print axioms BridgelandStabLean.GroupAction.GLTilde.topologicalSpace
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinateHomeomorph
#print axioms BridgelandStabLean.GroupAction.continuous_rotationMatrix
#print axioms BridgelandStabLean.GroupAction.glTildeOfCoordinates_coordinates
#print axioms BridgelandStabLean.GroupAction.GLTilde.continuous_toMat
#print axioms BridgelandStabLean.GroupAction.GLTilde.contractibleSpace
#print axioms BridgelandStabLean.GroupAction.GLTilde.simplyConnectedSpace

/-! ## GLTildeCover — base coordinates and the universal covering map -/

#print axioms BridgelandStabLean.GroupAction.circleMatrix
#print axioms BridgelandStabLean.GroupAction.circleMatrixInv
#print axioms BridgelandStabLean.GroupAction.circleMatrix_det
#print axioms BridgelandStabLean.GroupAction.circleMatrix_mul_inv
#print axioms BridgelandStabLean.GroupAction.circleMatrix_inv_mul
#print axioms BridgelandStabLean.GroupAction.circleGLPos
#print axioms BridgelandStabLean.GroupAction.circleGLPos_mat
#print axioms BridgelandStabLean.GroupAction.GLPosCoordinates
#print axioms BridgelandStabLean.GroupAction.firstColumnComplex
#print axioms BridgelandStabLean.GroupAction.firstColumnComplex_ne_zero
#print axioms BridgelandStabLean.GroupAction.firstColumnRadius
#print axioms BridgelandStabLean.GroupAction.firstColumnDirection
#print axioms BridgelandStabLean.GroupAction.firstColumnDirection_re
#print axioms BridgelandStabLean.GroupAction.firstColumnDirection_im
#print axioms BridgelandStabLean.GroupAction.secondColumnAlong
#print axioms BridgelandStabLean.GroupAction.secondColumnPerp
#print axioms BridgelandStabLean.GroupAction.secondColumnPerp_pos
#print axioms BridgelandStabLean.GroupAction.glPosCoordinates
#print axioms BridgelandStabLean.GroupAction.glPosOfCoordinates
#print axioms BridgelandStabLean.GroupAction.glPosOfCoordinates_mat
#print axioms BridgelandStabLean.GroupAction.firstColumnDirection_glPosOfCoordinates
#print axioms BridgelandStabLean.GroupAction.secondColumnAlong_glPosOfCoordinates
#print axioms BridgelandStabLean.GroupAction.secondColumnPerp_glPosOfCoordinates
#print axioms BridgelandStabLean.GroupAction.glPosCoordinates_ofCoordinates
#print axioms BridgelandStabLean.GroupAction.glPosOfCoordinates_coordinates
#print axioms BridgelandStabLean.GroupAction.continuous_toMatGLPos
#print axioms BridgelandStabLean.GroupAction.glPosCoordinateHomeomorph
#print axioms BridgelandStabLean.GroupAction.IsCoveringMap.prodMap_id
#print axioms BridgelandStabLean.GroupAction.phaseCircle
#print axioms BridgelandStabLean.GroupAction.phaseCircle_isCoveringMap
#print axioms BridgelandStabLean.GroupAction.coordinateProjection
#print axioms BridgelandStabLean.GroupAction.coordinateProjection_isCoveringMap
#print axioms BridgelandStabLean.GroupAction.phaseCircle_coe
#print axioms BridgelandStabLean.GroupAction.circleMatrix_phaseCircle
#print axioms BridgelandStabLean.GroupAction.glPosOfCoordinates_coordinateProjection
#print axioms BridgelandStabLean.GroupAction.coordinateProjection_apply_glTildeCoordinates
#print axioms BridgelandStabLean.GroupAction.GLTilde.isCoveringMap_toMat
#print axioms BridgelandStabLean.GroupAction.GLTilde.universalCoverData

/-! ## GLTildeTopologicalGroup — compatibility of topology and group operations -/

#print axioms BridgelandStabLean.GroupAction.upperSectionZero_shift_apply
#print axioms BridgelandStabLean.GroupAction.coordinateShift
#print axioms BridgelandStabLean.GroupAction.glTildeOfCoordinates_shift_apply
#print axioms BridgelandStabLean.GroupAction.GLTilde.continuous_shift_apply
#print axioms BridgelandStabLean.GroupAction.GLTilde.isTopologicalGroup

/-! ## AutPairAction — the same action, as a genuine `MulAction` -/

#print axioms BridgelandStabLean.GroupAction.AutPair
#print axioms BridgelandStabLean.GroupAction.AutPair.id
#print axioms BridgelandStabLean.GroupAction.AutPair.mul
#print axioms BridgelandStabLean.GroupAction.AutPair.inv
#print axioms BridgelandStabLean.GroupAction.AutPair.setoid
#print axioms BridgelandStabLean.GroupAction.AutPair.act
#print axioms BridgelandStabLean.GroupAction.AutPair.act_id
#print axioms BridgelandStabLean.GroupAction.AutPair.act_mul
#print axioms BridgelandStabLean.GroupAction.AutPair.act_congr
#print axioms BridgelandStabLean.GroupAction.AutPairQuot
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.group
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.mulAction
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.toAutQuot

/-! ## Normalized quotient, combined action, and topological action layer -/

#print axioms BridgelandStabLean.GroupAction.TriEquiv.inverseIsoOfFunctorIso

#print axioms BridgelandStabLean.GroupAction.relabel_mapEquiv
#print axioms BridgelandStabLean.GroupAction.gltilde_autPair_smul_comm
#print axioms BridgelandStabLean.GroupAction.smulCommClassGLTildeAutPairQuot
#print axioms BridgelandStabLean.GroupAction.combinedMulAction
#print axioms BridgelandStabLean.GroupAction.prod_mk_smul_slicing
#print axioms BridgelandStabLean.GroupAction.prod_mk_smul_Z

#print axioms BridgelandStabLean.GroupAction.Slicing.mapEquiv_phiPlus
#print axioms BridgelandStabLean.GroupAction.Slicing.mapEquiv_phiMinus
#print axioms BridgelandStabLean.GroupAction.slicingDist_mapEquiv_le
#print axioms BridgelandStabLean.GroupAction.stabSeminorm_aut_le
#print axioms BridgelandStabLean.GroupAction.AutPair.mapsTo_basisNhd
#print axioms BridgelandStabLean.GroupAction.AutPair.continuous_act
#print axioms BridgelandStabLean.GroupAction.autPairQuotContinuousConstSMul
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.homeomorph

#print axioms BridgelandStabLean.GroupAction.Slicing.relabel_phiPlus
#print axioms BridgelandStabLean.GroupAction.Slicing.relabel_phiMinus
#print axioms BridgelandStabLean.GroupAction.exists_slicingDist_relabel_control
#print axioms BridgelandStabLean.GroupAction.actCCLM
#print axioms BridgelandStabLean.GroupAction.actCCLM_apply
#print axioms BridgelandStabLean.GroupAction.actC_inv_apply
#print axioms BridgelandStabLean.GroupAction.actCCondition
#print axioms BridgelandStabLean.GroupAction.actCCondition_pos
#print axioms BridgelandStabLean.GroupAction.norm_actC_div_norm_actC_le
#print axioms BridgelandStabLean.GroupAction.stabSeminorm_gltilde_le
#print axioms BridgelandStabLean.GroupAction.exists_gltilde_basisNhd_control
#print axioms BridgelandStabLean.GroupAction.GLTilde.continuous_const_smul_stability
#print axioms BridgelandStabLean.GroupAction.gltildeContinuousConstSMulStability
#print axioms BridgelandStabLean.GroupAction.combinedContinuousConstSMulStability
#print axioms BridgelandStabLean.GroupAction.GLTilde.stabilityHomeomorph
#print axioms BridgelandStabLean.GroupAction.combinedStabilityHomeomorph

/-! ## Jointly continuous symmetry actions -/

#print axioms BridgelandStabLean.GroupAction.GLTilde.continuous_shift_displacement
#print axioms BridgelandStabLean.GroupAction.GLTilde.eventually_uniform_shift_displacement
#print axioms BridgelandStabLean.GroupAction.slicingDist_smul_le_of_displacement
#print axioms BridgelandStabLean.GroupAction.actCCLM_one
#print axioms BridgelandStabLean.GroupAction.GLTilde.continuous_actCCLM
#print axioms BridgelandStabLean.GroupAction.norm_actC_sub_div_le
#print axioms BridgelandStabLean.GroupAction.stabSeminorm_near_identity_le
#print axioms BridgelandStabLean.GroupAction.exists_identity_basisNhd_control
#print axioms BridgelandStabLean.GroupAction.continuousAt_smul_identity
#print axioms BridgelandStabLean.GroupAction.GLTilde.continuousAt_smul_stability
#print axioms BridgelandStabLean.GroupAction.GLTilde.continuous_smul_stability
#print axioms BridgelandStabLean.GroupAction.gltildeContinuousSMulStability
#print axioms BridgelandStabLean.GroupAction.autPairQuotTopologicalSpace
#print axioms BridgelandStabLean.GroupAction.autPairQuotDiscreteTopology
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.continuous_smul_stability
#print axioms BridgelandStabLean.GroupAction.autPairQuotContinuousSMulStability
#print axioms BridgelandStabLean.GroupAction.continuous_combined_smul_stability
#print axioms BridgelandStabLean.GroupAction.combinedContinuousSMulStability

/-! ## Components, equivariant periods, and the effective symmetry quotient -/

#print axioms BridgelandStabLean.GroupAction.componentSmul
#print axioms BridgelandStabLean.GroupAction.componentSmul_mk
#print axioms BridgelandStabLean.GroupAction.componentMulAction
#print axioms BridgelandStabLean.GroupAction.image_connectedComponent_smul
#print axioms BridgelandStabLean.GroupAction.componentHomeomorph
#print axioms BridgelandStabLean.GroupAction.componentHomeomorph_apply_coe
#print axioms BridgelandStabLean.GroupAction.componentStabilizer
#print axioms BridgelandStabLean.GroupAction.mem_componentStabilizer_iff
#print axioms BridgelandStabLean.GroupAction.componentStabilizerMulAction

#print axioms BridgelandStabLean.GroupAction.GLTilde.chargeAddEquiv
#print axioms BridgelandStabLean.GroupAction.GLTilde.chargeAddEquiv_apply
#print axioms BridgelandStabLean.GroupAction.AutPair.chargeAddEquiv
#print axioms BridgelandStabLean.GroupAction.AutPair.chargeAddEquiv_apply
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.chargeAddEquiv
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.chargeAddEquiv_mk
#print axioms BridgelandStabLean.GroupAction.combinedChargeAddEquiv
#print axioms BridgelandStabLean.GroupAction.combinedChargeAddEquiv_mk_apply
#print axioms BridgelandStabLean.GroupAction.GLTilde.centralCharge_equivariant
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.centralCharge_equivariant
#print axioms BridgelandStabLean.GroupAction.combinedCentralCharge_equivariant
#print axioms BridgelandStabLean.GroupAction.combinedCentralCharge_equivariant_apply
#print axioms BridgelandStabLean.GroupAction.componentCentralCharge_equivariant
#print axioms BridgelandStabLean.GroupAction.componentLocalModel_chargeMap_equivariant

#print axioms BridgelandStabLean.GroupAction.shiftFunctorCommShift
#print axioms BridgelandStabLean.GroupAction.shiftTwoMapTriangleIso
#print axioms BridgelandStabLean.GroupAction.shiftTwoIsTriangulated
#print axioms BridgelandStabLean.GroupAction.shiftNegTwoMapTriangleIso
#print axioms BridgelandStabLean.GroupAction.shiftNegTwoIsTriangulated
#print axioms BridgelandStabLean.GroupAction.shiftTwoTriEquiv
#print axioms BridgelandStabLean.GroupAction.K₀.mapF_shift_neg_two
#print axioms BridgelandStabLean.GroupAction.shiftTwoPair
#print axioms BridgelandStabLean.GroupAction.deckShift_neg_one_inv_apply
#print axioms BridgelandStabLean.GroupAction.shiftTwoPair_act_eq_deck_neg_one
#print axioms BridgelandStabLean.GroupAction.deck_mul_deck
#print axioms BridgelandStabLean.GroupAction.deck_zero
#print axioms BridgelandStabLean.GroupAction.deck_one_shiftTwo_combined_smul
#print axioms BridgelandStabLean.GroupAction.combinedActionHom
#print axioms BridgelandStabLean.GroupAction.combinedActionKernel
#print axioms BridgelandStabLean.GroupAction.EffectiveCombinedSymmetry
#print axioms BridgelandStabLean.GroupAction.effectiveCombinedPermHom
#print axioms BridgelandStabLean.GroupAction.effectiveCombinedMulAction
#print axioms BridgelandStabLean.GroupAction.effectiveCombinedFaithfulSMul
#print axioms BridgelandStabLean.GroupAction.deck_one_shiftTwo_mem_combinedActionKernel
#print axioms BridgelandStabLean.GroupAction.deck_one_shiftTwo_eq_one_in_effective

/-! ## AutIsometry — the action preserves the foundational library's phase distance -/

#print axioms CategoryTheory.Triangulated.Slicing.phiPlus_congr
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_congr
#print axioms CategoryTheory.Triangulated.isZero_inverse_iff
#print axioms CategoryTheory.Triangulated.isZero_functor_iff
#print axioms CategoryTheory.Triangulated.mapEquiv_phiPlus
#print axioms CategoryTheory.Triangulated.mapEquiv_phiMinus
#print axioms CategoryTheory.Triangulated.mapEquiv_slicingDist
#print axioms CategoryTheory.Triangulated.actStabAut_slicingDist
#print axioms CategoryTheory.Triangulated.AutPairQuot_smul_slicingDist

/-! ## StabilityMass — choice-free HN mass envelope -/

#print axioms CategoryTheory.Triangulated.HNFiltration.mass
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.charge_ne_zero_of_semistable
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_pos
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_ofIso
#print axioms CategoryTheory.Triangulated.stabilityMass
#print axioms CategoryTheory.Triangulated.stabilityMass_pos
#print axioms CategoryTheory.Triangulated.stabilityMass_congr
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_eq_zero_of_isZero
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_eq_mass
#print axioms CategoryTheory.Triangulated.stabilityMass_eq_mass
#print axioms CategoryTheory.Triangulated.stabilityMass_ne_top
#print axioms CategoryTheory.Triangulated.stabilityMass_lt_top
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_sum
#print axioms CategoryTheory.Triangulated.HNFiltration.exists_headTail_mass
#print axioms CategoryTheory.Triangulated.stabilityMass_eq_zero_iff
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_pos
#print axioms BridgelandStabLean.GroupAction.AutPair.act_charge
#print axioms BridgelandStabLean.GroupAction.AutPair.mass_map_inverse
#print axioms BridgelandStabLean.GroupAction.AutPair.mass_map_functor
#print axioms BridgelandStabLean.GroupAction.AutPair.act_stabilityMass
#print axioms BridgelandStabLean.GroupAction.AutPair.act_stabilityMass_functor_obj

/-! ## StabilityDistance — the three-coordinate extended pseudodistance -/

#print axioms CategoryTheory.Triangulated.logMassDist
#print axioms CategoryTheory.Triangulated.logMassDist_self
#print axioms CategoryTheory.Triangulated.logMassDist_comm
#print axioms CategoryTheory.Triangulated.logMassDist_triangle
#print axioms CategoryTheory.Triangulated.logMassDist_eq_of_ne_top
#print axioms CategoryTheory.Triangulated.phiPlusDist
#print axioms CategoryTheory.Triangulated.phiMinusDist
#print axioms CategoryTheory.Triangulated.massDist
#print axioms CategoryTheory.Triangulated.stabilityDistTerm
#print axioms CategoryTheory.Triangulated.stabilityDist
#print axioms CategoryTheory.Triangulated.phiPlusDist_self
#print axioms CategoryTheory.Triangulated.phiMinusDist_self
#print axioms CategoryTheory.Triangulated.massDist_self
#print axioms CategoryTheory.Triangulated.phiPlusDist_comm
#print axioms CategoryTheory.Triangulated.phiMinusDist_comm
#print axioms CategoryTheory.Triangulated.massDist_comm
#print axioms CategoryTheory.Triangulated.phiPlusDist_triangle
#print axioms CategoryTheory.Triangulated.phiMinusDist_triangle
#print axioms CategoryTheory.Triangulated.massDist_triangle
#print axioms CategoryTheory.Triangulated.massDist_eq_abs_log
#print axioms CategoryTheory.Triangulated.massDist_eq_abs_log_ratio
#print axioms CategoryTheory.Triangulated.stabilityDist_self
#print axioms CategoryTheory.Triangulated.stabilityDist_comm
#print axioms CategoryTheory.Triangulated.stabilityDist_triangle
#print axioms CategoryTheory.Triangulated.slicingDist_le_stabilityDist
#print axioms CategoryTheory.Triangulated.stabilityDistTerm_le_stabilityDist
#print axioms CategoryTheory.Triangulated.phiPlusDist_le_stabilityDist
#print axioms CategoryTheory.Triangulated.phiMinusDist_le_stabilityDist
#print axioms CategoryTheory.Triangulated.massDist_le_stabilityDist

/-! ## StabilityDistanceSeparation — identity of indiscernibles -/

#print axioms CategoryTheory.Triangulated.stabilityDistTerm_eq_zero_of_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_norm_charge
#print axioms CategoryTheory.Triangulated.phiPlus_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.phiMinus_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.slicing_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.charge_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.charge_comp_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityDist_eq_zero_iff
#print axioms CategoryTheory.Triangulated.stabilityConditionDist_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityConditionDist_eq_zero_iff

/-! ## StabilityDistanceTopology — Proposition 8.1 topology comparison -/

#print axioms CategoryTheory.Triangulated.abs_phiPlus_sub_lt_of_stabilityDist
#print axioms CategoryTheory.Triangulated.abs_phiMinus_sub_lt_of_stabilityDist
#print axioms CategoryTheory.Triangulated.abs_log_mass_ratio_lt_of_stabilityDist
#print axioms CategoryTheory.Triangulated.exp_neg_lt_mass_ratio_and_lt_exp_of_stabilityDist
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_lt_exp_mul_of_stabilityDist
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_lt_exp_mul_of_stabilityDist'
#print axioms CategoryTheory.Triangulated.norm_phaseExp_sub_phaseExp_le
#print axioms CategoryTheory.Triangulated.norm_sum_phaseExp_sub_centralRay_le
#print axioms CategoryTheory.Triangulated.charge_eq_stabilityMass_mul_phaseExp
#print axioms CategoryTheory.Triangulated.norm_charge_sub_mass_phaseExp_le_of_stabilityDist
#print axioms CategoryTheory.Triangulated.cos_mul_stabilityMass_le_norm_charge_of_width
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_le_of_mem_basisNhd_of_semistable
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_le_of_mem_basisNhd_of_semistable'
#print axioms CategoryTheory.Triangulated.StabilityMassTriangleInequality
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_congr
#print axioms CategoryTheory.Triangulated.stabilityMass_chain_le_partial_sum
#print axioms CategoryTheory.Triangulated.stabilityMass_le_sum_postnikov_factors
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_le_of_mem_basisNhd
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_le_of_mem_basisNhd'
#print axioms CategoryTheory.Triangulated.basisForwardMassFactor
#print axioms CategoryTheory.Triangulated.basisReverseMassFactor
#print axioms CategoryTheory.Triangulated.basisMassControl
#print axioms CategoryTheory.Triangulated.basisForwardMassFactor_zero
#print axioms CategoryTheory.Triangulated.basisReverseMassFactor_zero
#print axioms CategoryTheory.Triangulated.basisMassControl_zero
#print axioms CategoryTheory.Triangulated.abs_log_mass_ratio_le_of_mem_basisNhd
#print axioms CategoryTheory.Triangulated.exists_basisMassControl_lt
#print axioms CategoryTheory.Triangulated.exists_basisNhd_subset_stabilityDist_ball
#print axioms CategoryTheory.Triangulated.stabilityChargeControl
#print axioms CategoryTheory.Triangulated.stabilityChargeControl_zero
#print axioms CategoryTheory.Triangulated.norm_charge_sub_charge_lt_of_stabilityDist
#print axioms CategoryTheory.Triangulated.stabSeminorm_le_of_stabilityDist_lt
#print axioms CategoryTheory.Triangulated.exists_stabilityChargeControl_lt
#print axioms CategoryTheory.Triangulated.exists_stabilityDist_ball_subset_basisNhd
#print axioms CategoryTheory.Triangulated.nhds_hasBasis_basisNhd
#print axioms CategoryTheory.Triangulated.StabilityDistanceTopologyCompatible
#print axioms CategoryTheory.Triangulated.stabilityDistanceTopologyCompatible_of_mass_triangle
#print axioms CategoryTheory.Triangulated.stabilityPseudoEMetricSpace
#print axioms CategoryTheory.Triangulated.stabilityPseudoEMetricSpace_toTopologicalSpace
#print axioms CategoryTheory.Triangulated.stabilityPseudoEMetricSpace_edist
#print axioms CategoryTheory.Triangulated.stabilityEMetricSpace
#print axioms CategoryTheory.Triangulated.stabilityEMetricSpace_toTopologicalSpace
#print axioms CategoryTheory.Triangulated.stabilityPseudoEMetricSpaceOfMassTriangle
#print axioms CategoryTheory.Triangulated.stabilityEMetricSpaceOfMassTriangle

/-! ## StabilityMassTriangle — first categorical mass inequalities -/

/-! ### HNPolygon — abelian HN polygon and metric boundary path -/

#print axioms CategoryTheory.StabilityFunction.hnPolygon
#print axioms CategoryTheory.StabilityFunction.subobjectCharge_mem_hnPolygon
#print axioms CategoryTheory.StabilityFunction.hnPolygon_mono
#print axioms CategoryTheory.ComplexPolygonalPath.crossFunctional
#print axioms CategoryTheory.ComplexPolygonalPath.crossFunctional_apply
#print axioms CategoryTheory.ComplexPolygonalPath.unitRay
#print axioms CategoryTheory.ComplexPolygonalPath.unitRay_re
#print axioms CategoryTheory.ComplexPolygonalPath.unitRay_im
#print axioms CategoryTheory.ComplexPolygonalPath.unitRay_mem_upperHalfPlaneUnion
#print axioms CategoryTheory.ComplexPolygonalPath.arg_unitRay
#print axioms CategoryTheory.ComplexPolygonalPath.crossFunctional_pos_of_arg_lt
#print axioms CategoryTheory.ComplexPolygonalPath.crossFunctional_neg_of_arg_lt
#print axioms CategoryTheory.ComplexPolygonalPath.exists_strict_support_at_interior
#print axioms CategoryTheory.ComplexPolygonalPath.sum_edges_eq_last_sub_zero
#print axioms CategoryTheory.ComplexPolygonalPath.arg_last_sub_zero_le_arg_first
#print axioms CategoryTheory.ComplexPolygonalPath.arg_last_edge_le_arg_last_sub_zero
#print axioms CategoryTheory.ComplexPolygonalPath.length
#print axioms CategoryTheory.ComplexPolygonalPath.norm_last_sub_zero_le_length
#print axioms CategoryTheory.AbelianHNFiltration.semistable_le_chain_of_phase_gt
#print axioms CategoryTheory.AbelianHNFiltration.semistable_phase_le_first
#print axioms CategoryTheory.AbelianHNFiltration.factorObj
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex
#print axioms CategoryTheory.AbelianHNFiltration.polygonEdge
#print axioms CategoryTheory.AbelianHNFiltration.polygonLength
#print axioms CategoryTheory.AbelianHNFiltration.mass
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex_succ_sub
#print axioms CategoryTheory.AbelianHNFiltration.polygonEdge_mem_upperHalfPlaneUnion
#print axioms CategoryTheory.AbelianHNFiltration.polygonEdge_arg
#print axioms CategoryTheory.AbelianHNFiltration.polygonEdge_arg_strictAnti
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex_exists_strict_support
#print axioms CategoryTheory.AbelianHNFiltration.polygonLength_eq_mass
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex_zero
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex_last
#print axioms CategoryTheory.AbelianHNFiltration.phase_le_first
#print axioms CategoryTheory.AbelianHNFiltration.last_le_phase
#print axioms CategoryTheory.AbelianHNFiltration.phase_last_prefix_le_of_ne_zero_to_semistable
#print axioms CategoryTheory.AbelianHNFiltration.subobject_phase_le_first
#print axioms CategoryTheory.AbelianHNFiltration.quotientHNFiltration
#print axioms CategoryTheory.AbelianHNFiltration.quotientInfToCokernel
#print axioms CategoryTheory.AbelianHNFiltration.quotientInfToCokernel_mono
#print axioms CategoryTheory.AbelianHNFiltration.last_prefix_le_quotient_phase
#print axioms CategoryTheory.AbelianHNFiltration.quotient_inf_phase_le
#print axioms CategoryTheory.AbelianHNFiltration.subobjectCharge_le_of_polygonVertex_isMax
#print axioms CategoryTheory.AbelianHNFiltration.hnPolygon_le_of_polygonVertex_isMax
#print axioms CategoryTheory.AbelianHNFiltration.subobjectCharge_exists_strict_support
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex_exists_strict_support_hnPolygon
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex_mem_hnPolygon
#print axioms CategoryTheory.AbelianHNFiltration.norm_charge_le_polygonLength
#print axioms CategoryTheory.AbelianHNFiltration.norm_charge_le_mass

/-! ### ConvexPolygonPerimeter — Ikeda Lemma 3.7 at t = 0 -/

#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional_apply
#print axioms CategoryTheory.ComplexPolygonalPath.unitDirection
#print axioms CategoryTheory.ComplexPolygonalPath.norm_unitDirection_le_one
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional_unitDirection_self
#print axioms CategoryTheory.ComplexPolygonalPath.unitDirection_eq_unitRay_arg
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional_le_norm_mul
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional_sub_left
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional_sub_right
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional_unitRay_sub
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength_nil
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength_singleton
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength_cons_cons
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength_mono_sublist
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength_comp_monotone_le
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength_ofFn_eq_length
#print axioms CategoryTheory.ComplexPolygonalPath.closedEdge
#print axioms CategoryTheory.ComplexPolygonalPath.closedLength
#print axioms CategoryTheory.ComplexPolygonalPath.closedTangent
#print axioms CategoryTheory.ComplexPolygonalPath.turningFunctional
#print axioms CategoryTheory.ComplexPolygonalPath.closedLength_eq_sum_turning
#print axioms CategoryTheory.ComplexPolygonalPath.closedLength_eq_length_add_chord
#print axioms CategoryTheory.ComplexPolygonalPath.length_snoc
#print axioms CategoryTheory.ComplexPolygonalPath.closedLength_comp_monotone_le
#print axioms CategoryTheory.ComplexPolygonalPath.closedLength_le_of_monotone_support
#print axioms CategoryTheory.ComplexPolygonalPath.last_sub_zero_mem_upperHalfPlaneUnion
#print axioms CategoryTheory.ComplexPolygonalPath.sub_mem_upperHalfPlaneUnion_of_lt
#print axioms CategoryTheory.ComplexPolygonalPath.interiorPrevEdge
#print axioms CategoryTheory.ComplexPolygonalPath.interiorNextEdge
#print axioms CategoryTheory.ComplexPolygonalPath.interiorBisector
#print axioms CategoryTheory.ComplexPolygonalPath.interiorTurnScale
#print axioms CategoryTheory.ComplexPolygonalPath.turningFunctional_interior_eq_cross
#print axioms CategoryTheory.ComplexPolygonalPath.interiorTurnScale_pos
#print axioms CategoryTheory.ComplexPolygonalPath.interiorBisector_mem_Ioo
#print axioms CategoryTheory.ComplexPolygonalPath.interiorBisector_strictAnti
#print axioms CategoryTheory.ComplexPolygonalPath.crossMaxIndex
#print axioms CategoryTheory.ComplexPolygonalPath.crossMaxIndex_max
#print axioms CategoryTheory.ComplexPolygonalPath.crossMaxIndex_mono_of_angle_gt
#print axioms CategoryTheory.ComplexPolygonalPath.length_le_of_convexHull_subset
#print axioms CategoryTheory.AbelianHNFiltration.polygonLength_le_of_vertexHull_subset
#print axioms CategoryTheory.AbelianHNFiltration.polygonLength_le_add_norm_charge_sub_of_mono
#print axioms CategoryTheory.AbelianHNFiltration.mass_le_add_norm_cokernel_of_mono
#print axioms CategoryTheory.AbelianHNFiltration.mass_le_add_norm_of_shortExact
#print axioms CategoryTheory.AbelianHNFiltration.mass_eq_mass

/-! ### H0ExactnessBridge — the exact heart-source obstruction -/

#print axioms CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0Complex
#print axioms CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0Complex_exact_iff_mono_cokernelDesc
#print axioms CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0Complex_exact_of_isHomological
#print axioms CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0Complex_exact_of_H0Functor_isHomological
#print axioms CategoryTheory.Triangulated.HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc
#print axioms CategoryTheory.Triangulated.HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc_of_H0Functor
#print axioms CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoTruncGEOfIsLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_of_isLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isLE_toH0primeHom_of_isLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_of_isLE_fromH0primeHom_of_isLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isLE_zero
#print axioms CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_of_isLE_comp
#print axioms CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isLE_naturality
#print axioms CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_map_distinguished_exact_of_isLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.isIso_H0primeFunctor_map_truncLEι
#print axioms CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0Complex_exact
#print axioms CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_map_distinguished_exact_of_obj₁_isLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.mono_H0primeFunctor_map_mor₂_of_obj₁_isGE_one
#print axioms CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_isHomological_unconditional
#print axioms CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_unconditional
#print axioms CategoryTheory.Triangulated.HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional

#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observable
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observable_slicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observable_charge
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_Zobj
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_hasHN
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.mem_slicing_of_heart_isSemistable
#print axioms CategoryTheory.Triangulated.norm_charge_le_stabilityMass_toReal
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_shift_one
#print axioms CategoryTheory.Triangulated.stabilityMass_shift_one
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_shift_neg_one
#print axioms CategoryTheory.Triangulated.stabilityMass_shift_neg_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.charge_triangle
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_obj₂_semistable
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_same_phase
#print axioms CategoryTheory.Triangulated.StabilityMassBoundaryHeartInequality
#print axioms CategoryTheory.Triangulated.StabilityMassSemistableLeftTriangleInequality
#print axioms CategoryTheory.Triangulated.stabilityMassTriangleInequality_of_semistable_obj₁
#print axioms CategoryTheory.Triangulated.StabilityMassHeartShortExactInequality
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.mass_eq_stabilityMass_toReal
#print axioms CategoryTheory.Triangulated.stabilityMassBoundaryHeartInequality
#print axioms CategoryTheory.Triangulated.stabilityMassHeartShortExactInequality_of_triangle
#print axioms CategoryTheory.Triangulated.stabilityMass_heart_shortExact_le_of_obj₂_semistable
#print axioms CategoryTheory.Triangulated.stabilityMass_heart_shortExact_le_of_same_phase
#print axioms CategoryTheory.Triangulated.actC_rotationGLPos
#print axioms CategoryTheory.Triangulated.norm_actC_rotationGLPos
#print axioms CategoryTheory.Triangulated.HNFiltration.rotateStability
#print axioms CategoryTheory.Triangulated.HNFiltration.unrotateStability
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_rotateStability
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_unrotateStability
#print axioms CategoryTheory.Triangulated.stabilityMass_liftedRotation
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_appendFactor
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_appendFactor
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_triangle_eq_add_of_hn_separated
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_heartCoh_negOne_add_zero
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_triangle_eq_add_of_same_phase
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_obj₁_phase_one_of_obj₃_le_one
#print axioms CategoryTheory.Triangulated.heartShortExact_exists_distinguished_triangle
#print axioms CategoryTheory.Triangulated.phaseOne_endpoints_of_heart_shortExact
#print axioms CategoryTheory.Triangulated.stabilityMass_H0FunctorShift_negOne_zero_triangle_le_of_obj₁_phase_one
#print axioms CategoryTheory.Triangulated.stabilityMass_heartCoh_negOne_zero_triangle_le_of_obj₁_phase_one
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_obj₁_phase_one_of_amplitude
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_obj₁_phase_one
#print axioms CategoryTheory.Triangulated.stabilityMassSemistableLeftTriangleInequality

/-! ## AutFullIsometry — invariance of all three coordinates -/

#print axioms BridgelandStabLean.GroupAction.AutPair.act_phiPlusDist
#print axioms BridgelandStabLean.GroupAction.AutPair.act_phiMinusDist
#print axioms BridgelandStabLean.GroupAction.AutPair.act_massDist
#print axioms BridgelandStabLean.GroupAction.AutPair.act_stabilityDistTerm
#print axioms BridgelandStabLean.GroupAction.AutPair.act_stabilityDistTerm_functor_obj
#print axioms BridgelandStabLean.GroupAction.AutPair.act_stabilityDist
#print axioms CategoryTheory.Triangulated.AutPairQuot_smul_stabilityDist

/-! ## Group-law spot checks

`#print axioms` audits the proof term; these check the instance actually
computes the intended composition rather than some other group structure that
happens to typecheck. Both are `rfl`, so a wrong `mul` would fail here.
-/

section SpotChecks

open GroupAction

example (f g : NormalizedShift) (φ : ℝ) :
    (f * g).toOrderIso φ = f.toOrderIso (g.toOrderIso φ) := rfl

example (φ : ℝ) : (1 : NormalizedShift).toOrderIso φ = φ := rfl

example (f : NormalizedShift) (φ : ℝ) :
    (f⁻¹ * f).toOrderIso φ = φ := by simp

/-- `GLTilde` multiplication must compose the shift factors in the SAME order
as `NormalizedShift` does. An order flip here would typecheck and be wrong. -/
example (x y : GLTilde) (φ : ℝ) :
    (x * y).shift.toOrderIso φ = x.shift.toOrderIso (y.shift.toOrderIso φ) :=
  rfl

/-- The projections agree with the field accessors. -/
example (x : GLTilde) : GLTilde.toMatHom x = x.mat := rfl
example (x : GLTilde) : GLTilde.toShiftHom x = x.shift := rfl

/-- The identity really is a compatible pair, so `GLTilde` is inhabited and
the group is not vacuous. -/
example : (1 : GLTilde).mat = 1 ∧ (1 : GLTilde).shift = 1 := ⟨rfl, rfl⟩

/-- Phase `+1` is the antipodal ray — the shift functor `[1]`. -/
example (φ : ℝ) : rayVec (φ + 1) = -rayVec φ := rayVec_add_one φ

end SpotChecks

/-! ## Step-3a convention checks

The slicing action relabels by `f⁻¹`, not `f`. With `f` the definition still
typechecks and `mul_smul` fails, so the `MulAction` laws below are the real
guard; these `example`s pin the surface convention that goes with them.
-/

section SlicingChecks

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated GroupAction

-- Declared explicitly. `lake env lean` does not apply the package's
-- `[leanOptions]`, so under a bare `lean` invocation `u` and `v` were
-- auto-bound and this section elaborated by accident. Under the repo's actual
-- settings (`autoImplicit = false`) it did not compile at all -- which is
-- exactly the rot that covering this file with a `lean_lib` is meant to catch.
universe u v

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

example (f : NormalizedShift) (s : Slicing C) (φ : ℝ) :
    (f • s).P φ = s.P (f⁻¹.toOrderIso φ) := rfl

/-- `GLTilde` acts through its shift factor only — the matrix factor is not
consulted. -/
example (x : GLTilde) (s : Slicing C) (φ : ℝ) :
    (x • s).P φ = (x.shift • s).P φ := rfl

/-! Step 3b: both factors act, each on its own component. -/

variable {Λ : Type*} [AddCommGroup Λ] (v : K₀ C →+ Λ)

example (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) :
    (x • σ).slicing = x • σ.slicing := rfl

example (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) (a : Λ) :
    (x • σ).Z a = actC x.mat (σ.Z a) := rfl

/-! Step 3c: the action reaches full stability conditions. -/

section StabChecks

variable [IsTriangulated C]

example (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) :
    (x • σ).slicing = x • σ.slicing := rfl

example (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) (a : Λ) :
    (x • σ).Z a = actC x.mat (σ.Z a) := rfl

end StabChecks

/-! The `Aut` half, now a `MulAction`.

Both components reverse under `*`, and they reverse in *opposite* syntactic
directions — the auto-equivalences compose contravariantly, the lattice maps
covariantly. Getting one of the two backwards typechecks and is wrong, so both
are pinned by `rfl` here. -/

section AutPairChecks

variable [IsTriangulated C]

/-- `a * b` applies `b`'s lattice automorphism FIRST. -/
example (a b : AutPair v) (σ : StabilityCondition.WithClassMap C v) (x : Λ) :
    ((AutPairQuot.mk a * AutPairQuot.mk b) • σ).Z x = σ.Z (b.lam (a.lam x)) := rfl

/-- ...and correspondingly applies `a`'s inverse equivalence first on objects. -/
example (a b : AutPair v) (σ : StabilityCondition.WithClassMap C v) (φ : ℝ) (X : C) :
    ((AutPairQuot.mk a * AutPairQuot.mk b) • σ).slicing.P φ X
      = σ.slicing.P φ (b.Φ.e.inverse.obj (a.Φ.e.inverse.obj X)) := rfl

/-- The identity acts as the identity, definitionally on both components. -/
example (σ : StabilityCondition.WithClassMap C v) (x : Λ) :
    ((1 : AutPairQuot v) • σ).Z x = σ.Z x := rfl

/-- The forgetful map really does forget only the lattice datum. -/
example (a : AutPair v) : AutPairQuot.toAutQuot (AutPairQuot.mk a) = AutQuot.mk a.Φ := rfl

/-- The quotient relation is normalized: only the forward functor is part of
the relation; inverse isomorphisms are derived from adjoint uniqueness. -/
example (a b : AutPair v) :
    a ≈ b ↔ (Nonempty (a.Φ.e.functor ≅ b.Φ.e.functor) ∧ a.lam = b.lam) := Iff.rfl

/-- The two §8 factors commute on stability conditions. -/
example (x : GLTilde) (a : AutPair v) (σ : StabilityCondition.WithClassMap C v) :
    x • (AutPairQuot.mk a • σ) = AutPairQuot.mk a • (x • σ) :=
  gltilde_autPair_smul_comm x a σ

/-- All three fixed-element continuity instances are found by typeclass search. -/
example (x : GLTilde) :
    Continuous fun σ : StabilityCondition.WithClassMap C v ↦ x • σ :=
  continuous_const_smul x

example (q : AutPairQuot v) :
    Continuous fun σ : StabilityCondition.WithClassMap C v ↦ q • σ :=
  continuous_const_smul q

example (p : GLTilde × AutPairQuot v) :
    Continuous fun σ : StabilityCondition.WithClassMap C v ↦ p • σ :=
  continuous_const_smul p

/-- The corresponding joint-continuity instances are also available. -/
example : Continuous fun p : GLTilde × StabilityCondition.WithClassMap C v ↦
    p.1 • p.2 :=
  continuous_smul

example : Continuous fun p : AutPairQuot v × StabilityCondition.WithClassMap C v ↦
    p.1 • p.2 :=
  continuous_smul

example : Continuous fun p : (GLTilde × AutPairQuot v) ×
    StabilityCondition.WithClassMap C v ↦ p.1 • p.2 :=
  continuous_smul

end AutPairChecks

end SlicingChecks
