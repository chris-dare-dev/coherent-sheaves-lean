/-
Axiom + sorry audit over a HAND-MAINTAINED LIST of this library's declarations.

Run: `lake env lean scripts/DGCategoryAudit.lean` (to read the output), or
`lake build DGCategoryAudit` (to check it still elaborates).

The same shape as `scripts/StabilityConditionAudit.lean`, and gated the same way:

    lake env lean scripts/DGCategoryAudit.lean > dg-audit.txt 2>&1
    python3 scripts/check_audit.py dg-audit.txt scripts/DGCategoryAudit.lean

`#print axioms` prints `[sorryAx]` and exits 0, so being in the build is not
being a gate -- `check_audit.py` is what fails on an axiom outside the trusted
three, on `sorryAx`, on an empty sweep, and on this file falling behind the
source tree.

The dg-category subsystem was gated from its first commit rather than
retrofitted. The algebraic-geometry subsystem needed a linter ratchet to catch
up; this list starts complete and should stay that way.
-/
import DerivedAlgGeo.CategoryTheory.DGCategory

#print axioms CategoryTheory.Cdg
#print axioms CategoryTheory.Cdg.coboundariesIn_le_comap
#print axioms CategoryTheory.Cdg.coboundaries_le_comap
#print axioms CategoryTheory.Cdg.cochain_ofHom_coneHom
#print axioms CategoryTheory.Cdg.cocycleAddEquiv
#print axioms CategoryTheory.Cdg.cocycles_eq
#print axioms CategoryTheory.Cdg.comp_fst_of_split
#print axioms CategoryTheory.Cdg.comp_snd_of_split
#print axioms CategoryTheory.Cdg.coneCocycle
#print axioms CategoryTheory.Cdg.coneHom
#print axioms CategoryTheory.Cdg.coneObj
#print axioms CategoryTheory.Cdg.delta_shift_sign_agrees
#print axioms CategoryTheory.Cdg.dgComp_eq
#print axioms CategoryTheory.Cdg.dgHom_eq
#print axioms CategoryTheory.Cdg.dgId_eq
#print axioms CategoryTheory.Cdg.enhancement
#print axioms CategoryTheory.Cdg.h0Functor
#print axioms CategoryTheory.Cdg.homEquivCohomologyClass
#print axioms CategoryTheory.Cdg.homOf_comp
#print axioms CategoryTheory.Cdg.homOf_dgComp
#print axioms CategoryTheory.Cdg.homSeam
#print axioms CategoryTheory.Cdg.instDGCategory
#print axioms CategoryTheory.Cdg.instEssSurjH0HomotopyCategoryIntUpH0Functor
#print axioms CategoryTheory.Cdg.instFaithfulH0HomotopyCategoryIntUpH0Functor
#print axioms CategoryTheory.Cdg.instFullH0HomotopyCategoryIntUpH0Functor
#print axioms CategoryTheory.Cdg.instIsEquivalenceH0HomotopyCategoryIntUpH0Functor
#print axioms CategoryTheory.Cdg.isConeOf
#print axioms CategoryTheory.Cdg.isPretriangulated
#print axioms CategoryTheory.Cdg.isShiftBy
#print axioms CategoryTheory.Cdg.mem_coboundaries_iff'
#print axioms CategoryTheory.Cdg.of
#print axioms CategoryTheory.Cdg.ofCocycle
#print axioms CategoryTheory.Cdg.ofCocycle_toCocycle
#print axioms CategoryTheory.Cdg.ofCocycle_val
#print axioms CategoryTheory.Cdg.of_shiftObj
#print axioms CategoryTheory.Cdg.postcompAddEquiv
#print axioms CategoryTheory.Cdg.quotient_map_homOf_eq
#print axioms CategoryTheory.Cdg.rightUnshift_shiftCocycle
#print axioms CategoryTheory.Cdg.seam
#print axioms CategoryTheory.Cdg.shiftCocycle
#print axioms CategoryTheory.Cdg.shiftComp_eq
#print axioms CategoryTheory.Cdg.shiftD_eq
#print axioms CategoryTheory.Cdg.shiftObj
#print axioms CategoryTheory.Cdg.struct
#print axioms CategoryTheory.Cdg.toCocycle
#print axioms CategoryTheory.Cdg.toCocycle_ofCocycle
#print axioms CategoryTheory.Cdg.toCocycle_val
#print axioms CategoryTheory.Const
#print axioms CategoryTheory.Const.dgCategory
#print axioms CategoryTheory.DGCategory
#print axioms CategoryTheory.DGCategory.dgComp_assoc
#print axioms CategoryTheory.DGCategory.dgComp_id
#print axioms CategoryTheory.DGCategory.dgComp_leibniz
#print axioms CategoryTheory.DGCategory.dgComp_units_smul_left
#print axioms CategoryTheory.DGCategory.dgComp_units_smul_right
#print axioms CategoryTheory.DGCategory.dgId_cocycle
#print axioms CategoryTheory.DGCategory.dgId_comp
#print axioms CategoryTheory.DGCategory.dgProd_fst_add
#print axioms CategoryTheory.DGCategory.dgProd_fst_units_smul
#print axioms CategoryTheory.DGCategory.dgProd_snd_add
#print axioms CategoryTheory.DGCategory.dgProd_snd_units_smul
#print axioms CategoryTheory.DGCategory.hom_units_smul
#print axioms CategoryTheory.DGCategory.op
#print axioms CategoryTheory.DGCategory.opStruct
#print axioms CategoryTheory.DGCategory.op_dgComp_apply
#print axioms CategoryTheory.DGCategory.op_dgHom
#print axioms CategoryTheory.DGCategory.op_dgId
#print axioms CategoryTheory.DGCategory.prod
#print axioms CategoryTheory.DGCategory.prodStruct
#print axioms CategoryTheory.DGCategory.prod_d_apply
#print axioms CategoryTheory.DGCategory.prod_dgComp_apply
#print axioms CategoryTheory.DGCategory.prod_dgId
#print axioms CategoryTheory.DGCategory.shiftComp
#print axioms CategoryTheory.DGCategory.shiftComp.congr_simp
#print axioms CategoryTheory.DGCategory.shiftComp_apply
#print axioms CategoryTheory.DGCategory.shiftComp_assoc
#print axioms CategoryTheory.DGCategory.shiftComp_dgId_left
#print axioms CategoryTheory.DGCategory.shiftComp_dgId_right
#print axioms CategoryTheory.DGCategory.shiftComp_leibniz
#print axioms CategoryTheory.DGCategory.shiftComp_zero_zero
#print axioms CategoryTheory.DGCategory.shiftD
#print axioms CategoryTheory.DGCategory.shiftD_apply
#print axioms CategoryTheory.DGCategory.shiftD_shiftD
#print axioms CategoryTheory.DGCategory.shiftD_zero
#print axioms CategoryTheory.DGCategory.shiftFunctor_dgHom_X
#print axioms CategoryTheory.DGCategory.shiftFunctor_dgHom_d
#print axioms CategoryTheory.DGCategory.toDGCategoryStruct
#print axioms CategoryTheory.DGCategoryStruct
#print axioms CategoryTheory.DGCategoryStruct.dgComp
#print axioms CategoryTheory.DGCategoryStruct.dgComp.congr_simp
#print axioms CategoryTheory.DGCategoryStruct.dgHom
#print axioms CategoryTheory.DGCategoryStruct.dgId
#print axioms CategoryTheory.DGFunctor
#print axioms CategoryTheory.DGFunctor.IsQuasiEquivalence
#print axioms CategoryTheory.DGFunctor.IsQuasiEquivalence.essSurj
#print axioms CategoryTheory.DGFunctor.IsQuasiEquivalence.quasiIso
#print axioms CategoryTheory.DGFunctor.comp
#print axioms CategoryTheory.DGFunctor.comp_map
#print axioms CategoryTheory.DGFunctor.comp_obj
#print axioms CategoryTheory.DGFunctor.h0
#print axioms CategoryTheory.DGFunctor.h0CompIso
#print axioms CategoryTheory.DGFunctor.h0IdIso
#print axioms CategoryTheory.DGFunctor.h0_map_mk
#print axioms CategoryTheory.DGFunctor.h0_obj
#print axioms CategoryTheory.DGFunctor.id
#print axioms CategoryTheory.DGFunctor.id_map
#print axioms CategoryTheory.DGFunctor.id_obj
#print axioms CategoryTheory.DGFunctor.map
#print axioms CategoryTheory.DGFunctor.mapComplex
#print axioms CategoryTheory.DGFunctor.map_comp
#print axioms CategoryTheory.DGFunctor.map_d
#print axioms CategoryTheory.DGFunctor.map_id
#print axioms CategoryTheory.DGFunctor.map_mem_coboundaries
#print axioms CategoryTheory.DGFunctor.map_mem_cocycles
#print axioms CategoryTheory.DGFunctor.mk.inj
#print axioms CategoryTheory.DGFunctor.mk.sizeOf_spec
#print axioms CategoryTheory.DGFunctor.obj
#print axioms CategoryTheory.DGLinear
#print axioms CategoryTheory.DGLinear.comp_smul_left
#print axioms CategoryTheory.DGLinear.comp_smul_right
#print axioms CategoryTheory.DGLinear.d_smul
#print axioms CategoryTheory.Enhancement
#print axioms CategoryTheory.Enhancement.dgCat
#print axioms CategoryTheory.Enhancement.equiv
#print axioms CategoryTheory.Enhancement.hasZeroObject
#print axioms CategoryTheory.Enhancement.isDGCategory
#print axioms CategoryTheory.Enhancement.isPretriangulated
#print axioms CategoryTheory.Enhancement.mk.inj
#print axioms CategoryTheory.Enhancement.mk.sizeOf_spec
#print axioms CategoryTheory.H0
#print axioms CategoryTheory.H0.category
#print axioms CategoryTheory.H0.coboundariesIn
#print axioms CategoryTheory.H0.hasZeroObject
#print axioms CategoryTheory.H0.isZero_of_dgId_eq_zero
#print axioms CategoryTheory.H0.of
#print axioms CategoryTheory.H0.of_self
#print axioms CategoryTheory.H0.preadditive
#print axioms CategoryTheory.IsConeOf
#print axioms CategoryTheory.IsConeOf.bijective
#print axioms CategoryTheory.IsConeOf.comp_inr_mem_coboundaries
#print axioms CategoryTheory.IsConeOf.inl
#print axioms CategoryTheory.IsConeOf.inr
#print axioms CategoryTheory.IsConeOf.inr_closed
#print axioms CategoryTheory.IsConeOf.inr_mem_cocycles
#print axioms CategoryTheory.IsConeOf.mk.inj
#print axioms CategoryTheory.IsConeOf.mk.sizeOf_spec
#print axioms CategoryTheory.IsConeOf.δ_inl
#print axioms CategoryTheory.IsPretriangulated
#print axioms CategoryTheory.IsPretriangulated.exists_cone
#print axioms CategoryTheory.IsPretriangulated.exists_shift
#print axioms CategoryTheory.IsPretriangulated.exists_zero
#print axioms CategoryTheory.IsShiftBy
#print axioms CategoryTheory.IsShiftBy.bijective
#print axioms CategoryTheory.IsShiftBy.bijective_homMap
#print axioms CategoryTheory.IsShiftBy.comp
#print axioms CategoryTheory.IsShiftBy.compare
#print axioms CategoryTheory.IsShiftBy.compare_comp_compare
#print axioms CategoryTheory.IsShiftBy.compare_eq_mapShift
#print axioms CategoryTheory.IsShiftBy.compare_mem_cocycles
#print axioms CategoryTheory.IsShiftBy.hom
#print axioms CategoryTheory.IsShiftBy.homMap
#print axioms CategoryTheory.IsShiftBy.hom_closed
#print axioms CategoryTheory.IsShiftBy.hom_inv
#print axioms CategoryTheory.IsShiftBy.inv
#print axioms CategoryTheory.IsShiftBy.inv_closed
#print axioms CategoryTheory.IsShiftBy.inv_hom
#print axioms CategoryTheory.IsShiftBy.mapShift
#print axioms CategoryTheory.IsShiftBy.mapShift_comp
#print axioms CategoryTheory.IsShiftBy.mapShift_id
#print axioms CategoryTheory.IsShiftBy.mapShift_mem_cocycles
#print axioms CategoryTheory.IsShiftBy.mk.inj
#print axioms CategoryTheory.IsShiftBy.mk.sizeOf_spec
#print axioms CategoryTheory.IsShiftBy.self
#print axioms CategoryTheory.Z0
#print axioms CategoryTheory.Z0.category
#print axioms CategoryTheory.Z0.comp_mem
#print axioms CategoryTheory.Z0.comp_val
#print axioms CategoryTheory.Z0.id_val
#print axioms CategoryTheory.Z0.of
#print axioms CategoryTheory.Z0.toH0
#print axioms CategoryTheory.coboundaries
#print axioms CategoryTheory.coboundaries_le_cocycles
#print axioms CategoryTheory.coboundary_comp_mem
#print axioms CategoryTheory.cocycles
#print axioms CategoryTheory.compRight
#print axioms CategoryTheory.compRight.congr_simp
#print axioms CategoryTheory.compRight_apply
#print axioms CategoryTheory.compRight_comm
#print axioms CategoryTheory.comp_coboundary_mem
#print axioms CategoryTheory.comp_sub_mem
#print axioms CategoryTheory.constComplex
#print axioms CategoryTheory.constComplex_X_coe
#print axioms CategoryTheory.constComplex_d
#print axioms CategoryTheory.dgComp_closed
#print axioms CategoryTheory.mem_coboundaries_iff
#print axioms CategoryTheory.mem_cocycles_iff
#print axioms CategoryTheory.prodComp
#print axioms CategoryTheory.prodComp_apply
#print axioms CategoryTheory.prodComplex
#print axioms CategoryTheory.prodComplex_X_coe
#print axioms CategoryTheory.prodComplex_d
#print axioms CategoryTheory.prodD

-- dg-enhancements-e6: the shift functor on H0, its zero and add comparison
-- isomorphisms, all three ShiftMkCore coherence identities, and the resulting
-- HasShift (H0 C) instance.
#print axioms CategoryTheory.H0.compareIso
#print axioms CategoryTheory.H0.hasShift
#print axioms CategoryTheory.H0.shiftCompWitness
#print axioms CategoryTheory.H0.shiftCompWitness'
#print axioms CategoryTheory.H0.shiftFunctor
#print axioms CategoryTheory.H0.shiftFunctorAddIso
#print axioms CategoryTheory.H0.shiftFunctorAddIso'
#print axioms CategoryTheory.H0.shiftFunctorAddIso'_assoc
#print axioms CategoryTheory.H0.shiftFunctorAddIso'_hom_app_congr
#print axioms CategoryTheory.H0.shiftFunctorAddIso'_hom_app_zero_left
#print axioms CategoryTheory.H0.shiftFunctorAddIso'_hom_app_zero_right
#print axioms CategoryTheory.H0.shiftFunctorZeroIso
#print axioms CategoryTheory.H0.shiftFunctor_additive
#print axioms CategoryTheory.H0.shiftFunctor_map_mk
#print axioms CategoryTheory.H0.shiftMkCore
#print axioms CategoryTheory.IsPretriangulated.shiftObj
#print axioms CategoryTheory.IsPretriangulated.shiftWitness
#print axioms CategoryTheory.IsShiftBy.comp'
#print axioms CategoryTheory.IsShiftBy.comp'.congr_simp
#print axioms CategoryTheory.IsShiftBy.comp'_assoc_hom
#print axioms CategoryTheory.IsShiftBy.comp'_hom
#print axioms CategoryTheory.IsShiftBy.comp'_inv
#print axioms CategoryTheory.IsShiftBy.comp'_self_left_inv
#print axioms CategoryTheory.IsShiftBy.comp'_self_right_inv
#print axioms CategoryTheory.IsShiftBy.comp_eq_comp'
#print axioms CategoryTheory.IsShiftBy.comp_hom
#print axioms CategoryTheory.IsShiftBy.comp_inv
#print axioms CategoryTheory.IsShiftBy.compare_comp'_right
#print axioms CategoryTheory.IsShiftBy.compare_congr
#print axioms CategoryTheory.IsShiftBy.compare_self
#print axioms CategoryTheory.IsShiftBy.compare_trans
#print axioms CategoryTheory.IsShiftBy.inv_unique
#print axioms CategoryTheory.IsShiftBy.mapShiftHom
#print axioms CategoryTheory.IsShiftBy.mapShiftHom_apply
#print axioms CategoryTheory.IsShiftBy.mapShift_add
#print axioms CategoryTheory.IsShiftBy.mapShift_comp'_shift
#print axioms CategoryTheory.IsShiftBy.mapShift_comp_shift
#print axioms CategoryTheory.IsShiftBy.mapShift_compare
#print axioms CategoryTheory.IsShiftBy.mapShift_compare_comp
#print axioms CategoryTheory.IsShiftBy.mapShift_compare_comp'
#print axioms CategoryTheory.IsShiftBy.mapShift_mem_coboundaries
#print axioms CategoryTheory.IsShiftBy.mapShift_self
#print axioms CategoryTheory.IsShiftBy.self_inv

-- The maps *out* of a dg cone (dg-enhancements-e6). `IsConeOf` gives the universal
-- property for maps into the cone; the triangle needs the projections, and the
-- projection to the source is closed for a reason -- uniqueness of the splitting --
-- rather than by assumption.
#print axioms CategoryTheory.IsConeOf.splitId
#print axioms CategoryTheory.IsConeOf.fst
#print axioms CategoryTheory.IsConeOf.snd
#print axioms CategoryTheory.IsConeOf.fst_inl_add_snd_inr
#print axioms CategoryTheory.IsConeOf.delta_splitId_key
#print axioms CategoryTheory.IsConeOf.delta_fst
#print axioms CategoryTheory.IsConeOf.inr_comp_fst_and_snd
#print axioms CategoryTheory.IsConeOf.inr_comp_fst
#print axioms CategoryTheory.IsConeOf.inr_comp_snd
#print axioms CategoryTheory.IsConeOf.toShift
#print axioms CategoryTheory.IsConeOf.toShift_closed
#print axioms CategoryTheory.IsConeOf.toShift_mem_cocycles
#print axioms CategoryTheory.IsConeOf.inr_comp_toShift

-- The cone on an identity is contractible: the primitive is `snd` composed with
-- `inl`, and both of the cone's differential corrections are consumed exactly.
#print axioms CategoryTheory.IsConeOf.delta_fst_and_snd
#print axioms CategoryTheory.IsConeOf.delta_snd
#print axioms CategoryTheory.IsConeOf.dgId_mem_coboundaries_of_dgId

-- The distinguished triangles of H⁰, and three of the six Pretriangulated fields.
#print axioms CategoryTheory.H0.homMk
#print axioms CategoryTheory.H0.shiftFunctor_additive'
#print axioms CategoryTheory.H0.coneTriangle
#print axioms CategoryTheory.H0.distinguishedTriangles
#print axioms CategoryTheory.H0.coneTriangle_mem
#print axioms CategoryTheory.H0.isomorphic_distinguished
#print axioms CategoryTheory.H0.distinguished_cocone_triangle
#print axioms CategoryTheory.H0.isZero_of_dgId_mem_coboundaries
#print axioms CategoryTheory.H0.contractible_distinguished
