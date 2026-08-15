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
#print axioms CategoryTheory.Cdg.cocycleAddEquiv
#print axioms CategoryTheory.Cdg.cocycles_eq
#print axioms CategoryTheory.Cdg.delta_shift_sign_agrees
#print axioms CategoryTheory.Cdg.dgComp_eq
#print axioms CategoryTheory.Cdg.dgHom_eq
#print axioms CategoryTheory.Cdg.dgId_eq
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
#print axioms CategoryTheory.Cdg.mem_coboundaries_iff'
#print axioms CategoryTheory.Cdg.of
#print axioms CategoryTheory.Cdg.ofCocycle
#print axioms CategoryTheory.Cdg.ofCocycle_toCocycle
#print axioms CategoryTheory.Cdg.ofCocycle_val
#print axioms CategoryTheory.Cdg.postcompAddEquiv
#print axioms CategoryTheory.Cdg.quotient_map_homOf_eq
#print axioms CategoryTheory.Cdg.seam
#print axioms CategoryTheory.Cdg.shiftComp_eq
#print axioms CategoryTheory.Cdg.shiftD_eq
#print axioms CategoryTheory.Cdg.struct
#print axioms CategoryTheory.Cdg.toCocycle
#print axioms CategoryTheory.Cdg.toCocycle_ofCocycle
#print axioms CategoryTheory.Cdg.toCocycle_val
#print axioms CategoryTheory.Const
#print axioms CategoryTheory.Const.dgCategory
#print axioms CategoryTheory.DGCategory
#print axioms CategoryTheory.DGCategory.coneHom
#print axioms CategoryTheory.DGCategory.coneHomXIso
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
#print axioms CategoryTheory.DGCategory.postcomp
#print axioms CategoryTheory.DGCategory.postcompHom
#print axioms CategoryTheory.DGCategory.postcompHom_apply
#print axioms CategoryTheory.DGCategory.postcompHom_comm
#print axioms CategoryTheory.DGCategory.postcomp_f
#print axioms CategoryTheory.DGCategory.precomp
#print axioms CategoryTheory.DGCategory.precompHom
#print axioms CategoryTheory.DGCategory.precompHom_apply
#print axioms CategoryTheory.DGCategory.precompHom_comm
#print axioms CategoryTheory.DGCategory.precomp_f
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
#print axioms CategoryTheory.H0
#print axioms CategoryTheory.H0.category
#print axioms CategoryTheory.H0.coboundariesIn
#print axioms CategoryTheory.H0.of
#print axioms CategoryTheory.H0.of_self
#print axioms CategoryTheory.H0.preadditive
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
#print axioms CategoryTheory.comp_coboundary_mem
#print axioms CategoryTheory.comp_sub_mem
#print axioms CategoryTheory.constComplex
#print axioms CategoryTheory.constComplex_X_coe
#print axioms CategoryTheory.constComplex_d
#print axioms CategoryTheory.mem_coboundaries_iff
#print axioms CategoryTheory.mem_cocycles_iff
#print axioms CategoryTheory.prodComp
#print axioms CategoryTheory.prodComp_apply
#print axioms CategoryTheory.prodComplex
#print axioms CategoryTheory.prodComplex_X_coe
#print axioms CategoryTheory.prodComplex_d
#print axioms CategoryTheory.prodD
