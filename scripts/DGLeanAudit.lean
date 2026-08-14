/-
Axiom + sorry audit over a HAND-MAINTAINED LIST of this library's declarations.

Run: `lake env lean scripts/DGLeanAudit.lean` (to read the output), or
`lake build DGLeanAudit` (to check it still elaborates).

The same shape as `scripts/BridgelandAudit.lean`, and gated the same way:

    lake env lean scripts/DGLeanAudit.lean > dg-audit.txt 2>&1
    python3 scripts/check_audit.py dg-audit.txt scripts/DGLeanAudit.lean

`#print axioms` prints `[sorryAx]` and exits 0, so being in the build is not
being a gate -- `check_audit.py` is what fails on an axiom outside the trusted
three, on `sorryAx`, on an empty sweep, and on this file falling behind the
source tree.

`DGLean` was gated from its first commit rather than retrofitted. `CohLean`
went the other way and needed a 203-entry `scripts/nolints.json` ratchet to
catch up; this list starts complete and should stay that way.
-/
import DGLean

#print axioms Const
#print axioms Const.dgCategory
#print axioms DGCategory
#print axioms DGCategory.dgComp_assoc
#print axioms DGCategory.dgComp_id
#print axioms DGCategory.dgComp_leibniz
#print axioms DGCategory.dgComp_units_smul_left
#print axioms DGCategory.dgComp_units_smul_right
#print axioms DGCategory.dgId_cocycle
#print axioms DGCategory.dgId_comp
#print axioms DGCategory.dgProd_fst_add
#print axioms DGCategory.dgProd_fst_units_smul
#print axioms DGCategory.dgProd_snd_add
#print axioms DGCategory.dgProd_snd_units_smul
#print axioms DGCategory.hom_units_smul
#print axioms DGCategory.op
#print axioms DGCategory.opStruct
#print axioms DGCategory.op_dgComp_apply
#print axioms DGCategory.op_dgHom
#print axioms DGCategory.op_dgId
#print axioms DGCategory.prod
#print axioms DGCategory.prodStruct
#print axioms DGCategory.prod_d_apply
#print axioms DGCategory.prod_dgComp_apply
#print axioms DGCategory.prod_dgId
#print axioms DGCategory.toDGCategoryStruct
#print axioms DGCategoryStruct
#print axioms DGCategoryStruct.dgComp
#print axioms DGCategoryStruct.dgComp.congr_simp
#print axioms DGCategoryStruct.dgHom
#print axioms DGCategoryStruct.dgId
#print axioms DGFunctor
#print axioms DGFunctor.comp
#print axioms DGFunctor.comp_map
#print axioms DGFunctor.comp_obj
#print axioms DGFunctor.id
#print axioms DGFunctor.id_map
#print axioms DGFunctor.id_obj
#print axioms DGFunctor.map
#print axioms DGFunctor.map_comp
#print axioms DGFunctor.map_d
#print axioms DGFunctor.map_id
#print axioms DGFunctor.mk.inj
#print axioms DGFunctor.mk.sizeOf_spec
#print axioms DGFunctor.obj
#print axioms DGLinear
#print axioms DGLinear.comp_smul_left
#print axioms DGLinear.comp_smul_right
#print axioms DGLinear.d_smul
#print axioms constComplex
#print axioms constComplex_X_coe
#print axioms constComplex_d
#print axioms prodComp
#print axioms prodComp_apply
#print axioms prodComplex
#print axioms prodComplex_X_coe
#print axioms prodComplex_d
#print axioms prodD
#print axioms DGFunctor.IsQuasiEquivalence
#print axioms DGFunctor.IsQuasiEquivalence.essSurj
#print axioms DGFunctor.IsQuasiEquivalence.quasiIso
#print axioms DGFunctor.h0
#print axioms DGFunctor.h0CompIso
#print axioms DGFunctor.h0IdIso
#print axioms DGFunctor.h0_map_mk
#print axioms DGFunctor.h0_obj
#print axioms DGFunctor.mapComplex
#print axioms DGFunctor.map_mem_coboundaries
#print axioms DGFunctor.map_mem_cocycles
#print axioms H0
#print axioms H0.category
#print axioms H0.coboundariesIn
#print axioms H0.of
#print axioms H0.of_self
#print axioms H0.preadditive
#print axioms Z0
#print axioms Z0.category
#print axioms Z0.comp_mem
#print axioms Z0.comp_val
#print axioms Z0.id_val
#print axioms Z0.of
#print axioms Z0.toH0
#print axioms coboundaries
#print axioms coboundaries_le_cocycles
#print axioms coboundary_comp_mem
#print axioms cocycles
#print axioms comp_coboundary_mem
#print axioms comp_sub_mem
#print axioms mem_coboundaries_iff
#print axioms mem_cocycles_iff
