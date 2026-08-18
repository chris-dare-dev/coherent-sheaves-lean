/-
Pretriangulated-axioms slice of the StabilityCondition audit, split out so
concurrent branches append to different files (#480). See the umbrella file for
the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.PretriangulatedAxioms

/-! ## The pretriangulated axioms, with rotation only forward (dg-enhancements-e6)

The reverse direction of `rotate_distinguished_triangle` is a theorem about the
other four axioms rather than a construction, so it is proved once here and
every category that supplies the forward half gets the class.
-/

#print axioms CategoryTheory.Pretriangulated.exists_lift_of_iso
#print axioms CategoryTheory.Pretriangulated.Axioms
#print axioms CategoryTheory.Pretriangulated.Axioms.isomorphic
#print axioms CategoryTheory.Pretriangulated.Axioms.contractible
#print axioms CategoryTheory.Pretriangulated.Axioms.cocone
#print axioms CategoryTheory.Pretriangulated.Axioms.rotate
#print axioms CategoryTheory.Pretriangulated.Axioms.complete
#print axioms CategoryTheory.Pretriangulated.Axioms.comp_eq_zero₁₂
#print axioms CategoryTheory.Pretriangulated.Axioms.exists_lift₁
#print axioms CategoryTheory.Pretriangulated.Axioms.coyoneda_exact₂
#print axioms CategoryTheory.Pretriangulated.Axioms.mem_of_rotate_mem
#print axioms CategoryTheory.Pretriangulated.Axioms.pretriangulated
