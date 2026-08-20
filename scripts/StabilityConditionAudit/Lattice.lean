/-
Lattice slice of the StabilityCondition audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract and reading guide.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearYoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.LinearCoyoneda
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import DerivedAlgGeo.LinearAlgebra
open CategoryTheory.Triangulated

/-! ## Lattice lane -/

#print axioms IntegralLattice.NumLattice
#print axioms IntegralLattice.eq_zero_of_zsmul_eq_zero
#print axioms IntegralLattice.eq_zero_of_two_zsmul_eq_zero
#print axioms IntegralLattice.zsmul_injective
#print axioms IntegralLattice.zsmul_left_cancel
#print axioms IntegralLattice.finrank_numLattice
#print axioms IntegralLattice.ne_zero_of_apply_ne_zero
#print axioms IntegralLattice.eq_zero_of_two_zsmul_eq_zero_num

/-! ## Mukai lane — the extension `ℤ ⊕ N ⊕ ℤ` of a symmetric bilinear lattice

Pure lattice arithmetic. Nothing here is a statement about a K3 surface, a
Mukai lattice of a variety, or any geometric object; see the module docstrings
in `DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/`. -/

#print axioms Mukai.MukaiLattice
#print axioms Mukai.pairing
#print axioms Mukai.pairing_mk
#print axioms Mukai.pairing_add_left
#print axioms Mukai.pairing_add_right
#print axioms Mukai.pairing_smul_left
#print axioms Mukai.pairing_smul_right
#print axioms Mukai.pairing_neg_left
#print axioms Mukai.pairing_neg_right
#print axioms Mukai.pairing_sub_left
#print axioms Mukai.pairing_sub_right
#print axioms Mukai.pairing_zero_left
#print axioms Mukai.pairing_zero_right
#print axioms Mukai.pairing_comm
#print axioms Mukai.selfPairing
#print axioms Mukai.selfPairing_eq_pairing
#print axioms Mukai.selfPairing_mk
#print axioms Mukai.selfPairing_smul
#print axioms Mukai.selfPairing_zero
#print axioms Mukai.selfPairing_neg
#print axioms Mukai.even_selfPairing
#print axioms Mukai.IsSpherical
#print axioms Mukai.IsIsotropic
#print axioms Mukai.isSpherical_iff
#print axioms Mukai.isIsotropic_iff
#print axioms Mukai.IsSpherical.neg
#print axioms Mukai.IsIsotropic.neg
#print axioms Mukai.not_isSpherical_and_isIsotropic
#print axioms Mukai.expectedDim
#print axioms Mukai.expectedDim_eq_zero_iff
#print axioms Mukai.expectedDim_eq_two_iff
#print axioms Mukai.rankUnit
#print axioms Mukai.corankUnit
#print axioms Mukai.pairing_outer
#print axioms Mukai.isIsotropic_rankUnit
#print axioms Mukai.isIsotropic_corankUnit
#print axioms Mukai.pairing_rankUnit_corankUnit
#print axioms Mukai.pairingBilin
#print axioms Mukai.pairingBilin_apply

/-! ## Mukai lane — rank-two subpairs -/

#print axioms Mukai.gram
#print axioms Mukai.gram_comm
#print axioms Mukai.gram_zero_left
#print axioms Mukai.gram_zero_right
#print axioms Mukai.pairing_lincomb
#print axioms Mukai.selfPairing_lincomb
#print axioms Mukai.gram_lincomb
#print axioms Mukai.IsHyperbolicPair
#print axioms Mukai.isHyperbolicPair_iff
#print axioms Mukai.discr_pos_of_isHyperbolicPair
#print axioms Mukai.gram_ne_zero_of_isHyperbolicPair
#print axioms Mukai.ne_zero_left_of_isHyperbolicPair
#print axioms Mukai.ne_zero_right_of_isHyperbolicPair
#print axioms Mukai.isHyperbolicPair_comm
#print axioms Mukai.isHyperbolicPair_lincomb
#print axioms Mukai.orthWitness
#print axioms Mukai.pairing_orthWitness
#print axioms Mukai.selfPairing_orthWitness
#print axioms Mukai.selfPairing_orthWitness_neg
#print axioms Mukai.orthWitness_ne_zero
#print axioms Mukai.pairSpan
#print axioms Mukai.mem_pairSpan_left
#print axioms Mukai.mem_pairSpan_right
#print axioms Mukai.orthWitness_mem_pairSpan
#print axioms Mukai.HasSphericalClass
#print axioms Mukai.HasIsotropicClass
#print axioms Mukai.exists_neg_selfPairing_of_isHyperbolicPair


/-! ## Mukai lane — reflection in a spherical class

Still pure lattice arithmetic. `reflect` is a map of the abstract Mukai
extension; it is **not** the Seidel–Thomas spherical twist, and no autoequivalence
of any derived category is constructed or asserted. -/

#print axioms Mukai.reflect
#print axioms Mukai.reflect_apply
#print axioms Mukai.reflect_zero
#print axioms Mukai.reflect_add
#print axioms Mukai.reflect_smul
#print axioms Mukai.reflect_neg
#print axioms Mukai.reflectHom
#print axioms Mukai.reflectHom_apply
#print axioms Mukai.pairing_reflect_right
#print axioms Mukai.reflect_reflect
#print axioms Mukai.reflect_involutive
#print axioms Mukai.reflect_bijective
#print axioms Mukai.reflectEquiv
#print axioms Mukai.reflectEquiv_apply
#print axioms Mukai.reflectEquiv_symm_apply
#print axioms Mukai.reflect_self
#print axioms Mukai.reflect_of_pairing_eq_zero
#print axioms Mukai.pairing_reflect_eq_zero_iff
#print axioms Mukai.pairing_reflect_reflect
#print axioms Mukai.selfPairing_reflect
#print axioms Mukai.reflectIsometry
#print axioms Mukai.reflectIsometry_apply
#print axioms Mukai.IsSpherical.reflect
#print axioms Mukai.IsIsotropic.reflect
#print axioms Mukai.expectedDim_reflect
#print axioms Mukai.reflect_neg_left
