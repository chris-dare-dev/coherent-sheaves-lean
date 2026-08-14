/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import CohLean.AlgebraicGeometry.Proj.Modules.ProjectiveSpace
import CohLean.Cohomology.Finiteness.Boundedness

/-!
# The variable cover of projective space is Čech-acyclic for `O(d)`

For polynomial projective space over a field, the standard cover by the variable charts
`D₊(Xᵢ)` is Čech-acyclic for every nonnegative twist.  This is the hypothesis that the
Čech-to-derived comparison of `CohLean.Cohomology.Cech.GlobalComparison` consumes, so with it
`Hⁱ(Pⁿ, O(d))` is the cohomology of an explicit complex of degree-zero homogeneous
localizations.

Three inputs meet here, and none of them is new:

* `polynomialNatShift_isQuasicoherent` — `O(d)` is quasi-coherent, glued from the degree-one
  variable charts alone;
* `AlgebraicGeometry.Proj.isAffineOpen_basicOpen` — a basic open of a positive-degree
  homogeneous element is affine, which covers the `(n+1)`-fold Čech intersections because their
  denominator `∏ₐ X_{x a}` is homogeneous of degree `n + 1`;
* `AlgebraicGeometry.Cohomology.modules_HPrime_subsingleton_of_isAffineOpen` — positive local
  cohomology of a quasi-coherent module vanishes on an affine open, against the ambient
  `Sheaf.H'` rather than a model.

The `HasExt` witness is passed positionally throughout.  `Sheaf.H'` lands in the `HasExt`
universe, and the affine-vanishing result is stated at `HasExt.{u + 1}`; leaving the instance to
be found would let the small-site `HasExt.{u}` be selected instead, giving a statement about
different groups.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace CohLean.AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The variable basic opens cover polynomial projective space, as a covering family for the
open-set Grothendieck topology. -/
theorem polynomialVariable_coversTop (ι k : Type u) [Field k] :
    (Opens.grothendieckTopology
      (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k))).CoversTop
      (fun i : ι => _root_.AlgebraicGeometry.Proj.basicOpen (polynomialGrading ι k)
        (MvPolynomial.X i)) := by
  apply TopCat.Opens.grothendieckTopology_coversTop
  exact polynomialVariableBasicOpen_cover ι k

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Every nonempty finite intersection in the variable Čech nerve is an affine open, on which a
nonnegative twist has no positive cohomology.

The `(n+1)`-fold intersection is the basic open of `∏ₐ X_{x a}`, homogeneous of degree `n + 1`,
so it is affine for every `n`; the degree restriction that constrains the *trivialization* of
`O(d)` does not constrain this. -/
theorem polynomialVariable_isCechAcyclicFor (ι k : Type u) [Field k] (d : ℕ)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u}
      (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k)))] :
    @CategoryTheory.Sheaf.IsCechAcyclicFor
      (Opens (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k))) _
      (Opens.grothendieckTopology (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k))) _
      hExt ι _
      (fun i : ι => _root_.AlgebraicGeometry.Proj.basicOpen (polynomialGrading ι k)
        (MvPolynomial.X i))
      ((_root_.AlgebraicGeometry.Scheme.Modules.toSheaf _).obj
        (associatedSheaf (polynomialGrading ι k)
          (natShift (polynomialGrading ι k) d))) := by
  haveI := polynomialNatShift_isQuasicoherent ι k d
  intro q hq n x
  have hprod : (∏ᶜ fun a : Fin (n + 1) =>
        _root_.AlgebraicGeometry.Proj.basicOpen (polynomialGrading ι k) (MvPolynomial.X (x a))) =
      _root_.AlgebraicGeometry.Proj.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k x) := by
    have hbase : (⨅ a : Fin (n + 1), ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
          (MvPolynomial.X (x a))) =
        ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
          (polynomialVariableCechDenominator ι k x) :=
      (basicOpen_polynomialVariableCechDenominator ι k x).symm
    exact le_antisymm
      (le_of_le_of_eq (le_iInf fun a => leOfHom (Pi.π _ a)) hbase)
      (le_of_eq_of_le hbase.symm (leOfHom (Pi.lift fun a => homOfLE (iInf_le _ a))))
  have hvanish := _root_.AlgebraicGeometry.Cohomology.modules_HPrime_subsingleton_of_isAffineOpen
    (associatedSheaf (polynomialGrading ι k) (natShift (polynomialGrading ι k) d))
    (_root_.AlgebraicGeometry.Proj.basicOpen (polynomialGrading ι k)
      (polynomialVariableCechDenominator ι k x))
    (_root_.AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ _
      (polynomialVariableCechDenominator_mem ι k x) (Nat.succ_pos n)) q hq
  rwa [← hprod] at hvanish

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The variable cover is a Čech-acyclic cover for every nonnegative twist: it covers, and the
twist is acyclic on every nonempty finite intersection.

This is exactly the hypothesis of
`CategoryTheory.Sheaf.isCechAcyclicCover_cechComputesDerivedCohomology`, so `Hⁱ(Pⁿ, O(d))` is
the Čech cohomology of the variable cover in every degree. -/
theorem polynomialVariable_isCechAcyclicCover (ι k : Type u) [Field k] (d : ℕ)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u}
      (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k)))] :
    @CategoryTheory.Sheaf.IsCechAcyclicCover
      (Opens (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k))) _
      (Opens.grothendieckTopology (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k))) _
      hExt ι _
      (fun i : ι => _root_.AlgebraicGeometry.Proj.basicOpen (polynomialGrading ι k)
        (MvPolynomial.X i))
      ((_root_.AlgebraicGeometry.Scheme.Modules.toSheaf _).obj
        (associatedSheaf (polynomialGrading ι k)
          (natShift (polynomialGrading ι k) d))) :=
  ⟨polynomialVariable_coversTop ι k, polynomialVariable_isCechAcyclicFor ι k d⟩

end CohLean.AlgebraicGeometry.Proj
