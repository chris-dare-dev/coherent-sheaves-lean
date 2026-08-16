/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.ProjectiveSpace
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.Boundedness

/-!
# The variable cover of projective space is Čech-acyclic

For polynomial projective space over a field, the standard cover by the variable charts
`D₊(Xᵢ)` is Čech-acyclic for every quasi-coherent associated sheaf, and in particular for every
nonnegative twist.  This is the hypothesis that the
Čech-to-derived comparison of
`DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.GlobalComparison` consumes, so with it
`Hⁱ(Pⁿ, O(d))` is the cohomology of an explicit complex of degree-zero homogeneous
localizations.

Three inputs meet here, and none of them is new:

* quasi-coherence of the sheaf — the only place a twist enters at all, which is why the results
  are stated with it as a hypothesis and the `O(d)` case is a corollary supplying
  `polynomialNatShift_isQuasicoherent`. A negative twist becomes acyclic here the moment its
  quasi-coherence is available, with no change to this argument (see issue #439);
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

namespace AlgebraicGeometry.Proj

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
quasi-coherent associated sheaf has no positive cohomology.

The `(n+1)`-fold intersection is the basic open of `∏ₐ X_{x a}`, homogeneous of degree `n + 1`,
so it is affine for every `n`. Nothing else about the sheaf is used, which is why the hypothesis
is quasi-coherence rather than a twist: the degree restriction that constrains the
*trivialization* of `O(d)` does not constrain this argument at all. Any twist whose
quasi-coherence is known — integer twists included, once that is available — is acyclic here for
the same reason. -/
theorem polynomialVariable_isCechAcyclicFor_of_isQuasicoherent
    (ι k : Type u) [Field k] {M σM : Type u}
    [AddCommGroup M] [Module (MvPolynomial ι k) M]
    [SetLike σM M] [AddSubgroupClass σM M]
    (𝓜 : ℕ → σM) [SetLike.GradedSMul (polynomialGrading ι k) 𝓜]
    (hqc : (associatedSheaf (polynomialGrading ι k) 𝓜).IsQuasicoherent)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u}
      (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k)))] :
    @CategoryTheory.Sheaf.IsCechAcyclicFor
      (Opens (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k))) _
      (Opens.grothendieckTopology (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k))) _
      hExt ι _
      (fun i : ι => _root_.AlgebraicGeometry.Proj.basicOpen (polynomialGrading ι k)
        (MvPolynomial.X i))
      ((_root_.AlgebraicGeometry.Scheme.Modules.toSheaf _).obj
        (associatedSheaf (polynomialGrading ι k) 𝓜)) := by
  haveI := hqc
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
    (associatedSheaf (polynomialGrading ι k) 𝓜)
    (_root_.AlgebraicGeometry.Proj.basicOpen (polynomialGrading ι k)
      (polynomialVariableCechDenominator ι k x))
    (_root_.AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ _
      (polynomialVariableCechDenominator_mem ι k x) (Nat.succ_pos n)) q hq
  rwa [← hprod] at hvanish

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The nonnegative twist `O(d)` is acyclic on every variable Čech intersection.

This is `polynomialVariable_isCechAcyclicFor_of_isQuasicoherent` with the quasi-coherence of a
nonnegative twist supplied. -/
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
          (natShift (polynomialGrading ι k) d))) :=
  polynomialVariable_isCechAcyclicFor_of_isQuasicoherent ι k
    (natShift (polynomialGrading ι k) d) (polynomialNatShift_isQuasicoherent ι k d)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The variable cover is a Čech-acyclic cover for any quasi-coherent associated sheaf: it
covers, and the sheaf is acyclic on every nonempty finite intersection.

This is exactly the hypothesis of
`CategoryTheory.Sheaf.isCechAcyclicCover_cechComputesDerivedCohomology`, so the Čech cohomology
of the variable cover is the derived cohomology in every degree. -/
theorem polynomialVariable_isCechAcyclicCover_of_isQuasicoherent
    (ι k : Type u) [Field k] {M σM : Type u}
    [AddCommGroup M] [Module (MvPolynomial ι k) M]
    [SetLike σM M] [AddSubgroupClass σM M]
    (𝓜 : ℕ → σM) [SetLike.GradedSMul (polynomialGrading ι k) 𝓜]
    (hqc : (associatedSheaf (polynomialGrading ι k) 𝓜).IsQuasicoherent)
    [hExt : HasExt.{u + 1} (TopCat.Sheaf AddCommGrpCat.{u}
      (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k)))] :
    @CategoryTheory.Sheaf.IsCechAcyclicCover
      (Opens (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k))) _
      (Opens.grothendieckTopology (_root_.AlgebraicGeometry.Proj (polynomialGrading ι k))) _
      hExt ι _
      (fun i : ι => _root_.AlgebraicGeometry.Proj.basicOpen (polynomialGrading ι k)
        (MvPolynomial.X i))
      ((_root_.AlgebraicGeometry.Scheme.Modules.toSheaf _).obj
        (associatedSheaf (polynomialGrading ι k) 𝓜)) :=
  ⟨polynomialVariable_coversTop ι k,
    polynomialVariable_isCechAcyclicFor_of_isQuasicoherent ι k 𝓜 hqc⟩

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
  polynomialVariable_isCechAcyclicCover_of_isQuasicoherent ι k
    (natShift (polynomialGrading ι k) d) (polynomialNatShift_isQuasicoherent ι k d)

end AlgebraicGeometry.Proj
