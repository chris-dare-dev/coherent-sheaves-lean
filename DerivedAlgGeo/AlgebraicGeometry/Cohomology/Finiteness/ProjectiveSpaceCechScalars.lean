/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Finiteness.ProjectiveSpaceScalars
import DerivedAlgGeo.AlgebraicGeometry.Cohomology.Cech.TopDegree

/-!
# The per-index Čech comparison is `k`-linear

`intCechTermSectionAddEquiv_smul` says the comparison between a Čech *term* and its sections
respects the base-field action. `intCechIndexEquiv` is that comparison composed with one
transport, because a Čech index names sections over a categorical product of charts while the
term comparison is stated over a basic open, and `piObj_polynomialVariableChart` only says those
two opens are *equal*. This file carries the linearity across that transport.

## The transport is the whole content

`eqToIso_transport_varietyScalarAction` is `subst h; rfl` — moving sections along an equality of
opens cannot fail to commute with anything. What makes it worth stating separately is that it has
to be phrased against the **sheaf endomorphism** rather than against `•`: a `•` whose left factor
is `Γ(Proj 𝒜, W)` leaves instance search stuck, because that type and the structure sheaf's
sections at `W` are defeq without guiding search to the same `Module`. Stating both sides with
`varietyScalarAction`'s `app` sidesteps it, and `varietyScalarAction_app_eq` converts back
afterwards.

That friction has now appeared four times in this lane — `cechBlockSpan`, `constSection`,
`constSectionOn`, and here.

## Next

Degreewise linearity of `intCechCochainsDegreewiseAddEquiv` is a product of this over the tuple
index; the homology statement `r • [s] = [r • s]` is then `homologyπ` naturality. Neither is here.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι k : Type u) [Field k] [Finite ι] [Nonempty ι]

/-- Transport along an equality of opens commutes with the endomorphism a scalar induces. -/
theorem eqToIso_transport_varietyScalarAction (d : ℤ)
    {W W' : Opens (ProjectiveSpectrum.top (polynomialGrading ι k))} (h : W = W') (r : k)
    (s : (intTwistPresheaf ι k d).obj (op W)) :
    (eqToIso (congrArg (fun V => (intTwistPresheaf ι k d).obj (op V)) h)
        ).addCommGroupIsoToAddEquiv
        (((Cohomology.varietyScalarAction (projectiveSpaceVariety ι k)
            (associatedSheaf (polynomialGrading ι k)
              (intShift (polynomialGrading ι k) d)) r).val.app (op W)).hom s) =
      ((Cohomology.varietyScalarAction (projectiveSpaceVariety ι k)
          (associatedSheaf (polynomialGrading ι k)
            (intShift (polynomialGrading ι k) d)) r).val.app (op W')).hom
        ((eqToIso (congrArg (fun V => (intTwistPresheaf ι k d).obj (op V)) h)
          ).addCommGroupIsoToAddEquiv s) := by
  subst h; rfl

/-- The symm form of the term-level comparison lemma, against the sheaf endomorphism. -/
theorem intCechTermSectionAddEquiv_symm_varietyScalarAction (d : ℤ) {n : ℕ}
    (x : Fin (n + 1) → ι) (r : k)
    (w : (associatedSheafInType (polynomialGrading ι k)
      (intShift (polynomialGrading ι k) d)).1.obj
      (op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k x)))) :
    (intCechTermSectionAddEquiv ι k d x).symm
        (((Cohomology.varietyScalarAction (projectiveSpaceVariety ι k)
            (associatedSheaf (polynomialGrading ι k)
              (intShift (polynomialGrading ι k) d)) r).val.app _).hom w) =
      r • (intCechTermSectionAddEquiv ι k d x).symm w := by
  refine (congrArg (intCechTermSectionAddEquiv ι k d x).symm
    (varietyScalarAction_app_eq ι k (intShift (polynomialGrading ι k) d) r _ w)).trans ?_
  apply (intCechTermSectionAddEquiv ι k d x).injective
  rw [AddEquiv.apply_symm_apply, intCechTermSectionAddEquiv_smul, AddEquiv.apply_symm_apply]
  rfl

/-- **The per-index comparison is `k`-linear.** -/
theorem intCechIndexEquiv_smul (d : ℤ) {n : ℕ} (x : Fin (n + 1) → ι) (r : k)
    (s : (intTwistPresheaf ι k d).obj (op (∏ᶜ (polynomialVariableChart ι k ∘ x)))) :
    intCechIndexEquiv ι k d x
        (((Cohomology.varietyScalarAction (projectiveSpaceVariety ι k)
            (associatedSheaf (polynomialGrading ι k)
              (intShift (polynomialGrading ι k) d)) r).val.app
          (op (∏ᶜ (polynomialVariableChart ι k ∘ x)))).hom s) =
      r • intCechIndexEquiv ι k d x s := by
  refine Eq.trans (congrArg (intCechTermSectionAddEquiv ι k d x).symm
    (eqToIso_transport_varietyScalarAction ι k d (piObj_polynomialVariableChart ι k x) r s)) ?_
  exact intCechTermSectionAddEquiv_symm_varietyScalarAction ι k d x r _

end AlgebraicGeometry.Proj
