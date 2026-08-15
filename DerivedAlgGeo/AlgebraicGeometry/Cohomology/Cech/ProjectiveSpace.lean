/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.ProjectiveSpace
import DerivedAlgGeo.Topology.Opens.Limits
import DerivedAlgGeo.Algebra.Category.Grp.Products
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# The Čech complex of `O(d)` on polynomial projective space, degreewise

`cechCochainsDegreewiseAddEquiv` identifies degree `n` of Mathlib's Čech complex of `O(d)`,
taken over the variable chart cover, with `polynomialVariableCechCochains` — the explicit
product of homogeneous degree-zero localizations.

## Main definitions

* `polynomialVariableChart` — the variable basic-open cover of polynomial `Proj`;
* `twistPresheaf` — the `AddCommGrpCat`-valued presheaf of `O(d)`, which is what Mathlib's
  Čech complex consumes;
* `cechCochainsDegreewiseAddEquiv` — the degreewise comparison.

## Main statements

* `piObj_polynomialVariableChart` — the categorical product of the charts along a Čech index
  is the basic open of the product denominator.

## Implementation notes

Three shape mismatches separate the two sides, and each is resolved by a different mechanism.

**The outer product.** Degree `n` of the Čech complex is a categorical product `∏ᶜ` in
`AddCommGrpCat`, indexed by `Fin (n + 1) → ι`, while `polynomialVariableCechCochains` is a Pi
type. `AddCommGrpCat.piAddEquivPi` bridges them. That is the whole reason it exists; note the
`AddEquiv` form is needed rather than `piIsoPi`, because the next step is
`AddEquiv.piCongrRight` and `piIsoPi`'s codomain is a bundled object.

**The inner product.** The Čech term evaluates the presheaf on `∏ᶜ (U ∘ x)`, a categorical
product in `Opens`, whereas the algebraic side names the open as a single basic open.
`piObj_polynomialVariableChart` identifies them: the product in `Opens` is the infimum (the
category is a complete lattice), and `basicOpen_polynomialVariableCechDenominator` already says
the infimum of the charts is the basic open of the product. This is an equality of opens, not
merely an isomorphism, so it transports through `eqToIso` rather than a comparison map.

**The coefficients.** `cechTermSectionAddEquiv` lands in the `Type`-valued sheaf, while the
Čech complex needs the `AddCommGrpCat`-valued presheaf. No conversion is required:
`associatedPresheafInAddCommGrp` is defined by bundling exactly that section type, so the two
are definitionally equal and the per-index equivalence is reused unchanged.

Degree `n` of the complex is *definitionally* the product over `Fin (n + 1) → ι` — no `dsimp`
or unfolding lemma is needed to expose it, and `AddCommGrpCat.piAddEquivPi` applies to it
directly.

This is a degreewise statement only. Promoting it to an isomorphism of cochain complexes needs
the Čech differential transported through it, which is separate work; nothing here asserts
compatibility with the differential.

## Tags

Čech complex, projective space, twisting sheaf, homogeneous localization
-/

noncomputable section

open CategoryTheory Limits DirectSum Opposite SetLike TopCat TopologicalSpace

namespace AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι k : Type u) [Field k]

/-- The variable basic-open cover of polynomial `Proj`: the chart where the `i`-th coordinate
is invertible. This is the cover the algebraic Čech terms are indexed by. -/
def polynomialVariableChart :
    ι → Opens (ProjectiveSpectrum.top (polynomialGrading ι k)) :=
  fun i => ProjectiveSpectrum.basicOpen (polynomialGrading ι k) (MvPolynomial.X i)

/-- The `AddCommGrpCat`-valued presheaf of `O(d)` on polynomial `Proj`.

Mathlib's Čech complex is built from a presheaf valued in a preadditive category with products,
so the `Type`-valued sheaf that the section comparisons are stated against cannot be used
directly. Its underlying type is unchanged, which is what lets `cechTermSectionAddEquiv` be
reused here without a conversion step. -/
abbrev twistPresheaf (d : ℕ) :=
  associatedPresheafInAddCommGrp (polynomialGrading ι k)
    (natShift (polynomialGrading ι k) d)

/-- The categorical product of the charts along a Čech index is the basic open of the product
denominator.

The product in `Opens` is the infimum, because the category is a complete lattice; the rest is
`basicOpen_polynomialVariableCechDenominator`. The conclusion is an equality of opens rather
than an isomorphism, which is what lets the presheaf be transported across it by `eqToIso`. -/
theorem piObj_polynomialVariableChart {n : ℕ} (x : Fin (n + 1) → ι) :
    (∏ᶜ (polynomialVariableChart ι k ∘ x)) =
      ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k x) := by
  rw [basicOpen_polynomialVariableCechDenominator]
  apply le_antisymm
  · exact le_iInf fun a => leOfHom (Pi.π (polynomialVariableChart ι k ∘ x) a)
  · exact leOfHom (Pi.lift fun a => homOfLE (iInf_le _ a))

/-- Degree `n` of the Čech complex of `O(d)` over the variable charts is the explicit product of
homogeneous degree-zero localizations.

The three factors are the outer product (`AddCommGrpCat.piAddEquivPi`), the identification of
the open (`piObj_polynomialVariableChart`, transported by `eqToIso`), and the per-index section
comparison (`cechTermSectionAddEquiv`). Degreewise only — the Čech differential is not claimed
to correspond. -/
def cechCochainsDegreewiseAddEquiv (d n : ℕ) :
    (((cechComplexFunctor (polynomialVariableChart ι k)).obj
        (twistPresheaf ι k d)).X n : AddCommGrpCat) ≃+
      polynomialVariableCechCochains ι k d n :=
  (AddCommGrpCat.piAddEquivPi _).trans
    (AddEquiv.piCongrRight fun x =>
      (eqToIso (congrArg (fun W => (twistPresheaf ι k d).obj (op W))
          (piObj_polynomialVariableChart ι k x))).addCommGroupIsoToAddEquiv.trans
        (cechTermSectionAddEquiv ι k d x).symm)

end AlgebraicGeometry.Proj
