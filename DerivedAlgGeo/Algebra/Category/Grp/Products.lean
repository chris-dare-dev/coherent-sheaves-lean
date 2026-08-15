/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Tactic.CategoryTheory.Elementwise

/-!
# The categorical product of abelian groups is the Pi type

`AddCommGrpCat` has products — `Mathlib.Algebra.Category.Grp.Limits` gives it all limits — but
nothing identifies `∏ᶜ Z` with `∀ i, Z i`. Mathlib carries that identification under the name
`piIsoPi` for `ModuleCat` (`Algebra/Category/ModuleCat/Products.lean`), `TopCat`, and `Grpd`, and
for `AddCommGrpCat` only in the *finite* biproduct case (`biproductIsoPi`, over a `Fintype`
index). The infinite-index product form is absent, checked against the pinned revision.

It is needed here because a Čech complex is indexed by `Fin (p + 1) → ι` with `ι` the variable
type of a polynomial ring, so the index is infinite whenever the ambient projective space is —
`biproductIsoPi` does not apply, and the Čech term of an abelian-group-valued sheaf cannot be
compared with an explicit Pi type without it.

The construction is `ModuleCat.piIsoPi`'s, transported: the concrete cone on `∀ i, Z i` with the
evaluation homomorphisms as projections, shown limiting by the universal property of `Pi`, then
`limit.isoLimitCone`.

## Main declarations

* `AddCommGrpCat.productCone` — the concrete cone on the Pi type;
* `AddCommGrpCat.productConeIsLimit` — it is limiting;
* `AddCommGrpCat.piIsoPi` — the resulting isomorphism `∏ᶜ Z ≅ of (∀ i, Z i)`;
* `AddCommGrpCat.piIsoPi_inv_π` — the projection compatibility, which is what callers use;
* `AddCommGrpCat.piAddEquivPi` — the same comparison as an `AddEquiv`, for callers that leave
  the category.

## Implementation notes

This is owned library code, not a placeholder held open against an upstream fix; no Mathlib PR
is planned. If Mathlib does later declare these names, redeclaring them here is a hard error
rather than a shadowing warning, so this file is deleted at that point. That can only surface
during a deliberate `lakefile.toml` pin bump, since the Mathlib revision is an exact pin, and
the fix is deleting the file — hence the bare `AddCommGrpCat` namespace is kept rather than
hedged behind a repository prefix, per `ARCHITECTURE.md`.

The trap for a caller is the codomain of `piIsoPi`. It is the *bundled* object
`AddCommGrpCat.of (∀ i, Z i)`, not the type `∀ i, Z i`, so `piIsoPi` does not compose with an
equivalence of Pi types. `piAddEquivPi` is the form that does.

The `elementwise` variants `piIsoPi_inv_π_apply` and `piIsoPi_hom_eval_apply` are the applied
forms a caller indexing into the function type wants. Following Mathlib they are not `simp`
lemmas — neither side of the applied equation is more normal than the other — so use them by
name.

## Tags

abelian group, categorical product, limit, concrete category
-/

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AddCommGrpCat

variable {ι : Type v} (Z : ι → AddCommGrpCat.{max v w})

/-- The product cone induced by the concrete product. -/
def productCone : Fan Z :=
  Fan.mk (AddCommGrpCat.of (∀ i : ι, Z i)) fun i =>
    ofHom (Pi.evalAddMonoidHom (fun i : ι => Z i) i)

/-- The concrete product cone is limiting. -/
def productConeIsLimit : IsLimit (productCone Z) where
  lift s := ofHom (AddMonoidHom.pi fun j => (s.π.app ⟨j⟩).hom)
  uniq s m w := by
    ext x
    funext i
    exact DFunLike.congr_fun (congr_arg Hom.hom (w ⟨i⟩)) x

variable [HasProduct Z]

/-- The categorical product of a family of abelian groups is the Pi type.

The `ModuleCat` analogue is `ModuleCat.piIsoPi`; this is the same statement one forgetful functor
further down, and is what lets a Čech term over an infinite index set be named concretely. The
codomain is the bundled object, so to compose with an equivalence of function types reach for
`piAddEquivPi` instead. -/
noncomputable def piIsoPi : ∏ᶜ Z ≅ AddCommGrpCat.of (∀ i : ι, Z i) :=
  limit.isoLimitCone ⟨_, productConeIsLimit Z⟩

/-- The isomorphism is compatible with the projections, in the direction callers need: reading a
component off the Pi type agrees with the categorical projection. -/
@[simp, elementwise]
theorem piIsoPi_inv_π (i : ι) :
    (piIsoPi Z).inv ≫ Pi.π Z i = ofHom (Pi.evalAddMonoidHom (fun i : ι => Z i) i) :=
  limit.isoLimitCone_inv_π _ _

/-- Evaluating at an index after transporting the categorical product into the dependent function
type is the categorical projection. -/
@[simp, elementwise]
theorem piIsoPi_hom_eval (i : ι) :
    (piIsoPi Z).hom ≫ ofHom (Pi.evalAddMonoidHom (fun i : ι => Z i) i) = Pi.π Z i :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ (limit.isLimit _) (Discrete.mk i)

/-- The categorical product of a family of abelian groups as an `AddEquiv` onto the Pi type.

This is `piIsoPi` with the bundled codomain forgotten. It is the form that composes with
equivalences of function types — `AddEquiv.piCongrRight` and friends — which is what comparing a
product-valued complex against a pointwise-defined one needs, and is the shape in which the Čech
term meets `polynomialVariableCechCochains`. Its forward and inverse actions are
`piIsoPi_hom_eval_apply` and `piIsoPi_inv_π_apply`, which apply to it definitionally. -/
noncomputable def piAddEquivPi : (∏ᶜ Z : AddCommGrpCat) ≃+ (∀ i : ι, Z i) :=
  (piIsoPi Z).addCommGroupIsoToAddEquiv

end AddCommGrpCat
