/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Realization
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm

/-!
# Transferring Euler-form preservation across a realization

`Realization.PreservesEuler` is the hypothesis that a map of numerical
Grothendieck groups preserves `χ`.  This file reduces it to two inputs on the
categorical side, so that it stops being an opaque assumption about `N`.

## Why it does not follow from adjunction

The classical argument preserves `χ` from **full faithfulness**, not
adjunction: `χ(E,F) = Σᵢ (-1)ⁱ dim Hom(E, F[i])`, and a fully faithful functor
commuting with the shift matches the summands one by one.  Adjunction alone
gives `Hom(ΦE, ΦF) ≅ Hom(E, ΦᴿΦF)`, which is `Hom(E,F)` only once `ΦᴿΦ ≅ 𝟭` —
that is, only once `Φ` is fully faithful.  Serre duality is *not* needed for
this step; once full faithfulness is known the summands already match.

Full faithfulness alone is also not quite enough, and the missing word is
`k`-linear.  The summands are equal as `k`-dimensions, so the functor must
induce `k`-linear isomorphisms on `Hom`; an additive fully faithful functor
need not.  The hypothesis the construction below would discharge is therefore
a fully faithful `k`-linear shift-compatible functor, together with the
Hom-finiteness and boundedness that make the sum finite.

Neither hypothesis reaches `chi₂` on its own, and the reason is structural.
`NumericalVariety.chi₂` is `∫ ch(E)ᵛ · ch(F) · td(X)`: a formula in Chern
characters, with no `Hom` anywhere in it.  `EulerPairing`'s own docstring is
explicit that `chi₂ E F = Σᵢ (-1)ⁱ dim Extⁱ(E,F)` is **the bilinear
Hirzebruch--Riemann--Roch**, that there is no `Ext` at this layer to state it
against, and that discharging it is Layer B's job.  So a categorical
hypothesis can only reach `chi₂` through an HRR comparison, and that
comparison has to be supplied.

This file supplies it as `IsRiemannRoch` and does the bookkeeping.

## The reduction

`preservesEuler_of_descends` takes

* `hΦ : PreservesCategoricalEuler` — what full faithfulness would give, stated
  for a supplied categorical Euler form rather than derived from `Hom`;
* `hRR`, `hRR'` — bilinear HRR for the two realizations;
* `hsurj` — surjectivity of the source realization, which is what lets a
  statement about classes of complexes become a statement about all of `N`;
* `hd` — the descent square from `Realization`;

and concludes `PreservesEuler φ`, hence (via
`pairing_mukaiVector_eq_on_realized`) that a kernel functor leaves the Mukai
pairing unchanged on realized classes.  Against `IntegralMukaiData` that is an
equality of pairings and not an isometry of lattices; against
`AdditiveMukaiData` the same conclusion is an isometry of the Mukai forms on
`N` and `N'` (`Realization.isometryOfPreservesEuler`), and still not a map of
Mukai extensions.  See `Realization`'s docstring for why the distinctions
matter here.

## What this file does not assert

* **A `CategoricalEulerForm` can now be constructed** — `ofLinear`, from
  `Triangulated/GrothendieckGroup/EulerForm.lean`'s `chiK₀`.  What that costs is
  `HomFiniteBounded`: finite-dimensionality of every `Hom(X, Y⟦i⟧)` and finite
  support in `i`.  So the obligation is *moved*, from "produce a biadditive
  pairing" to "produce Hom-finiteness", not eliminated.  A caller with an
  abstract `𝒯` and no `k` still supplies the structure directly.
* **`PreservesCategoricalEuler` is now proved** for a fully faithful `k`-linear
  shift-compatible functor between Hom-finite categories, against forms built by
  `ofLinear` (`ofLinear_preservesCategoricalEuler`).  It stays a hypothesis for
  *supplied* forms, where there is no `Hom` for the argument to run on.
* `IsRiemannRoch` is bilinear HRR, assumed.  No variety is shown to satisfy
  it, and `NumericalVariety.hirzebruch_riemannRoch` — the one-variable
  statement — is itself an axiom of the Layer A interface.
-/

universe v₁ v₂ v₃ w₁ w₂ u₁ u₂ u₃ x₁ x₂ y₁ y₂

namespace AlgebraicGeometry.Numerical

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated
open NumericalRing NumericalRingWithDual NumericalVariety

section Form

variable (𝒯 : Type u₁) [Category.{v₁} 𝒯] [HasZeroObject 𝒯] [HasShift 𝒯 ℤ]
  [Preadditive 𝒯] [∀ n : ℤ, (shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯]

/-- A **categorical Euler form**: a biadditive `ℤ`-valued pairing on `K₀ 𝒯`.

Geometrically this is `χ(E,F) = Σᵢ (-1)ⁱ dim Hom(E, F[i])`.

The structure remains an interface — it asks only for the pairing, and carries
no `k` — but it is no longer *only* supplied: `ofLinear` below constructs one
from `Hom` for a `k`-linear category with finite-dimensional, finitely-supported
shifted Hom-spaces. A caller in that situation should use `ofLinear` rather than
inventing a `chi`. -/
structure CategoricalEulerForm where
  /-- The pairing. -/
  chi : K₀ 𝒯 →+ K₀ 𝒯 →+ ℤ

end Form

section OfLinear

open CategoryTheory.Triangulated

/-- **The Hom-built Euler form, packaged as a `CategoricalEulerForm`.**

`Triangulated/GrothendieckGroup/EulerForm.lean` constructs
`χ(X,Y) = Σᵢ (-1)ⁱ dimₖ Hom(X, Y⟦i⟧)` and proves it biadditive; this is that
`chiK₀` in the shape the numerical track consumes.

The constructor lives here rather than at the construction site because
`CategoricalEulerForm` is stated over a merely-`Preadditive` `𝒯` with no `k` in
its binders — the `k`-linear hypotheses cannot be attached to the structure
without changing its signature and every consumer's.

**What this does and does not discharge.** `EulerTransfer`'s conclusion rests on
three supplied inputs; this retires the first of them for `k`-linear
Hom-finite categories. `IsRiemannRoch` and `PreservesCategoricalEuler` remain
supplied, and `HomFiniteBounded` is itself supplied — the obligation is moved
from "produce a biadditive pairing" to "produce Hom-finiteness", which is a
better place for it but is not nothing. -/
noncomputable def CategoricalEulerForm.ofLinear (k : Type w₁) [DivisionRing k]
    (𝒯 : Type u₁) [Category.{v₁} 𝒯] [HasZeroObject 𝒯] [HasShift 𝒯 ℤ]
    [Preadditive 𝒯] [∀ n : ℤ, (shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯]
    [Linear k 𝒯] [∀ n : ℤ, (shiftFunctor 𝒯 n).Linear k]
    [HomFiniteBounded k 𝒯] : CategoricalEulerForm 𝒯 :=
  ⟨chiK₀ k 𝒯⟩

@[simp]
theorem CategoricalEulerForm.ofLinear_chi (k : Type w₁) [DivisionRing k]
    (𝒯 : Type u₁) [Category.{v₁} 𝒯] [HasZeroObject 𝒯] [HasShift 𝒯 ℤ]
    [Preadditive 𝒯] [∀ n : ℤ, (shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯]
    [Linear k 𝒯] [∀ n : ℤ, (shiftFunctor 𝒯 n).Linear k]
    [HomFiniteBounded k 𝒯] :
    (CategoricalEulerForm.ofLinear k 𝒯).chi = chiK₀ k 𝒯 := rfl

end OfLinear

section Transfer

variable {n : ℕ} {𝒳 : Type u₁} {𝒴 : Type u₂}
  {A : Type y₁} {A' : Type y₂} {N : Type x₁} {N' : Type x₂}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴]
  [HasZeroObject 𝒳] [HasShift 𝒳 ℤ] [Preadditive 𝒳]
  [∀ m : ℤ, (shiftFunctor 𝒳 m).Additive] [Pretriangulated 𝒳]
  [HasZeroObject 𝒴] [HasShift 𝒴 ℤ] [Preadditive 𝒴]
  [∀ m : ℤ, (shiftFunctor 𝒴 m).Additive] [Pretriangulated 𝒴]
  [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety n A N]
  [NumericalRingWithDual n A]
  [CommRing A'] [Algebra ℚ A'] [AddCommGroup N'] [NumericalVariety n A' N']
  [NumericalRingWithDual n A']

/-- **Bilinear Hirzebruch--Riemann--Roch for a realization**: the categorical
Euler form computes the numerical one on realized classes.

This is the comparison the whole reduction turns on, and it is assumed.  The
one-variable statement `NumericalVariety.hirzebruch_riemannRoch` is already an
axiom of the Layer A interface; this is its bilinear companion. -/
def IsRiemannRoch (R : NumericalRealization 𝒳 N)
    (E : CategoricalEulerForm 𝒳) : Prop :=
  ∀ x y : K₀ 𝒳, ((E.chi x y : ℤ) : ℚ) = chi₂ (A := A) (R.cl x) (R.cl y)

/-- `Φ` **preserves the categorical Euler form**.

For a fully faithful `k`-linear shift-commuting functor this is the classical
fact, term by term in `Σᵢ (-1)ⁱ dim Hom(E, F[i])`; `k`-linearity is what makes
the matched summands equal as `k`-dimensions, and additivity alone would not.

It remains a *hypothesis* here, because the definition is stated for supplied
forms on categories carrying no `k`.  For forms that come from `Hom` via
`CategoricalEulerForm.ofLinear` it is now a **theorem** —
`ofLinear_preservesCategoricalEuler` below. -/
def PreservesCategoricalEuler (Φ : 𝒳 ⥤ 𝒴) [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (E : CategoricalEulerForm 𝒳) (E' : CategoricalEulerForm 𝒴) : Prop :=
  ∀ x y : K₀ 𝒳, E'.chi (K₀.map Φ x) (K₀.map Φ y) = E.chi x y

omit [NumericalRingWithDual n A] [NumericalRingWithDual n A'] in
/-- **Euler preservation transfers across a realization.**

Given bilinear HRR on both sides, a functor preserving the categorical Euler
form, and a descent, the descended map preserves the numerical Euler form.
Surjectivity of the source realization is what turns a statement about classes
of complexes into one about all of `N`. -/
theorem preservesEuler_of_descends {Φ : 𝒳 ⥤ 𝒴} [Φ.CommShift ℤ]
    [Φ.IsTriangulated] {R : NumericalRealization 𝒳 N}
    {R' : NumericalRealization 𝒴 N'} {E : CategoricalEulerForm 𝒳}
    {E' : CategoricalEulerForm 𝒴} {φ : N →+ N'}
    (hsurj : Function.Surjective R.cl)
    (hRR : IsRiemannRoch (A := A) R E) (hRR' : IsRiemannRoch (A := A') R' E')
    (hΦ : PreservesCategoricalEuler Φ E E') (hd : Descends R R' Φ φ) :
    PreservesEuler (A := A) (A' := A') φ := by
  intro F G
  obtain ⟨x, rfl⟩ := hsurj F
  obtain ⟨y, rfl⟩ := hsurj G
  rw [← hd x, ← hd y, ← hRR', hΦ, hRR]

end Transfer

section Preservation

/-- **A fully faithful `k`-linear functor preserves the Hom-built Euler form.**

The last of the three obligations this file named, discharged for forms that
come from `Hom`.  The content is entirely `Triangulated.chiK₀_map`; what happens
here is only that it is restated against `CategoricalEulerForm`.

This is where the `k`-linearity caveat in this file's docstring stops being a
caveat and becomes a hypothesis of a theorem: `Φ.Linear k` is what makes the
matched summands equal as `k`-dimensions, and an additive fully faithful functor
would not do.  Note `Φ.FullyFaithful` is data rather than a `Prop` class, so it
is passed explicitly. -/
theorem ofLinear_preservesCategoricalEuler (k : Type w₁) [DivisionRing k]
    (𝒳 : Type u₁) (𝒴 : Type u₂) [Category.{v₁} 𝒳] [Category.{v₂} 𝒴]
    [HasZeroObject 𝒳] [HasShift 𝒳 ℤ] [Preadditive 𝒳]
    [∀ m : ℤ, (shiftFunctor 𝒳 m).Additive] [Pretriangulated 𝒳]
    [HasZeroObject 𝒴] [HasShift 𝒴 ℤ] [Preadditive 𝒴]
    [∀ m : ℤ, (shiftFunctor 𝒴 m).Additive] [Pretriangulated 𝒴]
    [Linear k 𝒳] [Linear k 𝒴]
    [∀ m : ℤ, (shiftFunctor 𝒳 m).Linear k] [∀ m : ℤ, (shiftFunctor 𝒴 m).Linear k]
    [HomFiniteBounded k 𝒳] [HomFiniteBounded k 𝒴]
    (Φ : 𝒳 ⥤ 𝒴) [Φ.Additive] [Φ.Linear k] [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (hΦ : Φ.FullyFaithful) :
    PreservesCategoricalEuler Φ (CategoricalEulerForm.ofLinear k 𝒳)
      (CategoricalEulerForm.ofLinear k 𝒴) :=
  fun x y => chiK₀_map k 𝒳 𝒴 Φ hΦ x y

end Preservation

section KernelFunctor

open K3 CategoryTheory.Triangulated.FourierMukai

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒲 : Type u₃}
  {A : Type y₁} {A' : Type y₂} {N : Type x₁} {N' : Type x₂}
  {Λ : Type w₁} {Λ' : Type w₂}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒲]
  [HasZeroObject 𝒳] [HasShift 𝒳 ℤ] [Preadditive 𝒳]
  [∀ m : ℤ, (shiftFunctor 𝒳 m).Additive] [Pretriangulated 𝒳]
  [HasZeroObject 𝒴] [HasShift 𝒴 ℤ] [Preadditive 𝒴]
  [∀ m : ℤ, (shiftFunctor 𝒴 m).Additive] [Pretriangulated 𝒴]
  [HasZeroObject 𝒲] [HasShift 𝒲 ℤ] [Preadditive 𝒲]
  [∀ m : ℤ, (shiftFunctor 𝒲 m).Additive] [Pretriangulated 𝒲]
  [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety 2 A N]
  [NumericalRingWithDual 2 A]
  [CommRing A'] [Algebra ℚ A'] [AddCommGroup N'] [NumericalVariety 2 A' N']
  [NumericalRingWithDual 2 A']
  [AddCommGroup Λ] [AddCommGroup Λ'] [IsK3 A N] [IsK3 A' N']

omit [NumericalRingWithDual 2 A] [NumericalRingWithDual 2 A'] in
/-- **A kernel functor preserving the categorical Euler form leaves the Mukai
pairing unchanged on realized classes.**

An equality of pairings, stated against `IntegralMukaiData`, where there is no
bilinear form for it to be an isometry of. This is
`pairing_mukaiVector_eq_on_realized` with its `PreservesEuler` hypothesis
discharged from categorical input; with `AdditiveMukaiData` the same
`PreservesEuler` output feeds `isometryOfPreservesEuler`, and no map of Mukai
*extensions* is built there either.

Three obligations remain, and all three are named rather than hidden:
constructing the categorical Euler form from `Hom`, proving a fully faithful
`k`-linear functor preserves it, and bilinear HRR. -/
theorem pairing_mukaiVector_eq_on_realized_of_categorical
    (C : Correspondence 𝒳 𝒴 𝒲) (K : 𝒲)
    [C.pull.CommShift ℤ] [(C.tensor.obj K).CommShift ℤ] [C.push.CommShift ℤ]
    [C.pull.IsTriangulated] [(C.tensor.obj K).IsTriangulated]
    [C.push.IsTriangulated]
    (R : NumericalRealization 𝒳 N) (R' : NumericalRealization 𝒴 N')
    (E : CategoricalEulerForm 𝒳) (E' : CategoricalEulerForm 𝒴)
    (φ : N →+ N') (hsurj : Function.Surjective R.cl)
    (hRR : IsRiemannRoch (A := A) R E) (hRR' : IsRiemannRoch (A := A') R' E')
    (hΦ : PreservesCategoricalEuler (C.transform K) E E')
    (hd : Descends R R' (C.transform K) φ)
    (D : IntegralMukaiData A N Λ) (D' : IntegralMukaiData A' N' Λ')
    (x y : K₀ 𝒳) :
    Mukai.pairing D'.b (D'.mukaiVector (R'.cl (C.transformK₀ K x)))
        (D'.mukaiVector (R'.cl (C.transformK₀ K y)))
      = Mukai.pairing D.b (D.mukaiVector (R.cl x))
        (D.mukaiVector (R.cl y)) :=
  pairing_mukaiVector_eq_on_realized C K R R' φ hd D D'
    (preservesEuler_of_descends hsurj hRR hRR' hΦ hd) x y

end KernelFunctor

end AlgebraicGeometry.Numerical
