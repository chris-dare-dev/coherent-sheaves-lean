/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Realization

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
pairing unchanged on realized classes.  That is an equality of pairings, not an
isometry of lattices -- see `Realization`'s docstring for why the distinction
matters here.

## What this file does not assert

* **Nothing constructs a `CategoricalEulerForm`.** Building `χ` from `Hom`
  needs an alternating sum `Σᵢ (-1)ⁱ dim Hom(X, Y[i])`, which needs
  Hom-finiteness, a bound making the sum finite, and additivity along
  distinguished triangles via the long exact Hom sequence.  None of that
  machinery exists in this repository; `Mathlib.CategoryTheory.Triangulated.Yoneda`
  has the exactness input, and the rest would be a track of its own.
* **Nothing proves `PreservesCategoricalEuler` for any functor.**  In
  particular neither full faithfulness nor `k`-linearity is anywhere used,
  because with the form supplied abstractly there is no `Hom` for either to act
  on.  That implication is exactly what the construction above would unlock.
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

Geometrically this is `χ(E,F) = Σᵢ (-1)ⁱ dim Hom(E, F[i])`.  It is supplied,
not built: see the module docstring for what constructing it would require. -/
structure CategoricalEulerForm where
  /-- The pairing. -/
  chi : K₀ 𝒯 →+ K₀ 𝒯 →+ ℤ

end Form

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
With the form supplied abstractly there is no `Hom` to run that argument on, so
here it is a hypothesis. -/
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

An equality of pairings, not an isometry: no map of Mukai lattices is built
here or anywhere downstream. This is `pairing_mukaiVector_eq_on_realized` with
its `PreservesEuler` hypothesis discharged from categorical input.

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
