/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.MukaiVector
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.GrothendieckGroup

/-!
# Realizing a triangulated Grothendieck group numerically

`CategoryTheory.Triangulated.K₀` is the Grothendieck group of a triangulated
category; `AlgebraicGeometry.Numerical`'s `N` is the numerical Grothendieck
group of a variety, supplied axiomatically by `NumericalVariety`.  Nothing in
this repository connected them, so no statement about a Fourier--Mukai
transform could reach the Mukai lattice.  This file supplies the connection as
data and proves what follows from it.

The chain it completes is

```
K₀ 𝒳  --K₀.map Φ-->  K₀ 𝒴
  | cl                  | cl'
  v                     v
  N   ----- φ ------>   N'
  | mukaiVector         | mukaiVector
  v                     v
 ℤ×Λ×ℤ  ---------->  ℤ×Λ'×ℤ
```

and the theorem is that the Mukai *pairing* of two Mukai vectors is unchanged
when `φ` preserves the Euler form: `pairing_mukaiVector_eq_of_preservesEuler`.
Specialised to `Φ = C.transform K` it says the pairing is unchanged on Mukai
vectors of **realized** classes, `pairing_mukaiVector_eq_on_realized`.

**This is not an isometry of Mukai lattices, and is deliberately not named as
one.** No map `MukaiLattice Λ → MukaiLattice Λ'` is constructed anywhere; the
statements are equalities of pairings between vectors that happen to be indexed
by the same classes. `mukaiVector` is a bare function, not an additive map, so
there is nothing to be well-defined on Mukai-vector fibres, and no injectivity
or surjectivity is assumed or proved. Building the actual lattice map is
further work and would need `c₁` additive at minimum.

## The realization is a hypothesis, and a large one

`NumericalRealization` follows the convention the stability-families track uses
for geometric input: the datum is named, so that the obligation is auditable,
and nothing here discharges it.  For an actual smooth projective `X` the
realization would be `K₀(D^b(Coh X)) → N(X)`.  Every ingredient of that is
missing at the pin:

* `D^b(Coh X)` does not exist here.  `Families.SchemeDerivedCategory` is the
  derived category of **all** sheaves of modules and says in its own docstring
  that no bounded coherent or perfect subcategory is identified;
* the Chern character of an object of a derived category does not exist --
  `NumericalVariety.chComp` is a field of the axiomatic interface, defined on
  the abstract `N`, not computed from a complex;
* the quotient of `K₀` by the radical of the Euler form is built in
  `GrothendieckGroup.Lattice` for the numerical side only.

So this file does not shorten the distance to a geometric theorem.  What it
does is make the distance explicit and let the categorical side be stated.

## What this file does not assert

* Nothing constructs a `NumericalRealization`, and nothing constructs a
  `Descends` witness.  Both are supplied.
* **Nothing proves a Fourier--Mukai transform preserves the Euler pairing.**
  That it does when the transform is an equivalence is a real theorem, and the
  hypothesis that carries it is full faithfulness together with `k`-linearity
  and shift-compatibility -- not adjunction, and not Serre duality, which is
  unnecessary once full faithfulness is known.  See `EulerTransfer`'s docstring.
  `PreservesEuler` is a hypothesis here, not a conclusion, and no transform is
  shown to satisfy it.
* No Hodge structure appears anywhere in this repository, so the classical
  statement that a Fourier--Mukai equivalence induces a **Hodge** isometry is
  not what is proved.  What is proved concerns the lattice form alone.
* No claim that a realization is injective, surjective, or unique, and none
  that two functors with the same descent are isomorphic.
* No map of Mukai lattices is constructed, and none of the pairing results is
  an isometry statement. `c₁` and `mukaiVector` are bare functions; additivity
  would be needed before a lattice map could even be written down.
-/

universe v₁ v₂ v₃ w₁ w₂ u₁ u₂ u₃ x₁ x₂ y₁ y₂

namespace AlgebraicGeometry.Numerical

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

section Realization

variable (𝒯 : Type u₁) [Category.{v₁} 𝒯] [HasZeroObject 𝒯] [HasShift 𝒯 ℤ]
  [Preadditive 𝒯] [∀ n : ℤ, (shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯]
  (N : Type x₁) [AddCommGroup N]

/-- A **numerical realization** of a triangulated category: a homomorphism from
its Grothendieck group to a numerical Grothendieck group.

Geometrically this is the class map `K₀(D^b(Coh X)) → N(X)`.  It is supplied,
never constructed -- see the module docstring for why every ingredient of the
geometric construction is missing at the pin. -/
structure NumericalRealization where
  /-- The class map. -/
  cl : K₀ 𝒯 →+ N

end Realization

section Descent

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {N : Type x₁} {N' : Type x₂}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴]
  [HasZeroObject 𝒳] [HasShift 𝒳 ℤ] [Preadditive 𝒳]
  [∀ n : ℤ, (shiftFunctor 𝒳 n).Additive] [Pretriangulated 𝒳]
  [HasZeroObject 𝒴] [HasShift 𝒴 ℤ] [Preadditive 𝒴]
  [∀ n : ℤ, (shiftFunctor 𝒴 n).Additive] [Pretriangulated 𝒴]
  [AddCommGroup N] [AddCommGroup N']

/-- `Φ` **descends** to `φ` along the two realizations: the square
`cl' ∘ K₀.map Φ = φ ∘ cl` commutes. -/
def Descends (R : NumericalRealization 𝒳 N) (R' : NumericalRealization 𝒴 N')
    (Φ : 𝒳 ⥤ 𝒴) [Φ.CommShift ℤ] [Φ.IsTriangulated] (φ : N →+ N') : Prop :=
  ∀ x : K₀ 𝒳, R'.cl (K₀.map Φ x) = φ (R.cl x)

/-- A descent is determined on classes of objects. -/
theorem Descends.apply_of {R : NumericalRealization 𝒳 N}
    {R' : NumericalRealization 𝒴 N'} {Φ : 𝒳 ⥤ 𝒴} [Φ.CommShift ℤ]
    [Φ.IsTriangulated] {φ : N →+ N'} (h : Descends R R' Φ φ) (E : 𝒳) :
    R'.cl (K₀.of 𝒴 (Φ.obj E)) = φ (R.cl (K₀.of 𝒳 E)) := by
  have := h (K₀.of 𝒳 E)
  rwa [K₀.map_of] at this

/-- Naturally isomorphic functors have the same descents. -/
theorem Descends.of_natIso {R : NumericalRealization 𝒳 N}
    {R' : NumericalRealization 𝒴 N'} {Φ Ψ : 𝒳 ⥤ 𝒴} [Φ.CommShift ℤ]
    [Φ.IsTriangulated] [Ψ.CommShift ℤ] [Ψ.IsTriangulated] {φ : N →+ N'}
    (h : Descends R R' Φ φ) (e : Φ ≅ Ψ) : Descends R R' Ψ φ := by
  intro x
  rw [← K₀.map_congr e]
  exact h x

end Descent

section Euler

open NumericalRing NumericalRingWithDual NumericalVariety

variable {n : ℕ} {A : Type y₁} {A' : Type y₂} {N : Type x₁} {N' : Type x₂}
  [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety n A N]
  [NumericalRingWithDual n A]
  [CommRing A'] [Algebra ℚ A'] [AddCommGroup N'] [NumericalVariety n A' N']
  [NumericalRingWithDual n A']

/-- `φ` **preserves the Euler form**: `χ(φE, φF) = χ(E, F)`.

For a fully faithful `k`-linear shift-compatible functor this is a theorem;
adjunction alone does not give it, and Serre duality is not needed for it.
Here it is a hypothesis; nothing in this repository discharges it for any
functor. -/
def PreservesEuler (φ : N →+ N') : Prop :=
  ∀ E F : N, chi₂ (A := A') (φ E) (φ F) = chi₂ (A := A) E F

end Euler

section Isometry

open NumericalRing NumericalRingWithDual NumericalVariety K3

variable {A : Type y₁} {A' : Type y₂} {N : Type x₁} {N' : Type x₂}
  {Λ : Type w₁} {Λ' : Type w₂}
  [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety 2 A N]
  [CommRing A'] [Algebra ℚ A'] [AddCommGroup N'] [NumericalVariety 2 A' N']
  [AddCommGroup Λ] [AddCommGroup Λ'] [IsK3 A N] [IsK3 A' N']

/-- **An Euler-preserving map leaves the Mukai pairing unchanged.**

Not an isometry statement: this equates two pairings, and constructs no map of
lattices. It is the arithmetic heart of the bridge, and where the sign
convention pays off: both sides equal `−χ` of their arguments by
`IntegralMukaiData.chi₂_eq_neg_pairing`, so preserving `χ` is exactly
preserving the Mukai pairing.  The `ℤ`-valued conclusion comes from the
`ℚ`-valued one by injectivity of the cast. -/
theorem pairing_mukaiVector_eq_of_preservesEuler (D : IntegralMukaiData A N Λ)
    (D' : IntegralMukaiData A' N' Λ') (φ : N →+ N')
    (hφ : PreservesEuler (A := A) (A' := A') φ) (E F : N) :
    Mukai.pairing D'.b (D'.mukaiVector (φ E)) (D'.mukaiVector (φ F))
      = Mukai.pairing D.b (D.mukaiVector E) (D.mukaiVector F) := by
  have hq : (Mukai.pairing D'.b (D'.mukaiVector (φ E)) (D'.mukaiVector (φ F)) : ℚ)
      = (Mukai.pairing D.b (D.mukaiVector E) (D.mukaiVector F) : ℚ) := by
    have h1 := D'.chi₂_eq_neg_pairing (φ E) (φ F)
    have h2 := D.chi₂_eq_neg_pairing E F
    have h3 := hφ E F
    linarith
  exact_mod_cast hq

/-- Self-pairings are preserved, hence so is sphericity of a Mukai vector. -/
theorem selfPairing_mukaiVector_eq_of_preservesEuler (D : IntegralMukaiData A N Λ)
    (D' : IntegralMukaiData A' N' Λ') (φ : N →+ N')
    (hφ : PreservesEuler (A := A) (A' := A') φ) (E : N) :
    Mukai.selfPairing D'.b (D'.mukaiVector (φ E))
      = Mukai.selfPairing D.b (D.mukaiVector E) := by
  rw [Mukai.selfPairing_eq_pairing, Mukai.selfPairing_eq_pairing]
  exact pairing_mukaiVector_eq_of_preservesEuler D D' φ hφ E E

/-- An Euler-preserving map carries spherical Mukai vectors to spherical ones,
in both directions. -/
theorem isSpherical_mukaiVector_iff_of_preservesEuler (D : IntegralMukaiData A N Λ)
    (D' : IntegralMukaiData A' N' Λ') (φ : N →+ N')
    (hφ : PreservesEuler (A := A) (A' := A') φ) (E : N) :
    Mukai.IsSpherical D'.b (D'.mukaiVector (φ E))
      ↔ Mukai.IsSpherical D.b (D.mukaiVector E) := by
  rw [Mukai.isSpherical_iff, Mukai.isSpherical_iff,
    selfPairing_mukaiVector_eq_of_preservesEuler D D' φ hφ]

end Isometry

section KernelFunctor

open NumericalRing NumericalRingWithDual NumericalVariety K3
open CategoryTheory.Triangulated.FourierMukai

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒲 : Type u₃}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒲]
  [HasZeroObject 𝒳] [HasShift 𝒳 ℤ] [Preadditive 𝒳]
  [∀ n : ℤ, (shiftFunctor 𝒳 n).Additive] [Pretriangulated 𝒳]
  [HasZeroObject 𝒴] [HasShift 𝒴 ℤ] [Preadditive 𝒴]
  [∀ n : ℤ, (shiftFunctor 𝒴 n).Additive] [Pretriangulated 𝒴]
  [HasZeroObject 𝒲] [HasShift 𝒲 ℤ] [Preadditive 𝒲]
  [∀ n : ℤ, (shiftFunctor 𝒲 n).Additive] [Pretriangulated 𝒲]
  {A : Type y₁} {A' : Type y₂} {N : Type x₁} {N' : Type x₂}
  {Λ : Type w₁} {Λ' : Type w₂}
  [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety 2 A N]
  [CommRing A'] [Algebra ℚ A'] [AddCommGroup N'] [NumericalVariety 2 A' N']
  [AddCommGroup Λ] [AddCommGroup Λ'] [IsK3 A N] [IsK3 A' N']

/-- **A kernel functor leaves the Mukai pairing unchanged on realized classes**,
given a descent of its class map that preserves the Euler form.

Read the quantifiers carefully. The conclusion is an equality of pairings for
the Mukai vectors of `R.cl x` and `R.cl y`, for classes `x y : K₀ 𝒳`. It is
NOT an isometry of Mukai lattices: no map between the two lattices is built, the
statement says nothing at vectors outside the image of `mukaiVector ∘ R.cl`, and
`mukaiVector` is not additive.

Every geometric input is named: the two realizations, the descent, and
Euler-preservation. None is constructed anywhere, and the classical theorem --
that a Fourier--Mukai *equivalence* supplies all of them and a Hodge isometry
besides -- is not proved here. -/
theorem pairing_mukaiVector_eq_on_realized (C : Correspondence 𝒳 𝒴 𝒲) (K : 𝒲)
    [C.pull.CommShift ℤ] [(C.tensor.obj K).CommShift ℤ] [C.push.CommShift ℤ]
    [C.pull.IsTriangulated] [(C.tensor.obj K).IsTriangulated]
    [C.push.IsTriangulated]
    (R : NumericalRealization 𝒳 N) (R' : NumericalRealization 𝒴 N')
    (φ : N →+ N') (hd : Descends R R' (C.transform K) φ)
    (D : IntegralMukaiData A N Λ) (D' : IntegralMukaiData A' N' Λ')
    (hφ : PreservesEuler (A := A) (A' := A') φ) (x y : K₀ 𝒳) :
    Mukai.pairing D'.b (D'.mukaiVector (R'.cl (C.transformK₀ K x)))
        (D'.mukaiVector (R'.cl (C.transformK₀ K y)))
      = Mukai.pairing D.b (D.mukaiVector (R.cl x)) (D.mukaiVector (R.cl y)) := by
  have hx : R'.cl (C.transformK₀ K x) = φ (R.cl x) := by
    rw [Correspondence.transformK₀_eq]; exact hd x
  have hy : R'.cl (C.transformK₀ K y) = φ (R.cl y) := by
    rw [Correspondence.transformK₀_eq]; exact hd y
  rw [hx, hy]
  exact pairing_mukaiVector_eq_of_preservesEuler D D' φ hφ _ _

end KernelFunctor

end AlgebraicGeometry.Numerical
