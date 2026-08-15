/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Convolution
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Foundation.TriangulatedGrothendieckFunctorial

/-!
# Kernel functors on the triangulated Grothendieck group

A Fourier--Mukai transform whose three constituents are triangulated is itself
triangulated, so it induces a homomorphism on `Triangulated.K₀`.  This file
names that homomorphism and proves the two facts that make it useful:

* a functor naturally isomorphic to a transform induces the *same* map, so the
  class map of a kernel functor is computed by any of its kernels
  (`K₀_map_eq_transformK₀`); and
* the convolved kernel's class map is the composite of the two factors'
  (`transformK₀_conv`) -- the K-theoretic shadow of Huybrechts' Prop. 5.10.

The second is the first place the abstract interface says something a caller
could not have written down by unfolding definitions: it turns a supplied
isomorphism of *functors* into an equality of *homomorphisms*, via
`K₀.map_congr`.

## Why this is a separate file

`Triangulated.K₀` lives under `StabilityCondition.Foundation`, so importing it
points a module at the stability track.  `FourierMukai.Basic` and
`FourierMukai.Convolution` deliberately stay clear of that and depend on
Mathlib alone; the dependency is confined here, where it is the subject rather
than a convenience.

## What this file does not assert

* No Euler pairing, Mukai vector, or numerical invariant appears.  Relating a
  transform's action on `K₀` to a Mukai-lattice isometry needs the Chern
  character and Riemann--Roch, which live under `AlgebraicGeometry.Numerical`
  and are not imported here.
* Nothing is claimed about injectivity, surjectivity, or invertibility of
  `transformK₀`, and no transform is shown to be an equivalence.
* `transformK₀` depends on the chosen kernel, and no result here says two
  kernels inducing the same class map are isomorphic.
-/

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

noncomputable section

universe v₁ v₂ v₃ w₁ w₂ w₃ u₁ u₂ u₃ t₁ t₂ t₃

namespace Correspondence

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒲 : Type t₁}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{w₁} 𝒲]
  [HasZeroObject 𝒳] [HasShift 𝒳 ℤ] [Preadditive 𝒳]
  [∀ n : ℤ, (shiftFunctor 𝒳 n).Additive] [Pretriangulated 𝒳]
  [HasZeroObject 𝒴] [HasShift 𝒴 ℤ] [Preadditive 𝒴]
  [∀ n : ℤ, (shiftFunctor 𝒴 n).Additive] [Pretriangulated 𝒴]
  [HasZeroObject 𝒲] [HasShift 𝒲 ℤ] [Preadditive 𝒲]
  [∀ n : ℤ, (shiftFunctor 𝒲 n).Additive] [Pretriangulated 𝒲]

/-- The homomorphism on triangulated Grothendieck groups induced by the
transform with kernel `K`.  Named after `Families.derivedPullK₀`, and carrying
the same kind of explicit exactness hypotheses. -/
def transformK₀ (C : Correspondence 𝒳 𝒴 𝒲) (K : 𝒲)
    [C.pull.CommShift ℤ] [(C.tensor.obj K).CommShift ℤ] [C.push.CommShift ℤ]
    [C.pull.IsTriangulated] [(C.tensor.obj K).IsTriangulated]
    [C.push.IsTriangulated] : K₀ 𝒳 →+ K₀ 𝒴 :=
  K₀.map (C.transform K)

/-- `transformK₀` is `K₀.map` of the transform, by definition.  Stated so that
later rewrites do not have to unfold a `def`. -/
theorem transformK₀_eq (C : Correspondence 𝒳 𝒴 𝒲) (K : 𝒲)
    [C.pull.CommShift ℤ] [(C.tensor.obj K).CommShift ℤ] [C.push.CommShift ℤ]
    [C.pull.IsTriangulated] [(C.tensor.obj K).IsTriangulated]
    [C.push.IsTriangulated] :
    C.transformK₀ K = K₀.map (C.transform K) :=
  rfl

@[simp]
theorem transformK₀_of (C : Correspondence 𝒳 𝒴 𝒲) (K : 𝒲)
    [C.pull.CommShift ℤ] [(C.tensor.obj K).CommShift ℤ] [C.push.CommShift ℤ]
    [C.pull.IsTriangulated] [(C.tensor.obj K).IsTriangulated]
    [C.push.IsTriangulated] (E : 𝒳) :
    C.transformK₀ K (K₀.of 𝒳 E) = K₀.of 𝒴 ((C.transform K).obj E) := by
  simp [transformK₀]

/-- A functor naturally isomorphic to a transform induces the same map on
`K₀`.  This is what makes the class map an invariant of the kernel functor
rather than of a presentation of it. -/
theorem K₀_map_eq_transformK₀ (C : Correspondence 𝒳 𝒴 𝒲) (K : 𝒲)
    [C.pull.CommShift ℤ] [(C.tensor.obj K).CommShift ℤ] [C.push.CommShift ℤ]
    [C.pull.IsTriangulated] [(C.tensor.obj K).IsTriangulated]
    [C.push.IsTriangulated] (Φ : 𝒳 ⥤ 𝒴) [Φ.CommShift ℤ] [Φ.IsTriangulated]
    (e : Φ ≅ C.transform K) :
    K₀.map Φ = C.transformK₀ K :=
  K₀.map_congr e

/-- The class map of a kernel functor is computed by the kernel chosen from
its `IsKernelFunctor` witness. -/
theorem K₀_map_eq_transformK₀_kernel {C : Correspondence 𝒳 𝒴 𝒲} {Φ : 𝒳 ⥤ 𝒴}
    [Φ.CommShift ℤ] [Φ.IsTriangulated] (h : C.IsKernelFunctor Φ)
    [C.pull.CommShift ℤ] [(C.tensor.obj h.kernel).CommShift ℤ]
    [C.push.CommShift ℤ] [C.pull.IsTriangulated]
    [(C.tensor.obj h.kernel).IsTriangulated] [C.push.IsTriangulated] :
    K₀.map Φ = C.transformK₀ h.kernel :=
  K₀.map_congr h.iso

end Correspondence

namespace ConvolutionData

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒵 : Type u₃}
  {𝒲₁ : Type t₁} {𝒲₂ : Type t₂} {𝒲₃ : Type t₃}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒵]
  [Category.{w₁} 𝒲₁] [Category.{w₂} 𝒲₂] [Category.{w₃} 𝒲₃]
  [HasZeroObject 𝒳] [HasShift 𝒳 ℤ] [Preadditive 𝒳]
  [∀ n : ℤ, (shiftFunctor 𝒳 n).Additive] [Pretriangulated 𝒳]
  [HasZeroObject 𝒴] [HasShift 𝒴 ℤ] [Preadditive 𝒴]
  [∀ n : ℤ, (shiftFunctor 𝒴 n).Additive] [Pretriangulated 𝒴]
  [HasZeroObject 𝒵] [HasShift 𝒵 ℤ] [Preadditive 𝒵]
  [∀ n : ℤ, (shiftFunctor 𝒵 n).Additive] [Pretriangulated 𝒵]
  [HasZeroObject 𝒲₁] [HasShift 𝒲₁ ℤ] [Preadditive 𝒲₁]
  [∀ n : ℤ, (shiftFunctor 𝒲₁ n).Additive] [Pretriangulated 𝒲₁]
  [HasZeroObject 𝒲₂] [HasShift 𝒲₂ ℤ] [Preadditive 𝒲₂]
  [∀ n : ℤ, (shiftFunctor 𝒲₂ n).Additive] [Pretriangulated 𝒲₂]
  [HasZeroObject 𝒲₃] [HasShift 𝒲₃ ℤ] [Preadditive 𝒲₃]
  [∀ n : ℤ, (shiftFunctor 𝒲₃ n).Additive] [Pretriangulated 𝒲₃]

/-- The K-theoretic shadow of Huybrechts' Prop. 5.10: convolving kernels
composes their class maps.

The supplied datum is an isomorphism of functors; what comes out is an
equality of homomorphisms, because `K₀.map_congr` collapses the isomorphism.
Nothing here needs to know how `conv` is defined. -/
theorem transformK₀_conv {C₁ : Correspondence 𝒳 𝒴 𝒲₁}
    {C₂ : Correspondence 𝒴 𝒵 𝒲₂} {C₃ : Correspondence 𝒳 𝒵 𝒲₃}
    (D : ConvolutionData C₁ C₂ C₃) (P : 𝒲₁) (Q : 𝒲₂)
    [C₁.pull.CommShift ℤ] [(C₁.tensor.obj P).CommShift ℤ] [C₁.push.CommShift ℤ]
    [C₁.pull.IsTriangulated] [(C₁.tensor.obj P).IsTriangulated]
    [C₁.push.IsTriangulated]
    [C₂.pull.CommShift ℤ] [(C₂.tensor.obj Q).CommShift ℤ] [C₂.push.CommShift ℤ]
    [C₂.pull.IsTriangulated] [(C₂.tensor.obj Q).IsTriangulated]
    [C₂.push.IsTriangulated]
    [C₃.pull.CommShift ℤ] [(C₃.tensor.obj (D.conv P Q)).CommShift ℤ]
    [C₃.push.CommShift ℤ] [C₃.pull.IsTriangulated]
    [(C₃.tensor.obj (D.conv P Q)).IsTriangulated] [C₃.push.IsTriangulated] :
    C₃.transformK₀ (D.conv P Q) =
      (C₂.transformK₀ Q).comp (C₁.transformK₀ P) := by
  rw [Correspondence.transformK₀_eq, Correspondence.transformK₀_eq,
    Correspondence.transformK₀_eq, ← K₀.map_congr (D.compIso P Q),
    K₀.map_comp]

end ConvolutionData

end

end CategoryTheory.Triangulated.FourierMukai
