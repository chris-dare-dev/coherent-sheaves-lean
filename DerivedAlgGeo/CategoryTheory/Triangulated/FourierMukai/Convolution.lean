/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.FourierMukai.Basic

/-!
# Convolution of Fourier--Mukai kernels

Geometrically, for `P ∈ D(X × Y)` and `Q ∈ D(Y × Z)` the composite
`Φ_Q ∘ Φ_P` is again a Fourier--Mukai transform, with kernel the convolution

`Q ∗ P = Rπ_{XZ*}(π_{XY}^* P ⊗^L π_{YZ}^* Q) ∈ D(X × Z)`

which is the classical composition law.  Proving it from the three-projection
description
needs the projection formula and flat base change on a triple product, none of
which the abstract `Correspondence` of `FourierMukai.Basic` carries.

So convolution enters here as *supplied data*, not as a theorem.  A
`ConvolutionData` names a kernel-level operation together with the family of
isomorphisms that Prop. 5.10 asserts, for three correspondences that share
their outer categories in the pattern `𝒳 → 𝒴 → 𝒵`.  What this file then proves
are the consequences: that kernel functors are closed under composition, and
that convolution is well behaved under isomorphism of either kernel.

This is the same division of labour as
`StabilityCondition.Families.Basic`, where the geometric tests are supplied by
a caller and the file proves what follows from them.  The value is that a
later geometric realization has one named obligation to discharge rather than
an implicit one, and that everything downstream of Prop. 5.10 is already
available once it is.

## What this file does not assert

* Nothing constructs a `ConvolutionData`, and no example is exhibited.  That
  is not an omission for want of trying: `compIso` is required to hold
  *uniformly in* `Q`, so the cheap degenerate constructions — fold the middle
  transform into `C₃.push`, or take `conv P Q = P` — all fail, because they
  produce a `C₃` whose transform has one fixed `Q` baked into it and so cannot
  meet the requirement for any other. The uniformity is what gives the
  structure content, and discharging it is a geometric obligation.
* `conv` is a bare function `𝒲₁ → 𝒲₂ → 𝒲₃`, not a functor.  It is not assumed
  to be additive, exact, or even to send isomorphic kernels to isomorphic
  kernels — only to send them to kernels with *isomorphic transforms*, which
  is what `transformMapConvIso` proves and is strictly weaker.
* Associativity of convolution **splits**.  At the transform level it is a
  theorem, `convolutionTransformAssoc`, derived from the four `compIso`
  families alone — no new input.  At the kernel level it is
  `ConvolutionAssocData`, a second layer of *supplied* data: recovering the
  kernel-level isomorphism from the transform-level one would need a kernel
  to be determined by its transform (Orlov uniqueness), which is not
  available here.  No result here depends on the kernel-level layer, and
  nothing constructs it.
* Triangulatedness does not transport across `compIso`.  Moving
  `IsTriangulated` along a natural isomorphism needs that isomorphism to
  commute with the shift (`NatTrans.CommShift`), which is an extra hypothesis
  on the supplied data rather than a consequence of it.
* No kernel is claimed to be determined by its transform, so `conv` is not
  claimed to be the unique operation satisfying `compIso`.
-/

namespace CategoryTheory.Triangulated.FourierMukai

open CategoryTheory

universe v₁ v₂ v₃ w₁ w₂ w₃ u₁ u₂ u₃ t₁ t₂ t₃

variable {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒵 : Type u₃}
  {𝒲₁ : Type t₁} {𝒲₂ : Type t₂} {𝒲₃ : Type t₃}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒵]
  [Category.{w₁} 𝒲₁] [Category.{w₂} 𝒲₂] [Category.{w₃} 𝒲₃]

/-- Convolution data for three correspondences arranged as `𝒳 → 𝒴 → 𝒵`.

`conv` is the kernel-level operation and `compIso` is the classical
composition law for it: composing the transform with kernel `P` and the
transform with kernel
`Q` gives the transform with kernel `conv P Q`.  Both are supplied; neither is
derived. -/
structure ConvolutionData (C₁ : Correspondence 𝒳 𝒴 𝒲₁)
    (C₂ : Correspondence 𝒴 𝒵 𝒲₂) (C₃ : Correspondence 𝒳 𝒵 𝒲₃) where
  /-- The convolution of two kernels. -/
  conv : 𝒲₁ → 𝒲₂ → 𝒲₃
  /-- Prop. 5.10: the composite of the two transforms is the transform of the
  convolved kernel. -/
  compIso (P : 𝒲₁) (Q : 𝒲₂) :
    C₁.transform P ⋙ C₂.transform Q ≅ C₃.transform (conv P Q)

namespace ConvolutionData

variable {C₁ : Correspondence 𝒳 𝒴 𝒲₁} {C₂ : Correspondence 𝒴 𝒵 𝒲₂}
  {C₃ : Correspondence 𝒳 𝒵 𝒲₃}

/-- The composite of two transforms is a kernel functor for the third
correspondence, witnessed by the convolved kernel. -/
theorem isKernelFunctor_transform_comp (D : ConvolutionData C₁ C₂ C₃)
    (P : 𝒲₁) (Q : 𝒲₂) :
    C₃.IsKernelFunctor (C₁.transform P ⋙ C₂.transform Q) :=
  ⟨D.conv P Q, ⟨D.compIso P Q⟩⟩

/-- Kernel functors are closed under composition.  This is the reason to name
`ConvolutionData` at all: the property of *being* of Fourier--Mukai type,
rather than any particular transform, is what composes. -/
theorem isKernelFunctor_comp (D : ConvolutionData C₁ C₂ C₃)
    {Φ : 𝒳 ⥤ 𝒴} {Ψ : 𝒴 ⥤ 𝒵}
    (hΦ : C₁.IsKernelFunctor Φ) (hΨ : C₂.IsKernelFunctor Ψ) :
    C₃.IsKernelFunctor (Φ ⋙ Ψ) := by
  obtain ⟨P, ⟨eP⟩⟩ := hΦ
  obtain ⟨Q, ⟨eQ⟩⟩ := hΨ
  exact ⟨D.conv P Q,
    ⟨Functor.isoWhiskerRight eP Ψ ≪≫
      Functor.isoWhiskerLeft (C₁.transform P) eQ ≪≫ D.compIso P Q⟩⟩

/-- Isomorphic kernels convolve to kernels with isomorphic transforms.

This is weaker than `conv P Q ≅ conv P' Q'`, and deliberately so: recovering
that would need a kernel to be determined by its transform, which is Orlov's
uniqueness statement and is not available here. -/
def transformMapConvIso (D : ConvolutionData C₁ C₂ C₃) {P P' : 𝒲₁} (eP : P ≅ P')
    {Q Q' : 𝒲₂} (eQ : Q ≅ Q') :
    C₃.transform (D.conv P Q) ≅ C₃.transform (D.conv P' Q') :=
  (D.compIso P Q).symm ≪≫
    Functor.isoWhiskerRight (C₁.transformMapIso eP) (C₂.transform Q) ≪≫
      Functor.isoWhiskerLeft (C₁.transform P') (C₂.transformMapIso eQ) ≪≫
        D.compIso P' Q'

/-- Convolving with isomorphisms that are both the identity leaves the
transform alone. -/
@[simp]
theorem transformMapConvIso_refl (D : ConvolutionData C₁ C₂ C₃) (P : 𝒲₁)
    (Q : 𝒲₂) :
    D.transformMapConvIso (Iso.refl P) (Iso.refl Q) =
      Iso.refl (C₃.transform (D.conv P Q)) := by
  ext E
  simp [transformMapConvIso]

end ConvolutionData

section Assoc

universe v₄ u₄ w₁₂ w₂₃ w₀ t₁₂ t₂₃ t₀

variable {𝒱 : Type u₄} [Category.{v₄} 𝒱]
  {𝒲₁₂ : Type t₁₂} {𝒲₂₃ : Type t₂₃} {𝒲 : Type t₀}
  [Category.{w₁₂} 𝒲₁₂] [Category.{w₂₃} 𝒲₂₃] [Category.{w₀} 𝒲]
  {C₁ : Correspondence 𝒳 𝒴 𝒲₁} {C₂ : Correspondence 𝒴 𝒵 𝒲₂}
  {C₃ : Correspondence 𝒵 𝒱 𝒲₃}
  {C₁₂ : Correspondence 𝒳 𝒵 𝒲₁₂} {C₂₃ : Correspondence 𝒴 𝒱 𝒲₂₃}
  {C : Correspondence 𝒳 𝒱 𝒲}

/-- **Associativity of convolution at the transform level — a theorem, not
data.**

For three composable correspondences with convolution data for both
bracketings landing in a common outer correspondence, the transforms of the
two associated kernels are isomorphic: each side is isomorphic to
`Φ_P ⋙ Φ_Q ⋙ Φ_R` by Prop. 5.10 twice.  No input beyond the four `compIso`
families is consumed.

What this does **not** give is an isomorphism of the kernels themselves; that
is `ConvolutionAssocData`, and the gap between the two is genuine — see its
docstring. -/
def convolutionTransformAssoc
    (D₁₂ : ConvolutionData C₁ C₂ C₁₂) (D₂₃ : ConvolutionData C₂ C₃ C₂₃)
    (Dl : ConvolutionData C₁₂ C₃ C) (Dr : ConvolutionData C₁ C₂₃ C)
    (P : 𝒲₁) (Q : 𝒲₂) (R : 𝒲₃) :
    C.transform (Dl.conv (D₁₂.conv P Q) R) ≅
      C.transform (Dr.conv P (D₂₃.conv Q R)) :=
  (Dl.compIso (D₁₂.conv P Q) R).symm ≪≫
    Functor.isoWhiskerRight (D₁₂.compIso P Q).symm (C₃.transform R) ≪≫
      Functor.associator (C₁.transform P) (C₂.transform Q) (C₃.transform R) ≪≫
        Functor.isoWhiskerLeft (C₁.transform P) (D₂₃.compIso Q R) ≪≫
          Dr.compIso P (D₂₃.conv Q R)

/-- **Associativity of convolution at the kernel level — supplied data.**

An isomorphism `(P ∗ Q) ∗ R ≅ P ∗ (Q ∗ R)` between the two bracketings, in
the kernel category of the common outer correspondence.

Strictly stronger than `convolutionTransformAssoc`, and the gap is Orlov's
uniqueness statement: the transforms of the two kernels are always isomorphic
(the theorem above), but recovering an isomorphism of the *kernels* from an
isomorphism of their transforms needs a kernel to be determined by its
transform, which nothing in this repository provides.

Geometrically the classical proof works on the quadruple product, by the same
projection-formula and base-change arguments that derive Prop. 5.10 on the
triple product.  That derivation is the geometric ledger's future work, and
this structure is the layer it would discharge.  Nothing here constructs one,
and no result in this file depends on it. -/
structure ConvolutionAssocData
    (D₁₂ : ConvolutionData C₁ C₂ C₁₂) (D₂₃ : ConvolutionData C₂ C₃ C₂₃)
    (Dl : ConvolutionData C₁₂ C₃ C) (Dr : ConvolutionData C₁ C₂₃ C) where
  /-- The two bracketings of three kernels agree at the kernel level. -/
  assocIso (P : 𝒲₁) (Q : 𝒲₂) (R : 𝒲₃) :
    Dl.conv (D₁₂.conv P Q) R ≅ Dr.conv P (D₂₃.conv Q R)

end Assoc

end CategoryTheory.Triangulated.FourierMukai
