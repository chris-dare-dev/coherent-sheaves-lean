/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The `k`-linear coyoneda functor is homological, and its shift sequence

The companion of `Triangulated/LinearYoneda.lean` in the other variable.
`(linearCoyoneda k C).obj A : C ⥤ ModuleCat k` is `Hom(A, −)`, and this file
gives it `IsHomological` and `ShiftSequence ℤ`, so a distinguished triangle in
the *second* argument of `Hom` also produces a long exact sequence of
`k`-modules.

## Why both variables are needed, and why only this one is cheap

A Hom-built Euler form `χ(X, Y) = Σᵢ (-1)ⁱ dimₖ Hom(X, Y⟦i⟧)` has to be
additive in each argument separately before it descends to `K₀ C ⊗ K₀ C`.
`LinearYoneda.lean` gives the long exact sequence when the triangle is in the
*first* argument; nothing there says anything about the second. This file is
that missing half.

The two halves are **not** symmetric, and the asymmetry is worth stating because
it shows up as a hypothesis difference downstream:

* `linearYoneda` is contravariant, so its source is `Cᵒᵖ`. Its shift sequence
  has to move the shift across `op`, which is what drags in
  `Triangulated/LinearOpposite.lean` and, with it, the hypothesis
  `[∀ n, (shiftFunctor C n).Linear k]`.
* `linearCoyoneda` is covariant, with source `C`. Its shift sequence is
  `Functor.ShiftSequence.tautological` — literally `shiftFunctor C n ⋙ F` — so
  **no** opposite-category linearity and **no** shift-linearity hypothesis is
  required on this side at all.

Mathlib has the `preadditiveCoyoneda` counterparts of both instances
(`Triangulated/Yoneda.lean`); as with `linearYoneda`, they cannot serve a
`k`-dimension count because `AddCommGrpCat` carries no `k`. The proof here is
Mathlib's with `ShortComplex.ab_exact_iff` replaced by
`ShortComplex.moduleCat_exact_iff`, the same substitution `LinearYoneda.lean`
makes.

## What this file does not provide

No Euler form, and no finiteness. Having the long exact sequence in both
variables is not having `Σᵢ (-1)ⁱ dimₖ Hom(X, Y⟦i⟧)`: that needs each term
finite-dimensional and the sum finitely supported, both of which are supplied
data assembled elsewhere.
-/

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {k : Type*} [Ring k] {C : Type*} [Category C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The `k`-linear coyoneda functor is homological.**

The `ModuleCat k` counterpart of Mathlib's instance for `preadditiveCoyoneda`.
As on the Yoneda side the `k`-action plays no part in the proof, because
`Triangle.coyoneda_exact₂` is a statement about morphisms in `C`. -/
instance linearCoyoneda_isHomological (A : Cᵒᵖ) :
    ((linearCoyoneda k C).obj A).IsHomological where
  exact T hT := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro (x₂ : A.unop ⟶ T.obj₂) (hx₂ : x₂ ≫ T.mor₂ = 0)
    obtain ⟨x₁, hx₁⟩ := T.coyoneda_exact₂ hT x₂ hx₂
    exact ⟨x₁, hx₁.symm⟩

/-- **The shifted Hom-groups in the second variable, assembled.**

Tautological, and that is the point: `(linearCoyoneda k C).obj A` is covariant
with source `C`, so shifting the argument is just precomposition with
`shiftFunctor C n`. Contrast `LinearYoneda.lean`'s instance, which has to move a
shift across `op` and needs `(shiftFunctor C n).Linear k` to do it. -/
noncomputable instance linearCoyonedaShiftSequence (A : Cᵒᵖ) :
    ((linearCoyoneda k C).obj A).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ _

/-! ### The long exact sequence

Named specializations of Mathlib's homology-sequence API, matching
`LinearYoneda.lean`'s. Unlike those, these are stated for a triangle in `C`
directly — the coyoneda functor's source is `C`, so no op-triangle is
involved. -/

/-- Exactness in the middle. -/
lemma linearCoyoneda_homologySequence_exact₂ (A : Cᵒᵖ) (T : Triangle C)
    (hT : T ∈ distTriang C) (n₀ : ℤ) :
    (ShortComplex.mk _ _
      (((linearCoyoneda k C).obj A).homologySequence_comp T hT n₀)).Exact :=
  ((linearCoyoneda k C).obj A).homologySequence_exact₂ T hT n₀

/-- Exactness at the connecting map's source. -/
lemma linearCoyoneda_homologySequence_exact₃ (A : Cᵒᵖ) (T : Triangle C)
    (hT : T ∈ distTriang C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _
      (((linearCoyoneda k C).obj A).comp_homologySequenceδ T hT n₀ n₁ h)).Exact :=
  ((linearCoyoneda k C).obj A).homologySequence_exact₃ T hT n₀ n₁ h

/-- Exactness at the connecting map's target. -/
lemma linearCoyoneda_homologySequence_exact₁ (A : Cᵒᵖ) (T : Triangle C)
    (hT : T ∈ distTriang C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    (ShortComplex.mk _ _
      (((linearCoyoneda k C).obj A).homologySequenceδ_comp T hT n₀ n₁ h)).Exact :=
  ((linearCoyoneda k C).obj A).homologySequence_exact₁ T hT n₀ n₁ h

end CategoryTheory.Triangulated
