/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The `k`-linear Yoneda functor is homological

Mathlib proves that `preadditiveYoneda.obj B : Cᵒᵖ ⥤ AddCommGrpCat` is
homological. This file proves the same for `(linearYoneda k C).obj B`, which
lands in `ModuleCat k` instead.

The distinction is not cosmetic. A categorical Euler form
`χ(E,F) = Σᵢ (-1)ⁱ dim_k Hom(E, F[i])` needs `Module.finrank k` of each `Hom`,
and `finrank k` is not statable in `AddCommGrpCat` — the objects carry no
`k`-action to take dimensions over (`finrank ℤ` is statable, but `ℤ`-rank is
not the dimension count `χ` needs). `preadditiveYoneda` therefore cannot feed
that construction and `linearYoneda` can.

## Why the proof is short

The argument never mentions the target category. `Triangle.yoneda_exact₂` is a
statement about morphisms in `C`, and `ShortComplex.moduleCat_exact_iff` has the
*same shape* as the `ShortComplex.ab_exact_iff` Mathlib's proof uses:

`S.Exact ↔ ∀ x₂, S.g x₂ = 0 → ∃ x₁, S.f x₁ = x₂`.

So Mathlib's proof transplants with one lemma name changed. An earlier draft
reflected exactness along `forget₂ (ModuleCat k) Ab` instead; that works, but it
is strictly more plumbing for the same result.

## What this file does not provide

**`ShiftSequence ℤ` is not here**, and without it this instance does not yet
feed a Hom-built Euler form: the alternating sum needs the shifted Hom-groups
`Hom(E, F⟦i⟧)` assembled into a sequence, which is exactly what `ShiftSequence`
does. Three Mathlib-level gaps block it, none of them deep:

* `Linear R Cᵒᵖ` **does not exist** in Mathlib. `Preadditive Cᵒᵖ` does, by
  transporting `AddCommGroup` along `opEquiv`, but there is no `k`-linear
  counterpart — and morphisms in `Cᵒᵖ` are `Opposite`-wrapped
  (`(X ⟶ Y)` is `(unop Y ⟶ unop X)ᵒᵖ`), so nothing is definitionally available.
* `ShiftedHom.opEquiv_symm_smul` and `opEquiv'_symm_smul` do not exist. The
  additive versions do, and `ShiftedHom` already has a `Linear` section with
  `comp_smul`/`smul_comp`, so the groundwork is half present.
* The instance itself would then mirror Mathlib's `preadditiveYoneda` version
  with `LinearEquiv.toModuleIso` in place of `AddEquiv.toAddCommGrpIso`.

All three are general-purpose and belong upstream rather than here; they are
tracked as an `upstream-candidate` issue. Until they land,
`AlgebraicGeometry.Numerical.CategoricalEulerForm` stays supplied rather than
constructed, as its own docstring says.
-/

namespace CategoryTheory.Triangulated

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite Pretriangulated.Opposite

variable {k : Type*} [Ring k] {C : Type*} [Category C] [Preadditive C]
  [Linear k C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The `k`-linear Yoneda functor is homological.**

The `ModuleCat k` counterpart of Mathlib's instance for `preadditiveYoneda`, and
the one a `k`-dimension count can use. The proof is Mathlib's, with
`ShortComplex.ab_exact_iff` replaced by `ShortComplex.moduleCat_exact_iff`; the
`k`-action plays no part, because `Triangle.yoneda_exact₂` is about morphisms in
`C`. -/
instance linearYoneda_isHomological (B : C) :
    ((linearYoneda k C).obj B).IsHomological where
  exact T hT := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro (x₂ : T.obj₂.unop ⟶ B) (hx₂ : T.mor₂.unop ≫ x₂ = 0)
    obtain ⟨x₃, hx₃⟩ := Triangle.yoneda_exact₂ _ (unop_distinguished T hT) x₂ hx₂
    exact ⟨x₃, hx₃.symm⟩

/-- The short complex of a distinguished triangle stays exact after applying the
`k`-linear Yoneda functor. The `ModuleCat k` counterpart of
`preadditiveYoneda_map_distinguished`. -/
lemma linearYoneda_map_distinguished (T : Triangle C) (hT : T ∈ distTriang C)
    (B : C) :
    ((shortComplexOfDistTriangle T hT).op.map ((linearYoneda k C).obj B)).Exact :=
  ((linearYoneda k C).obj B).map_distinguished_op_exact T hT

end CategoryTheory.Triangulated
