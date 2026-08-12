/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Weak.Tilting.Cohomology.Homological
import BridgelandStabLean.TStructure.Exactness

/-!
# Exact sequences from heart cohomology

`originalHeartCohFunctor t 0` is homological (`originalHeartCohFunctor_isHomological`),
so a distinguished triangle in `C` maps to an exact short complex in the heart of `t`.
This file states that consequence in the form the 2026 target papers use it, and
records what is still missing for the full long exact sequence.

## Main results

* `originalHeartCoh_exact_of_distTriang`: the degree-zero short complex of a
  distinguished triangle is exact in the heart.
* `originalHeartCoh_isZero_of_isZero`: degree-zero cohomology kills zero objects.
* `heart_map_originalHeartCoh`: a t-exact functor carries `H⁰_t(X)` into the
  heart of the target t-structure, so degree-zero cohomology transports along it
  at the level of objects.

## What is NOT here, and what it would take

The **long** exact sequence — connecting maps `δ : H^n(Z) ⟶ H^{n+1}(X)` and
exactness at every degree — is not stated, because homologicality is currently
available only at `n = 0`. Two routes exist, and neither is a short step:

1. **Truncation–shift compatibility.** Prove
   `(t.truncLT a).obj (X⟦n⟧) ≅ ((t.truncLT (a + n)).obj X)⟦n⟧` and the `truncGE`
   analogue, then `originalHeartCohFunctor t n ≅ shiftFunctor C n ⋙ originalHeartCohFunctor t 0`
   and homologicality at every `n` follows from Mathlib's composition instance.
   Mathlib has no such lemma at either pin — searched `TruncLTGE.lean` and
   `TruncLEGT.lean`; the truncation functors have no shift API at all. The proof
   runs through `liftTruncLT` / `descTruncGE` plus uniqueness of the truncation
   triangle.

2. **The sign-twisted shift argument.** Mathlib's `Triangle.shift_distinguished`
   makes `T.shift n` distinguished only after a sign twist, which is why
   `shiftFunctor C n` is not registered as a triangulated functor. The twist
   lands on the connecting map and not on `T.obj₁ ⟶ T.obj₂ ⟶ T.obj₃`, so
   homologicality survives it — but the bookkeeping has to be done explicitly
   through `IsHomological.mk'`.

Route 1 is the more valuable of the two: the truncation–shift lemmas are
Mathlib-shaped, reusable well beyond this file, and are what a `ShiftSequence`
instance would need anyway. It deserves its own issue rather than being folded
in here.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace BridgelandStabLean.Tilting

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C] (t : TStructure C)

-- `ShortComplex.Exact` in the heart needs the heart's abelian structure at statement
-- time, and `heartFullSubcategoryAbelian` is a `def`, not an instance. Scope it locally
-- rather than making it global: a global `Abelian` instance on every t-structure heart
-- is exactly the kind of thing that creates diamonds later.
attribute [local instance]
  BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian

/-- A distinguished triangle maps to an exact short complex under degree-zero
heart cohomology.

This is the degree-zero row of the long exact sequence; see the module docstring
for why the other rows are not yet available. -/
theorem originalHeartCoh_exact_of_distTriang
    (T : Triangle C) (hT : T ∈ distTriang C) :
    ((shortComplexOfDistTriangle T hT).map (originalHeartCohFunctor t 0)).Exact :=
  Functor.map_distinguished_exact (originalHeartCohFunctor t 0) T hT

/-- Degree-zero heart cohomology sends zero objects to zero objects. -/
theorem originalHeartCoh_isZero_of_isZero {X : C} (hX : IsZero X) :
    IsZero ((originalHeartCohFunctor t 0).obj X) := by
  have : IsZero (((originalHeartCohFunctor t 0).obj X).obj) := by
    change IsZero ((shiftFunctor C 0).obj ((t.truncGELE 0 0).obj X))
    exact (t.truncGELE 0 0 ⋙ shiftFunctor C 0).map_isZero hX
  exact BridgelandStabLean.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategory.isZero_of_obj_isZero this

section TExact

variable {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {F : C ⥤ D} {t' : TStructure D}

/-- A t-exact functor carries heart objects to heart objects, so it is defined on
the targets of `originalHeartCohFunctor`.

This is the object-level statement. The natural transformation
`F ∘ H⁰_t ⟶ H⁰_{t'} ∘ F` needs the truncation–shift API described in the module
docstring and is deliberately not asserted here. -/
theorem heart_map_originalHeartCoh [Functor.IsTExact F t t'] (X : C) :
    t'.heart (F.obj ((originalHeartCohFunctor t 0).obj X).obj) :=
  Functor.heart_map_of_isTExact _ ((originalHeartCohFunctor t 0).obj X).property

end TExact

end BridgelandStabLean.Tilting
