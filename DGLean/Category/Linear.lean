/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DGLean.Category.Basic

/-!
# `k`-linear dg categories

`DGCategory` is stated over abelian groups so that its Hom-complexes are
exactly the complexes `CochainComplex.HomComplex` produces. Linearity over a
commutative ring is layered on top, the way `CategoryTheory.Linear` layers over
`Preadditive` in Mathlib.

`ADR-0011` records why this is a refinement rather than part of the definition:
a first draft that baked `ModuleCat k` into `dgHom` collided with the
`AddCommGrpCat`-valued `HomComplex` three separate times.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u w

open CategoryTheory DGCategoryStruct

/-- A `k`-linear structure on a dg category: given `k`-module structures on the
graded pieces of the Hom-complexes, both the differential and the composition
are `k`-linear.

The module structures are a parameter rather than a field. A field cannot be
used as an instance inside the same class's later field types, and the version
that tried produced a stuck `HSMul` metavariable on the first axiom. -/
class DGLinear (k : Type w) [CommRing k] (C : Type u) [DGCategory.{v} C]
    [∀ (X Y : C) (p : ℤ), Module k ((dgHom X Y).X p)] where
  /-- The differential is `k`-linear. -/
  d_smul {X Y : C} (p q : ℤ) (c : k) (f : (dgHom X Y).X p) :
    ((dgHom X Y).d p q).hom (c • f) = c • ((dgHom X Y).d p q).hom f
  /-- Composition is `k`-linear in its first argument. -/
  comp_smul_left {X Y Z : C} (p q r : ℤ) (h : p + q = r) (c : k)
      (f : (dgHom X Y).X p) (g : (dgHom Y Z).X q) :
    dgComp p q r h (c • f) g = c • dgComp p q r h f g
  /-- Composition is `k`-linear in its second argument. -/
  comp_smul_right {X Y Z : C} (p q r : ℤ) (h : p + q = r) (c : k)
      (f : (dgHom X Y).X p) (g : (dgHom Y Z).X q) :
    dgComp p q r h f (c • g) = c • dgComp p q r h f g
