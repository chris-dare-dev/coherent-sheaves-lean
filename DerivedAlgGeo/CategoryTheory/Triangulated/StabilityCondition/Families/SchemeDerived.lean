/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.ResidueFiber

/-!
# Derived categories attached to scheme fibers

For every scheme `X`, its category `X.Modules` of sheaves of
`𝒪_X`-modules is abelian.  Mathlib therefore constructs its derived category
as the localization of cochain complexes at quasi-isomorphisms, together with
the canonical triangulated structure.  This file exposes that construction
for scheme base changes and their residue-field fibers.  It also exposes the
bounded derived category defined by the canonical t-structure.

These are derived categories of all sheaves of modules.  No bounded coherent
or perfect subcategory is identified here.  Moreover, the construction is
objectwise: no derived pullback functor, base-change coherence, geometric
slicing witness, relative HN structure, openness, boundedness, moduli result,
or conclusion of Theorem 22.2 of arXiv:1902.08184v4 is asserted.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u w

/-- The derived category of sheaves of modules on a scheme, constructed using
Mathlib's standard localization at quasi-isomorphisms. -/
abbrev SchemeDerivedCategory (X : Scheme.{u}) :=
  letI := HasDerivedCategory.standard X.Modules
  DerivedCategory X.Modules

/-- The bounded derived category of sheaves of modules on a scheme, defined
using the canonical t-structure on `SchemeDerivedCategory X`. -/
abbrev SchemeBoundedDerivedCategory (X : Scheme.{u}) :=
  letI := HasDerivedCategory.standard X.Modules
  DerivedCategory.Bounded X.Modules

namespace SchemeDerivedCategory

/-- The localization functor from cochain complexes of module sheaves to the
scheme's derived category. -/
abbrev Q (X : Scheme.{u}) :
    CochainComplex X.Modules ℤ ⥤ SchemeDerivedCategory X :=
  letI := HasDerivedCategory.standard X.Modules
  DerivedCategory.Q

/-- The canonical inclusion of the bounded derived category into the
unbounded derived category. -/
abbrev boundedInclusion (X : Scheme.{u}) :
    SchemeBoundedDerivedCategory X ⥤ SchemeDerivedCategory X :=
  letI := HasDerivedCategory.standard X.Modules
  DerivedCategory.Bounded.ι

end SchemeDerivedCategory

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- The concrete derived category attached to a scheme base change. -/
abbrev DerivedFiber (T : SchemeBaseChange S) :=
  SchemeDerivedCategory T.left

/-- The concrete bounded derived category attached to a scheme base change. -/
abbrev BoundedDerivedFiber (T : SchemeBaseChange S) :=
  SchemeBoundedDerivedCategory T.left

/-- The concrete derived category over the residue-field scheme at `x`. -/
abbrev ResidueDerivedFiber (T : SchemeBaseChange S) (x : T.left) :=
  (T.residue x).DerivedFiber

/-- The concrete bounded derived category over the residue-field scheme at
`x`. -/
abbrev ResidueBoundedDerivedFiber (T : SchemeBaseChange S) (x : T.left) :=
  (T.residue x).BoundedDerivedFiber

theorem residueDerivedFiber_eq (T : SchemeBaseChange S) (x : T.left) :
    T.ResidueDerivedFiber x =
      SchemeDerivedCategory (Spec (T.left.residueField x)) :=
  rfl

theorem residueBoundedDerivedFiber_eq (T : SchemeBaseChange S) (x : T.left) :
    T.ResidueBoundedDerivedFiber x =
      SchemeBoundedDerivedCategory (Spec (T.left.residueField x)) :=
  rfl

end SchemeBaseChange

namespace SchemeTriangulatedFiberFamily

variable {S : Scheme.{u}} (F : SchemeTriangulatedFiberFamily S)

/-- Objectwise identification of a supplied triangulated family with the
concrete derived categories of module sheaves.  This records no compatibility
between the equivalences and the supplied pullback functors. -/
structure DerivedRealization where
  /-- Equivalence between each supplied fiber and the concrete derived
  category on its underlying scheme. -/
  fiberEquivalence (T : SchemeBaseChange S) : F.Fiber T ≌ T.DerivedFiber

/-- Objectwise identification of a supplied triangulated family with the
concrete bounded derived categories of module sheaves.  Derived pullback and
its coherence remain additional data. -/
structure BoundedDerivedRealization where
  /-- Equivalence between each supplied fiber and the concrete bounded
  derived category on its underlying scheme. -/
  fiberEquivalence (T : SchemeBaseChange S) :
    F.Fiber T ≌ T.BoundedDerivedFiber

namespace DerivedRealization

variable {F}

/-- A derived realization specializes to the actual residue-field derived
category at every point. -/
def residueFiberEquivalence (R : F.DerivedRealization)
    (T : SchemeBaseChange S) (x : T.left) :
    F.ResidueFiber T x ≌ T.ResidueDerivedFiber x :=
  R.fiberEquivalence (T.residue x)

end DerivedRealization

namespace BoundedDerivedRealization

variable {F}

/-- A bounded derived realization specializes to the actual bounded derived
category of the residue-field scheme at every point. -/
def residueFiberEquivalence (R : F.BoundedDerivedRealization)
    (T : SchemeBaseChange S) (x : T.left) :
    F.ResidueFiber T x ≌ T.ResidueBoundedDerivedFiber x :=
  R.fiberEquivalence (T.residue x)

end BoundedDerivedRealization

end SchemeTriangulatedFiberFamily

end


end CategoryTheory.Triangulated.StabilityCondition.Families
