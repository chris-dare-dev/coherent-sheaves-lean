/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.AlgebraicGeometry.Modules.Affine.Equivalence
import CohLean.AlgebraicGeometry.Variety.Basic
import CohLean.Coh.Abelian.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finite-dimensional coherent cohomology data

This file defines the output interface for the projective finiteness theorem independently of
eventual cohomological vanishing. The separation matters mathematically and for the issue graph:

* finite-dimensionality of each `Hⁱ(X, F)` is the content of #29;
* a bound above which the groups vanish is the separate content of #30.

Mathlib currently exposes `Sheaf.H` only as an abelian group. Consequently the projective theorem
must first construct a functorial `k`-linear lift and a natural comparison after forgetting
scalars. `LinearCohomology` records that lift, while `FiniteDimensionalCohomology` adds exactly the
degreewise `Module.Finite` conclusion. These are structures carrying explicit proof data, not
global instances or existence axioms.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Cohomology

variable {k : Type u} [Field k]

/-- The existing abelian-group-valued degree-`i` cohomology functor on coherent sheaves.

The explicit `HasExt` instance is required by the current `Sheaf.H` API. -/
noncomputable def coherentH (X : Scheme.{u}) (i : ℕ) :
    Coh X ⥤ AddCommGrpCat.{u + 1} := by
  letI : HasExt.{u + 1}
      (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasExt.standard _
  exact Coh.ι X ⋙ Scheme.Modules.toSheaf X ⋙
    Sheaf.functorH (Opens.grothendieckTopology X) i

/-- A functorial base-field-linear realization of Mathlib's coherent sheaf cohomology.

The natural comparison rules out an unrelated family of vector spaces with the desired
dimensions: after forgetting scalars these are the actual `Sheaf.H` groups and maps. -/
structure LinearCohomology (X : Variety k) where
  /-- The base-field vector spaces `Hⁱ(X, F)`, functorial in the coherent sheaf `F`. -/
  moduleH : ℕ → Coh X.toScheme ⥤ ModuleCat.{u + 1} k
  /-- Forgetting the vector-space structure recovers derived-functor sheaf cohomology. -/
  comparison : ∀ i,
    moduleH i ⋙ forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1} ≅
      coherentH X.toScheme i

/-- Degreewise finite-dimensional coherent cohomology, with no eventual-vanishing claim.

This is the exact output interface for #29. A later boundedness result can extend it without
re-proving or repackaging the linear comparison. -/
structure FiniteDimensionalCohomology (X : Variety k) extends LinearCohomology X where
  /-- Every coherent cohomology vector space is finite-dimensional. -/
  finite : ∀ (i : ℕ) (F : Coh X.toScheme), Module.Finite k ((moduleH i).obj F)

namespace FiniteDimensionalCohomology

variable {X : Variety k}

/-- The dimension of degree-`i` coherent cohomology. -/
noncomputable abbrev dimension (D : FiniteDimensionalCohomology X)
    (F : Coh X.toScheme) (i : ℕ) : ℕ :=
  Module.finrank k ((D.moduleH i).obj F)

/-- Isomorphic coherent sheaves have equal cohomology dimensions in every degree. -/
theorem dimension_iso (D : FiniteDimensionalCohomology X)
    {F G : Coh X.toScheme} (e : F ≅ G) (i : ℕ) :
    D.dimension F i = D.dimension G i :=
  ((D.moduleH i).mapIso e).toLinearEquiv.finrank_eq

end FiniteDimensionalCohomology

end AlgebraicGeometry.Cohomology
