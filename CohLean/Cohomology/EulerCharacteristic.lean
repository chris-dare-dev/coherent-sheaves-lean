/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.AlgebraicGeometry.Modules.ModulesEquiv
import CohLean.AlgebraicGeometry.Variety
import CohLean.Coh.Abelian
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Geometric Euler characteristics of coherent sheaves

This file defines the geometric Euler characteristic

`χ(X, F) = ∑ᵢ (-1)ⁱ dimₖ Hⁱ(X, F)`

for coherent sheaves on a variety, relative to the two inputs that are not currently supplied
by Mathlib:

* the natural `k`-vector-space structure on coherent sheaf cohomology, functorial in `F`;
* finite-dimensionality and eventual vanishing.

The first input is packaged as a lift of the existing abelian-group-valued cohomology functors
to `ModuleCat k`. A natural isomorphism after forgetting scalars certifies that these are the
actual derived-functor groups `Sheaf.H`, not unrelated vector spaces of the desired dimensions.
The finiteness and vanishing fields are hypotheses, never axioms. Serre finiteness can later
construct them without changing the definition of `χ`.

The alternating sum reuses `GradedObject.eulerChar` from Mathlib. The support theorem below
removes its possible infinite-support junk value, and `eulerCharacteristic_eq_sum` exposes the
usual finite formula. Functoriality gives invariance under isomorphism of coherent sheaves.

Additivity in short exact sequences is deliberately the next layer: it requires the linear
long exact cohomology sequence, not merely the additive `Ext` sequence currently exposed by
`Sheaf.H`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace Cohomology

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

/-- Explicit data making coherent cohomology finite-dimensional over the base field.

`moduleH` is a functorial `k`-linear lift in every degree. `comparison` identifies its
underlying additive groups with Mathlib's derived-functor sheaf cohomology. The remaining
fields state Serre finiteness and eventual vanishing in exactly the form needed by the Euler
sum. -/
structure FiniteCohomology (X : Variety k) where
  /-- The base-field vector spaces `Hⁱ(X, F)`, functorial in the coherent sheaf `F`. -/
  moduleH : ℕ → Coh X.toScheme ⥤ ModuleCat.{u + 1} k
  /-- Forgetting the vector-space structure recovers derived-functor sheaf cohomology. -/
  comparison : ∀ i,
    moduleH i ⋙ forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1} ≅
      coherentH X.toScheme i
  /-- Every coherent cohomology vector space is finite-dimensional. -/
  finite : ∀ (i : ℕ) (F : Coh X.toScheme), Module.Finite k ((moduleH i).obj F)
  /-- A sheaf-dependent bound above which its cohomology vanishes. -/
  bound : Coh X.toScheme → ℕ
  /-- Cohomology vanishes strictly above `bound F`. -/
  vanishesAbove : ∀ (F : Coh X.toScheme) (i : ℕ), bound F < i →
    Subsingleton ((moduleH i).obj F)

namespace FiniteCohomology

variable {X : Variety k}

/-- The coherent cohomology groups of `F`, regarded as a graded family of `k`-modules. -/
abbrev gradedModule (D : FiniteCohomology X) (F : Coh X.toScheme) :
    GradedObject ℕ (ModuleCat.{u + 1} k) :=
  fun i ↦ (D.moduleH i).obj F

/-- The dimension of degree-`i` coherent cohomology. -/
noncomputable abbrev dimension (D : FiniteCohomology X) (F : Coh X.toScheme) (i : ℕ) : ℕ :=
  Module.finrank k ((D.moduleH i).obj F)

/-- The sign supplied by the cochain-complex shape is the usual `(-1)ⁱ`. -/
theorem upNat_sign (i : ℕ) : ((ComplexShape.up ℕ).χ i : ℤ) = (-1 : ℤ) ^ i := by
  change ((↑((-1 : ℤˣ) ^ i) : ℤ)) = (-1 : ℤ) ^ i
  exact Units.val_pow_eq_pow_val (-1 : ℤˣ) i

/-- The geometric Euler characteristic of a coherent sheaf. -/
noncomputable def eulerCharacteristic (D : FiniteCohomology X) (F : Coh X.toScheme) : ℤ :=
  GradedObject.eulerChar (ComplexShape.up ℕ) (D.gradedModule F)

/-- The finite-rank support of coherent cohomology lies below the supplied vanishing bound. -/
theorem finrankSupport_subset_range (D : FiniteCohomology X) (F : Coh X.toScheme) :
    GradedObject.finrankSupport (D.gradedModule F) ⊆
      (Finset.range (D.bound F + 1) : Set ℕ) := by
  intro i hi
  change D.dimension F i ≠ 0 at hi
  have hi_le : i ≤ D.bound F := by
    by_contra h
    haveI : Subsingleton ((D.moduleH i).obj F) :=
      D.vanishesAbove F i (Nat.lt_of_not_ge h)
    exact hi Module.finrank_zero_of_subsingleton
  simpa using Nat.lt_succ_of_le hi_le

/-- The Euler characteristic is the ordinary finite alternating sum through any supplied
vanishing bound. In particular, the `finsum` used by Mathlib has no junk value here. -/
theorem eulerCharacteristic_eq_sum (D : FiniteCohomology X) (F : Coh X.toScheme) :
    D.eulerCharacteristic F =
      ∑ i ∈ Finset.range (D.bound F + 1), (-1 : ℤ) ^ i * D.dimension F i := by
  simpa only [eulerCharacteristic, dimension, gradedModule, upNat_sign] using
    GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset
      (ComplexShape.up ℕ) (D.gradedModule F) (Finset.range (D.bound F + 1))
        (D.finrankSupport_subset_range F)

/-- Isomorphic coherent sheaves have equal cohomology dimensions in every degree. -/
theorem dimension_iso (D : FiniteCohomology X) {F G : Coh X.toScheme} (e : F ≅ G) (i : ℕ) :
    D.dimension F i = D.dimension G i :=
  ((D.moduleH i).mapIso e).toLinearEquiv.finrank_eq

/-- The geometric Euler characteristic is invariant under isomorphism of coherent sheaves. -/
theorem eulerCharacteristic_iso (D : FiniteCohomology X) {F G : Coh X.toScheme} (e : F ≅ G) :
    D.eulerCharacteristic F = D.eulerCharacteristic G := by
  apply finsum_congr
  intro i
  change ((ComplexShape.up ℕ).χ i : ℤ) * (D.dimension F i : ℤ) =
    ((ComplexShape.up ℕ).χ i : ℤ) * (D.dimension G i : ℤ)
  rw [D.dimension_iso e i]

end FiniteCohomology

end Cohomology

end AlgebraicGeometry
