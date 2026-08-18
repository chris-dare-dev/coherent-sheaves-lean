/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties

/-!
# Varieties over a field

This module bundles the geometric source object that the numerical layer is eventually meant
to receive data from. A `Variety k` is an integral scheme equipped with a finite-type morphism
to `Spec k`; it is not a synonym for `NumericalVarietyData`.

The two notions intentionally remain separated:

* `Variety k` carries actual scheme geometry;
* `NumericalVarietyData n A N` carries the intersection-theoretic quotient used by numerical
  arguments;
* a future realization constructor will derive the latter from the former after geometric
  Chern classes, Euler-characteristic finiteness, and Riemann--Roch are available.

Mathlib currently has proper and smooth morphisms but no general projective-morphism API. The
`SmoothProperVariety` bundle below therefore records the geometric hypotheses currently
expressible without pretending that properness is the definition of projectivity. A later
projective bundle should extend `Variety` with genuine projective data.
-/

universe u

namespace AlgebraicGeometry

/-- A variety over `k`: an integral scheme of finite type over `Spec k`.

The structure morphism is explicit because a general scheme does not carry a distinguished
base field. -/
structure Variety (k : Type u) [Field k] where
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  /-- The chosen structure morphism to the base field. -/
  structureMorphism : toScheme ⟶ Spec (CommRingCat.of k)
  /-- The underlying scheme is integral. -/
  isIntegral : IsIntegral toScheme
  /-- The structure morphism is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType structureMorphism

namespace Variety

variable {k : Type u} [Field k]

instance (X : Variety k) : IsIntegral X.toScheme := X.isIntegral

instance (X : Variety k) : LocallyOfFiniteType X.structureMorphism :=
  X.locallyOfFiniteType

/-- A variety over a field is locally noetherian: the base field is noetherian and the
structure morphism is locally of finite type. -/
noncomputable instance (X : Variety k) : IsLocallyNoetherian X.toScheme :=
  LocallyOfFiniteType.isLocallyNoetherian X.structureMorphism

end Variety

/-- A smooth proper variety over `k`.

This is a useful geometric input for coherent-cohomology work. It is deliberately named
`SmoothProperVariety`, not `SmoothProjectiveVariety`: projectivity requires additional data
that Mathlib does not yet expose as a general morphism property. -/
structure SmoothProperVariety (k : Type u) [Field k] extends Variety k where
  /-- The structure morphism is smooth. -/
  smooth : Smooth toVariety.structureMorphism
  /-- The structure morphism is proper. -/
  proper : IsProper toVariety.structureMorphism

namespace SmoothProperVariety

variable {k : Type u} [Field k]

instance (X : SmoothProperVariety k) : Smooth X.toVariety.structureMorphism := X.smooth

instance (X : SmoothProperVariety k) : IsProper X.toVariety.structureMorphism := X.proper

/-- A proper variety over a field is Noetherian: finite type gives local Noetherianity and
properness gives quasi-compactness over the compact point `Spec k`. -/
noncomputable instance (X : SmoothProperVariety k) : IsNoetherian X.toVariety.toScheme where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace :=
    QuasiCompact.compactSpace_of_compactSpace X.toVariety.structureMorphism

/-- A proper variety over a field is separated as an absolute scheme. -/
instance (X : SmoothProperVariety k) : X.toVariety.toScheme.IsSeparated where
  isSeparated_terminal_from := by
    rw [← CategoryTheory.Limits.terminal.comp_from X.toVariety.structureMorphism]
    infer_instance

end SmoothProperVariety

end AlgebraicGeometry
