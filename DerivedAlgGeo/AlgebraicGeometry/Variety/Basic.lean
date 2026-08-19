/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Properties

/-!
# Varieties over a field

This module separates an over-scheme from the proposition that it is a variety. A
`SchemeOverField k` contains only a scheme and its chosen map to `Spec k`; a `Variety k` is the
subtype satisfying integrality and local finite type. Smoothness and properness remain morphism
properties rather than fields in an inheritance hierarchy.

The two notions intentionally remain separated:

* `Variety k` carries actual scheme geometry;
* `NumericalVarietyData n A N` carries the intersection-theoretic quotient used by numerical
  arguments;
* a future realization constructor will derive the latter from the former after geometric
  Chern classes, Euler-characteristic finiteness, and Riemann--Roch are available.

`SmoothProperVariety` is retained as a compatibility subtype. Its property is proof-irrelevant,
so it cannot make two varieties from one underlying over-scheme; new APIs should instead take a
`Variety` and request `Smooth X.structureMorphism` or `IsProper X.structureMorphism` directly.
-/

universe u

namespace AlgebraicGeometry

/-- A scheme with a chosen structure morphism to `Spec k`.

This is the common object below all geometric adjectives. The induced `Scheme.Over` instance
lets APIs written against Mathlib's over-scheme interface consume the same structure map. -/
structure SchemeOverField (k : Type u) [Field k] where
  /-- The underlying scheme. -/
  toScheme : Scheme.{u}
  /-- The chosen structure morphism to the base field. -/
  structureMorphism : toScheme ⟶ Spec (CommRingCat.of k)

namespace SchemeOverField

variable {k : Type u} [Field k]

instance (X : SchemeOverField k) : X.toScheme.Over (Spec (CommRingCat.of k)) where
  hom := X.structureMorphism

/-- The proposition that an over-scheme is a variety: its source is integral and its structure
morphism is locally of finite type. -/
class IsVariety (X : SchemeOverField k) : Prop where
  /-- The underlying scheme is integral. -/
  isIntegral : IsIntegral X.toScheme
  /-- The structure morphism is locally of finite type. -/
  locallyOfFiniteType : LocallyOfFiniteType X.structureMorphism

end SchemeOverField

/-- A variety over `k`: an over-scheme satisfying the proposition-valued variety conditions.

Using a subtype rather than structural inheritance keeps the underlying over-scheme singular;
proof irrelevance identifies any two witnesses for the same over-scheme. -/
abbrev Variety (k : Type u) [Field k] :=
  { X : SchemeOverField k // SchemeOverField.IsVariety X }

namespace Variety

variable {k : Type u} [Field k]

/-- The underlying scheme of a variety. -/
abbrev toScheme (X : Variety k) : Scheme.{u} := X.1.toScheme

/-- The structure morphism of a variety. -/
abbrev structureMorphism (X : Variety k) :
    X.toScheme ⟶ Spec (CommRingCat.of k) :=
  X.1.structureMorphism

instance (X : Variety k) : IsIntegral X.toScheme := X.2.isIntegral

instance (X : Variety k) : LocallyOfFiniteType X.structureMorphism :=
  X.2.locallyOfFiniteType

/-- A variety over a field is locally noetherian: the base field is noetherian and the
structure morphism is locally of finite type. -/
noncomputable instance (X : Variety k) : IsLocallyNoetherian X.toScheme :=
  LocallyOfFiniteType.isLocallyNoetherian X.structureMorphism

end Variety

/-- A smooth proper variety over `k`.

This compatibility subtype carries only proof-irrelevant evidence. It does not create a second
geometric object, and generic APIs should prefer separate smoothness and properness hypotheses. -/
abbrev SmoothProperVariety (k : Type u) [Field k] :=
  { X : Variety k // Smooth X.structureMorphism ∧ IsProper X.structureMorphism }

namespace SmoothProperVariety

variable {k : Type u} [Field k]

/-- Forget the compatibility smooth-proper view without changing the underlying variety. -/
abbrev toVariety (X : SmoothProperVariety k) : Variety k := X.1

instance (X : SmoothProperVariety k) : Smooth X.toVariety.structureMorphism := X.2.1

instance (X : SmoothProperVariety k) : IsProper X.toVariety.structureMorphism := X.2.2

end SmoothProperVariety

namespace Variety

variable {k : Type u} [Field k]

/-- A proper variety over a field is Noetherian: finite type gives local Noetherianity and
properness gives quasi-compactness over the compact point `Spec k`. -/
noncomputable instance (X : Variety k) [IsProper X.structureMorphism] :
    IsNoetherian X.toScheme where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace :=
    QuasiCompact.compactSpace_of_compactSpace X.structureMorphism

/-- A proper variety over a field is separated as an absolute scheme. -/
instance (X : Variety k) [IsProper X.structureMorphism] : X.toScheme.IsSeparated where
  isSeparated_terminal_from := by
    rw [← CategoryTheory.Limits.terminal.comp_from X.structureMorphism]
    infer_instance

end Variety

end AlgebraicGeometry
