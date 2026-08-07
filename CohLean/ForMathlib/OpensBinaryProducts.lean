/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.Topology.Sets.Opens

/-!
# Binary products in the category of opens

The opens of a topological space form a complete lattice, so as a category they have binary
products — the product of `U` and `V` is `U ⊓ V`. Mathlib proves exactly this for any
`SemilatticeInf` with an `OrderTop`
(`CategoryTheory.Limits.CompleteLattice.instHasBinaryProducts`), but the instance does not
fire on `TopologicalSpace.Opens X`. This file supplies it.

## Why the general instance does not fire

`Opens X` carries two routes to its order: the bespoke
`TopologicalSpace.Opens.instPartialOrder`, derived from `SetLike`, and the one inside
`TopologicalSpace.Opens.instCompleteLattice`, which is a `CompleteLattice.copy` built to be
*definitionally* equal to it. Instance search unifies at reducible transparency, where the
copy does not unfold, so `OrderTop (Opens X)` — and hence `BoundedOrder (Opens X)` and the
binary-product instance above it — is not found, even though `CompleteLattice (Opens X)`,
`SemilatticeInf (Opens X)` and `Top (Opens X)` all are.

The projection `CompleteLattice.toBoundedOrder.toOrderTop` typechecks at default
transparency. Naming it in a `letI` is enough to put the search back on the rails, and the
resulting `HasBinaryProducts` is a `Prop`, so no diamond is created by supplying it.

## Why this matters here

`SheafOfModules.Presentation.quasicoherentData` — and therefore
`SheafOfModules.IsFinitePresentation.of_presentation` — assumes `[HasBinaryProducts C]` for
the site `C`. For a scheme `X` the site is `X.Opens`, so without this instance a global
presentation cannot be turned into finite presentation of a sheaf on a scheme at all.
Mathlib never instantiates `quasicoherentData` at a scheme site, which is why the gap has
not surfaced upstream.

Destined for `Mathlib/CategoryTheory/Limits/Lattice.lean` or
`Mathlib/Topology/Sets/Opens.lean`; the honest upstream fix is probably to make the general
lattice instance reachable rather than to special-case `Opens`.
-/

universe u

open CategoryTheory Limits

namespace TopologicalSpace.Opens

variable (X : Type u) [TopologicalSpace X]

/-- The opens of a topological space have binary products, given by intersection.

This is `CategoryTheory.Limits.CompleteLattice.instHasBinaryProducts`; see the module
docstring for why that instance does not fire on `Opens X` by itself. -/
instance hasBinaryProducts : HasBinaryProducts (Opens X) := by
  letI : OrderTop (Opens X) := CompleteLattice.toBoundedOrder.toOrderTop
  haveI : ∀ {U V : Opens X}, HasLimit (pair U V) := fun {_ _} =>
    HasLimit.mk (CompleteLattice.finiteLimitCone _)
  exact hasBinaryProducts_of_hasLimit_pair _

end TopologicalSpace.Opens
