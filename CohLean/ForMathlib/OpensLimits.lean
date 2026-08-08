/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.Topology.Sets.Opens

/-!
# Finite limits in the category of opens

The opens of a topological space form a complete lattice, so as a category they have finite
limits — the product of `U` and `V` is `U ⊓ V`, the terminal object is the whole space.
Mathlib proves exactly this for any `SemilatticeInf` with an `OrderTop`, in
`CategoryTheory.Limits.CompleteLattice`. Neither instance fires on
`TopologicalSpace.Opens X`. This file supplies both, once.

## Why the general instances do not fire

`Opens X` reaches its order twice over: through the bespoke
`TopologicalSpace.Opens.instPartialOrder`, derived from `SetLike`, and through the one inside
`TopologicalSpace.Opens.instCompleteLattice`, which is a `CompleteLattice.copy` built to be
*definitionally* equal to it. Instance search unifies at reducible transparency, where the
copy does not unfold, so **`OrderTop (Opens X)` and `BoundedOrder (Opens X)` are not found** —
even though `CompleteLattice`, `Order.Frame`, `SemilatticeInf`, `Lattice` and `Top` all are.

Everything in `CategoryTheory.Limits.CompleteLattice` sits above `OrderTop`, so every limit
instance on the site `X.Opens` is unreachable by default.

Naming the projections explicitly typechecks at default transparency, which is what
`orderTop` and `semilatticeInf` below do. They are `private`: `OrderTop` extends `Top`, and
`Opens` already has a `Top`, so a *global* `OrderTop` instance would create a data-carrying
diamond that could silently break existing `simp` lemmas about `⊤`. The bridge belongs inside
the proofs, not in the instance graph.

What is exported — `HasBinaryProducts` and `HasFiniteLimits` — is `Prop`-valued, so no diamond
is created by supplying it, and a later Mathlib instance of the same shape would be a harmless
duplicate.

## Why this matters here

`SheafOfModules.Presentation.quasicoherentData` — and therefore
`SheafOfModules.IsFinitePresentation.of_presentation` — assumes `[HasBinaryProducts C]` for the
site `C`. For a scheme `X` the site is `X.Opens`, so without these a global presentation cannot
be turned into finite presentation on a scheme at all. Mathlib never instantiates
`quasicoherentData` at a scheme site, which is why the gap has not surfaced upstream.

This file replaces two independent workarounds for the same gap — a global `hasBinaryProducts`
that lived in `ForMathlib/OpensBinaryProducts.lean`, and four `local instance`s in
`CohLean/Coh/Local.lean` — so that the explanation exists in one place and a third is not
written next time.

Destined for `Mathlib/CategoryTheory/Limits/Lattice.lean` or `Mathlib/Topology/Sets/Opens.lean`.
The honest upstream fix is to make the general lattice instances reachable rather than to
special-case `Opens`; that is worth a Mathlib issue, and this file should be deleted when it
lands.
-/

universe u

open CategoryTheory Limits

namespace TopologicalSpace.Opens

variable (X : Type u) [TopologicalSpace X]

/-- The `OrderTop` on `Opens X`, named rather than searched for.

`private`, deliberately: see the module docstring on why this must not enter the instance
graph. -/
@[reducible] private def orderTop : OrderTop (Opens X) :=
  (@CompleteLattice.toBoundedOrder _ (inferInstance : CompleteLattice (Opens X))).toOrderTop

/-- The `SemilatticeInf` on `Opens X`, taken through the same `CompleteLattice` as `orderTop`
so that both present the *same* underlying order to the category structure. -/
@[reducible] private def semilatticeInf : SemilatticeInf (Opens X) :=
  (@CompleteLattice.toLattice _ (inferInstance : CompleteLattice (Opens X))).toSemilatticeInf

/-- The opens of a topological space have binary products, given by intersection. -/
instance hasBinaryProducts : HasBinaryProducts (Opens X) :=
  @CategoryTheory.Limits.CompleteLattice.instHasBinaryProductsOfOrderTop _
    (semilatticeInf X) (orderTop X)

/-- The opens of a topological space have all finite limits. -/
instance hasFiniteLimits : HasFiniteLimits (Opens X) :=
  @CategoryTheory.Limits.CompleteLattice.hasFiniteLimits_of_semilatticeInf_orderTop _
    (semilatticeInf X) (orderTop X)

end TopologicalSpace.Opens
