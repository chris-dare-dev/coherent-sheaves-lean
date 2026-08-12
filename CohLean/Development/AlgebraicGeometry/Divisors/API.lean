/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.RingTheory.PicardGroup

/-!
# Layer B stage 2 — divisor API audit

**This file proves nothing.** It is a compile-only map of the Mathlib v4.32 API on which B2
will build. Each declaration below is an `example` naming an upstream declaration, so the file
fails to build if that API moves. Delete it once the inventory is encoded in the B2 theorem
statements.

Mathlib v4.32.0 is the first stable release containing both
`AlgebraicGeometry.AlgebraicCycle.Basic` and
`AlgebraicGeometry.OrderOfVanishing`; CohLean uses the v4.32.1 patch release.

## What is upstream

* `AlgebraicGeometry.AlgebraicCycle` and `AlgebraicCycle.map` provide locally finite cycles and
  quasicompact pushforward.
* `Scheme.ordHom` and `Scheme.ord` provide order of vanishing for the function field of a
  locally noetherian integral scheme.
* `SheafOfModules.IsLocallyFree` provides locally free sheaves of arbitrary local rank.
* `Module.Invertible` and `CommRing.Pic` provide invertible modules and the Picard group of a
  commutative ring. They are not definitions of invertible sheaves or `Pic X` for a scheme.
* `PresheafOfModules.sheafification` provides generic associated-sheaf machinery.
* `Scheme.IdealSheafData.subscheme` constructs a subscheme from ideal-sheaf data.

## Genuine B2 gaps

Mathlib v4.32.1 has no scheme-level rank-one/invertible-sheaf predicate, no tensor product on
`SheafOfModules`, no scheme Picard group, no Cartier or effective Cartier divisors, and no
divisor-associated sheaf `O_X(D)`. The generic sheafification and ideal-sheaf subscheme APIs are
building blocks for those definitions, not substitutes for them.

No algebraic-cycle or order-of-vanishing implementation belongs in CohLean.
-/

open CategoryTheory

namespace AlgebraicGeometry.DivisorAPIAudit

noncomputable section

/-! ### Cycles and order of vanishing -/

example := @AlgebraicGeometry.AlgebraicCycle
example := @AlgebraicGeometry.AlgebraicCycle.map
example := @AlgebraicGeometry.Scheme.ordHom
example := @AlgebraicGeometry.Scheme.ord

/-! ### Locally free sheaves and the ring-level Picard API -/

example := @SheafOfModules.IsLocallyFree
example := @Module.Invertible
example := @CommRing.Pic

/-! ### Generic construction machinery used by the missing divisor-specific layer -/

example := @PresheafOfModules.sheafification
example := @AlgebraicGeometry.Scheme.IdealSheafData
example := @AlgebraicGeometry.Scheme.IdealSheafData.subscheme

end

end AlgebraicGeometry.DivisorAPIAudit
