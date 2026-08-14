/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import DGLean.Category.H0
import DGLean.Model.Complexes

/-!
# The seam: `H⁰(C^dg A)` and the homotopy category

`dg-enhancements-e4`'s theorem. The route is to identify this repository's
`cocycles` and `coboundaries` with Mathlib's, so that the Hom-groups of
`H⁰(C^dg A)` *are* `CochainComplex.HomComplex.CohomologyClass _ _ 0`, and then
to use `CohomologyClass.homAddEquiv`, which Mathlib already proves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

open CategoryTheory CochainComplex CochainComplex.HomComplex

variable {A : Type u} [Category.{v} A] [Preadditive A]

namespace Cdg

/-- This repository's degree-zero cocycles are Mathlib's. -/
lemma cocycles_eq (K L : Cdg A) :
    cocycles K L = HomComplex.cocycle (of A K) (of A L) 0 := rfl

/-- This repository's degree-zero coboundaries are Mathlib's, transported along
`cocycles_eq`. Mathlib's version is a subgroup of the cocycles and asks for a
primitive in degree `m` with `m + 1 = 0`; this one is the range of `δ (-1) 0`.
The two conditions are the same condition. -/
lemma mem_coboundaries_iff' (K L : Cdg A) (f : (DGCategoryStruct.dgHom K L).X 0) :
    f ∈ _root_.coboundaries K L ↔ ∃ β : Cochain (of A K) (of A L) (-1), δ (-1) 0 β = f :=
  Iff.rfl

/-!
## Where this stops, and why

Two identifications hold **definitionally**, which is the substance of the seam:

* `cocycles_eq` — this repository's degree-zero cocycles are Mathlib's `cocycle`;
* `mem_coboundaries_iff'` — its coboundaries are Mathlib's condition at `m = -1`.

What is not yet built is the packaging. `H0`'s Hom-group is
`↥(cocycles K L) ⧸ H0.coboundariesIn K L`, and Mathlib's `CohomologyClass K L 0`
is `Cocycle K L 0 ⧸ HomComplex.coboundaries K L 0`. Same underlying type, same
subgroup — but `Cocycle` is a `def` for `↥(cocycle …)` carrying its own
`instAddCommGroupCocycle`, while the subgroup carries the one `AddSubgroup`
supplies. `AddSubgroup` is indexed by that instance, so
`HomComplex.coboundaries … 0` and `H0.coboundariesIn …` do not even have the
same type as far as `rw` is concerned, and the `ext` proof fails on an
application type mismatch rather than on any mathematical content.

The way through is to build the equivalence on representatives with
`QuotientAddGroup.map` rather than to make the two subgroup types agree — the
instance mismatch is not something to argue away, it is something to route
around. That is the next commit, and after it `CohomologyClass.homAddEquiv`
plus `shiftFunctorZero` give the Hom-level seam.

This is the same lesson as everywhere else in this track, one level up: two
things can be definitionally identical and still not interchangeable to
elaboration that matches on instance paths.
-/

end Cdg
