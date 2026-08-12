/-
Copyright (c) 2026 Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Zero objects in a full subcategory

`ObjectProperty.FullSubcategory.isZero_of_obj_isZero`: an object of
`P.FullSubcategory` is zero as soon as its underlying object is zero.

## Provenance and licence

Vendored verbatim from `BridgelandStability.HeartEquivalence.Basic` (line 100 at
revision `9e48f23a`), which is Apache-2.0. **This file retains the Apache-2.0
header of its origin and is not relicensed**, notwithstanding the MIT default of
the rest of this repository.

## Why it is here

Importing it from the foundational library puts `BridgelandStability` on the
import path of every consumer. The two files in
`StabilityCondition/Weak/Tilting/Cohomology/` are otherwise free of stability
content, and this lemma is one of exactly two constants standing between them
and an anchor-free import path.

Note that the foundational library also carries a **different**, same-named
theorem `Slicing.IntervalCat.isZero_of_obj_isZero`
(`IntervalCategory/Basic.lean:97`). That one is about interval categories of a
slicing and is not what this file supplies.

## Upstreaming

Absent from Mathlib by name at both `v4.29.0` (`8a178386`) and `v4.32.1`
(`520045ab`). It is a general statement about `ObjectProperty.FullSubcategory`
with no triangulated or stability content, so it belongs upstream.

**Deletion condition** — delete this file when

```
lake build
```

resolves `CategoryTheory.ObjectProperty.FullSubcategory.isZero_of_obj_isZero`
from Mathlib.
-/

universe v u

open CategoryTheory
open CategoryTheory.Limits
open scoped ZeroObject

namespace BridgelandStabLean.ForMathlib

namespace CategoryTheory

/-- If the underlying object of a full-subcategory object is zero, then the
full-subcategory object itself is zero. -/
theorem ObjectProperty.FullSubcategory.isZero_of_obj_isZero
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {P : ObjectProperty C}
    [HasZeroMorphisms P.FullSubcategory] [HasZeroObject P.FullSubcategory]
    {X : P.FullSubcategory} (hX : IsZero X.obj) : IsZero X := by
  let Z : P.FullSubcategory := 0
  have hZ : IsZero Z.obj := (P.ι.map_isZero (show IsZero Z from isZero_zero _))
  let e : X.obj ≅ Z.obj := hX.iso hZ
  exact (show IsZero Z from isZero_zero _).of_iso (P.isoMk e)

end CategoryTheory

end BridgelandStabLean.ForMathlib
