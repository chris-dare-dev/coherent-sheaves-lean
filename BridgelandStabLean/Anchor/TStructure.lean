/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.TStructure
import BridgelandStability.Slicing.TStructure

/-!
# Bridging the anchor's t-structure vocabulary

`BridgelandStabLean.TStructure.Exactness` is anchor-free by design, so it must
restate boundedness rather than reuse the foundational library's version. Both
definitions therefore exist in any environment that imports both, under the same
final name component:

* `CategoryTheory.Triangulated.TStructure.IsBounded` — the anchor's, stated
  through `t.le` / `t.ge` (`BridgelandStability/Slicing/TStructure.lean:215`);
* `BridgelandStabLean.TStructure.IsBounded` — the anchor-free one, stated
  through the `IsLE` / `IsGE` classes.

They are equivalent, and this file proves it. They are **not** definitionally
equal, and the difference is easy to miss, because dot notation resolves in the
namespace of the *type* rather than in the open namespaces: `t.IsBounded` is
always the anchor's, even in a file that has `open BridgelandStabLean`. A
downstream author who writes `t.IsBounded` and then reaches for `exists_isLE`
gets no error, just a lemma that does not apply. Convert with
`isBounded_iff_anchor` instead of assuming the names interchange.

## Placement

This module is the compatibility layer for the foundational library and is
therefore deliberately **not** anchor-free; it is excluded from
`scripts/check_anchor_free.py` for that reason. Nothing under
`BridgelandStabLean/TStructure/` may import it.
-/

universe v u

namespace BridgelandStabLean.Anchor

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The anchor-free `IsBounded` agrees with the foundational library's.

Left to right unpacks the `IsLE` / `IsGE` classes into the underlying
`t.le` / `t.ge` memberships; right to left repackages them. -/
theorem isBounded_iff_anchor (t : TStructure C) :
    BridgelandStabLean.TStructure.IsBounded t ↔
      CategoryTheory.Triangulated.TStructure.IsBounded t := by
  constructor
  · intro h E
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h E
    exact ⟨b, a, t.le_of_isLE E b, t.ge_of_isGE E a⟩
  · intro h X
    obtain ⟨a, b, ha, hb⟩ := h X
    exact ⟨⟨b, ⟨hb⟩⟩, ⟨a, ⟨ha⟩⟩⟩

/-- The anchor's boundedness gives the anchor-free one. -/
theorem isBounded_of_anchor {t : TStructure C}
    (h : CategoryTheory.Triangulated.TStructure.IsBounded t) :
    BridgelandStabLean.TStructure.IsBounded t :=
  (isBounded_iff_anchor t).2 h

/-- The anchor-free boundedness gives the anchor's. -/
theorem anchor_isBounded {t : TStructure C}
    (h : BridgelandStabLean.TStructure.IsBounded t) :
    CategoryTheory.Triangulated.TStructure.IsBounded t :=
  (isBounded_iff_anchor t).1 h

/-- **Bounded implies nondegenerate**, stated against the anchor's boundedness.

This is the payoff of the bridge: the existing consumers of boundedness in this
repository (`Weak/HarderNarasimhan/Ambient.lean`, for one) all hold the anchor's
predicate, and this is what lets them reach `IsNondegenerate`. -/
theorem isNondegenerate_of_anchor_isBounded {t : TStructure C}
    (h : CategoryTheory.Triangulated.TStructure.IsBounded t) :
    BridgelandStabLean.TStructure.IsNondegenerate t :=
  BridgelandStabLean.TStructure.isNondegenerate_of_isBounded (isBounded_of_anchor h)

end BridgelandStabLean.Anchor
