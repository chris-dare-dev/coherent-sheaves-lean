/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.CompactlyGenerated.Brown
import DerivedAlgGeo.CategoryTheory.Triangulated.TStructure.Restriction

/-!
# Ind-extended t-structures

This file names the output of Lemma A.14 in arXiv:2607.28411v1 without
asserting its geometric existence. An Ind-extension has a compactly generated
large t-structure, aisle `Coprod(Dᵇ≤0)`, and restriction equal to the original
bounded t-structure.

The record is theorem output data, not a replacement for Neeman's theorem.
`IndExtensionData.ofApproximation` now derives the large t-structure, aisle
formula, and compact generation from the A.13 output; only the geometric
restriction statements remain as A.14-specific inputs. Brown representability
and scheme-specific restriction remain the construction required by SF7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

universe w v u

namespace CategoryTheory.Triangulated.TStructure

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

/-- The large-category image of the nonpositive objects in a t-structure on
a full subcategory. -/
def boundedAisle (P : ObjectProperty C) [P.IsTriangulated]
    (t : TStructure P.FullSubcategory) : ObjectProperty C :=
  (t.le 0).map P.ι

/-- The precise output package of Lemma A.14.

`largeAisle` is clause (i), `compactlyGenerated` is clause (ii), and the two
restriction equivalences are clause (iii). -/
structure IndExtensionData (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory) (large : TStructure C) : Prop where
  /-- The original t-structure is bounded. -/
  small_isBounded : small.IsBounded
  /-- Clause (i): the large aisle is `Coprod` of the bounded aisle. -/
  largeAisle : large.le 0 = (boundedAisle P small).coprodClosure.{w}
  /-- Clause (ii): the large t-structure is compactly generated. -/
  compactlyGenerated : ∃ G : ObjectProperty C,
    large.IsCompactlyGeneratedBy.{w} G
  /-- The large t-structure restricts to the selected full subcategory. -/
  hasInduced : P.HasInducedTStructure large
  /-- Clause (iii), coconnective half, in every degree. -/
  isLE_iff (X : P.FullSubcategory) (n : ℤ) :
    large.IsLE X.obj n ↔ small.IsLE X n
  /-- Clause (iii), connective half, in every degree. -/
  isGE_iff (X : P.FullSubcategory) (n : ℤ) :
    large.IsGE X.obj n ↔ small.IsGE X n

namespace IndExtensionData

/-- Assemble the output of A.14 from the A.13 approximation and the geometric
restriction theorem.

The large t-structure, its aisle formula, and compact generation are derived
from `happrox`.  The only remaining A.14-specific inputs are stability of the
selected bounded subcategory under truncation and the two recognition
equivalences; these are exactly the geometric restriction statements rather
than another large t-structure existence assumption. -/
theorem ofApproximation
    (P : ObjectProperty C) [P.IsTriangulated]
    (small : TStructure P.FullSubcategory)
    (hsmall : small.IsBounded)
    (happrox : CompactGeneratorApproximation.{w} (boundedAisle P small))
    (hcompact : boundedAisle P small ≤
      ObjectProperty.compactObjects.{w} (C := C))
    (hInduced : P.HasInducedTStructure happrox.tStructure)
    (hLE : ∀ (X : P.FullSubcategory) (n : ℤ),
      happrox.tStructure.IsLE X.obj n ↔ small.IsLE X n)
    (hGE : ∀ (X : P.FullSubcategory) (n : ℤ),
      happrox.tStructure.IsGE X.obj n ↔ small.IsGE X n) :
    IndExtensionData.{w} P small happrox.tStructure := by
  letI : P.HasInducedTStructure happrox.tStructure := hInduced
  exact
    { small_isBounded := hsmall
      largeAisle := happrox.tStructure_le_zero
      compactlyGenerated :=
        ⟨boundedAisle P small, happrox.isCompactlyGeneratedBy hcompact⟩
      hasInduced := hInduced
      isLE_iff := hLE
      isGE_iff := hGE }

end IndExtensionData

end CategoryTheory.Triangulated.TStructure
