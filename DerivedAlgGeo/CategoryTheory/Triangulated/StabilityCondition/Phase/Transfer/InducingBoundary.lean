/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.Equivariance
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.InducedTStructures
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The Polishchuk/Ind inducing boundary

Appendix A of arXiv:2607.28411v1 proves that a raw preimage collection is a
slicing only under substantial extra hypotheses.  In Theorem A.17 these
include presentable/Ind-completed categories, boundedness reflection, and
right t-exactness of the monad; Corollary A.23 uses the dual condition
`Phi PhiL(P(phi)) ⊆ P(≥ phi)`.  Propositions 3.3 and 3.8 then verify the
corresponding geometric conditions for finite and faithfully-flat morphisms.

This file records the categorical shadow visible in the current bounded
triangulated API.  It does **not** assert that adjunction plus conservativity
produces a slicing: Remarks 3.2 and 3.7 explicitly say otherwise.  The actual
bounded intermediate output is `Slicing.InducedTStructures`, whose fields are
the recognition formulas (A.8); its Hom-vanishing consequence is proved in
`Phase.Transfer.InducedTStructures`.
-/

noncomputable section

open CategoryTheory.Triangulated
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Triangulated

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The old bounded categorical shadow of the left-adjoint inducing criterion
from Corollary A.23.

The composite `L ⋙ F` is the monad on the category carrying `s`.  The phase
condition resembles the bounded restriction of the source's `(v')`
hypothesis, but is not equivalent to it: `(v')` is stated in the Ind-extended
category.  Presentability, coproduct preservation, the large derived
categories, Ind-extension, and boundedness reflection are deliberately not
fabricated here.  New code should target `Slicing.InducedTStructures`; this
record remains temporarily for the existing geometric callers. -/
structure Slicing.LeftAdjointInducingPremise (s : Slicing D)
    (F : C ⥤ D) (L : D ⥤ C) where
  /-- The functor used to detect phase slices has a left adjoint. -/
  adjunction : L ⊣ F
  /-- Conservativity on bounded objects, expressed at the zero-object level
  needed by the bounded phase API. -/
  reflects_zero : ReflectsZeroObjects F
  /-- Corollary A.23 condition `(v')`: the monad sends a semistable object of
  phase `phi` into the weak upper window `P(≥ phi)`. -/
  monad_ge : ∀ (phi : ℝ) (E : D), s.P phi E →
    s.geProp D phi ((L ⋙ F).obj E)

/-- The legacy global theorem input still used by the geometric callers.

No inhabitant is provided in this repository.  Its premise is only a bounded
shadow and is not asserted to imply its conclusion.  SF7 replaces callers of
this proposition by the actual Theorem-A.17 hypotheses, constructs
`Slicing.InducedTStructures`, and then applies the Corollary-A.23 phase
truncation theorem. -/
def HasLeftAdjointInducingTheorem : Prop :=
  ∀ {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
      [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
      [Pretriangulated C]
    {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
      [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
      [Pretriangulated D]
    (s : Slicing D) (F : C ⥤ D) (L : D ⥤ C),
    s.LeftAdjointInducingPremise F L → s.PreimageData F

end CategoryTheory.Triangulated
