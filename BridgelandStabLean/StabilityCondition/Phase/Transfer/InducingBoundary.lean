/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Phase.Transfer.Equivariance
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The Polishchuk/Ind inducing boundary

Appendix A of arXiv:2607.28411v1 proves that a raw preimage collection is a
slicing only under substantial extra hypotheses.  In Theorem A.17 these
include presentable/Ind-completed categories, boundedness reflection, and
right t-exactness of the monad; Corollary A.23 uses the dual condition
`Phi PhiL(P(phi)) ⊆ P(≥ phi)`.  Propositions 3.3 and 3.8 then verify the
corresponding geometric conditions for finite and faithfully-flat morphisms.

This file records the categorical shape visible in the current bounded
triangulated API.  It does **not** assert that adjunction plus conservativity
produces a slicing: Remarks 3.2 and 3.7 explicitly say otherwise.  The output
of the future Ind/geometric theorem is exactly `Slicing.PreimageData`.
-/

noncomputable section

open BridgelandStabLean.Foundation
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂

namespace BridgelandStabLean.Foundation

variable {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- The bounded categorical fragment of the left-adjoint inducing criterion
from Corollary A.23.

The composite `L ⋙ F` is the monad on the category carrying `s`.  The phase
condition is the source's `(v')` hypothesis.  Presentability, Ind-extension,
and boundedness-reflection are deliberately not fabricated here. -/
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

/-- The exact theorem still required to connect the Appendix-A hypotheses to
the bounded slicing constructor.

No inhabitant is provided in this repository: proving it requires the
presentable/Ind and t-structure machinery listed in Theorem A.17. -/
def HasLeftAdjointInducingTheorem : Prop :=
  ∀ {C : Type u₁} [Category.{v₁} C] [HasZeroObject C] [HasShift C ℤ]
      [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
      [Pretriangulated C]
    {D : Type u₂} [Category.{v₂} D] [HasZeroObject D] [HasShift D ℤ]
      [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive]
      [Pretriangulated D]
    (s : Slicing D) (F : C ⥤ D) (L : D ⥤ C),
    s.LeftAdjointInducingPremise F L → s.PreimageData F

end BridgelandStabLean.Foundation
