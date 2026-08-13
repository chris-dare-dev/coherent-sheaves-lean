/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Slicing.PhaseCutClosure
import BridgelandStabLean.Foundation.Slicing.PhaseShift
import BridgelandStabLean.Foundation.Slicing.PhaseTruncation

/-!
# Owner phase truncation at an arbitrary real cutoff

Translate an owner HN filtration so a real cutoff becomes zero, apply the
owner zero-cut truncation, and translate the two phase-cut memberships back.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace BridgelandStabLean.Foundation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- Every owner HN filtration admits a distinguished truncation triangle at
an arbitrary real phase cutoff. -/
theorem Slicing.exists_cutoff_truncation (s : Slicing C) {A : C}
    (F : HNFiltration C s.P A) (t : ℝ) :
    ∃ (X Y : C) (_ : s.gtProp C t X) (_ : s.leProp C t Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ :=
    (s.phaseShift C t).exists_phase_truncation C A (F.phaseShift C t)
  exact ⟨X, Y, (s.phaseShift_gtProp_zero C t X).mp hX,
    (s.phaseShift_leProp_zero C t Y).mp hY, f, g, h, hT⟩

end BridgelandStabLean.Foundation
