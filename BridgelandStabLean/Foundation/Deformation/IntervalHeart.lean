/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Slicing.IntrinsicPhaseBounds
import BridgelandStabLean.Foundation.Slicing.PhaseShift
import BridgelandStabLean.Foundation.Slicing.PhaseTruncation

/-!
# Placing thin owner intervals in shifted hearts

Objects whose intrinsic phases lie in an interval of length at most one belong
to a real phase-shifted owner heart.  These lemmas provide the categorical
bridge used by the small-gap part of deformed hom-vanishing.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace BridgelandStabLean.Foundation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- Intrinsic phases in `(t,t+1]` place an object in the heart of the slicing
shifted by `t`. -/
theorem Slicing.mem_phaseShiftHeart_of_intrinsic_bounds
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {t : ℝ}
    (hminus : t < s.phiMinus C E hE)
    (hplus : s.phiPlus C E hE ≤ t + 1) :
    ((s.phaseShift C t).toTStructure C).heart E := by
  rw [(s.phaseShift C t).toTStructure_heart_iff C E]
  constructor
  · exact (s.phaseShift_gtProp_zero C t E).mpr
      (s.gtProp_of_phiMinus_gt C hE hminus)
  · exact (s.phaseShift_leProp C t 1 E).mpr
      (s.leProp_of_phiPlus_le C hE (by simpa [add_comm] using hplus))

/-- Every object in an open interval of width at most one lies in the heart
based at its lower endpoint. -/
theorem Slicing.mem_phaseShiftHeart_of_intervalProp
    (s : Slicing C) {E : C} {a b : ℝ}
    (hI : s.intervalProp C a b E) (hwidth : b ≤ a + 1) :
    ((s.phaseShift C a).toTStructure C).heart E := by
  by_cases hE : IsZero E
  · rw [(s.phaseShift C a).toTStructure_heart_iff C E]
    exact ⟨Or.inl hE, Or.inl hE⟩
  · apply s.mem_phaseShiftHeart_of_intrinsic_bounds C hE
    · exact s.phiMinus_gt_of_intervalProp C hE hI
    · exact (s.phiPlus_lt_of_intervalProp C hE hI).le.trans hwidth

omit [IsTriangulated C] in
/-- An intrinsic phase window also gives simultaneous old lower and upper
phase-cut membership. -/
theorem Slicing.gtProp_leProp_of_intrinsic_bounds
    (s : Slicing C) {E : C} (hE : ¬IsZero E) {a b : ℝ}
    (hminus : a < s.phiMinus C E hE)
    (hplus : s.phiPlus C E hE ≤ b) :
    s.gtProp C a E ∧ s.leProp C b E :=
  ⟨s.gtProp_of_phiMinus_gt C hE hminus,
    s.leProp_of_phiPlus_le C hE hplus⟩

end BridgelandStabLean.Foundation
