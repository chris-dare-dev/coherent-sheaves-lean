/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Slicing.FiltrationOperations
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart

/-!
# Phase truncations and the t-structure interface

This file isolates the final input needed to construct a t-structure from an
owner slicing: a distinguished triangle separating positive from nonpositive
HN phases.  The structure construction itself is proved here from that input;
the canonical decomposition supplied by an HN filtration is developed next.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace BridgelandStabLean.Foundation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Distinguished phase truncations at the boundary `0`.  This is the precise
decomposition datum required by the half-open t-structure convention. -/
class Slicing.HasPhaseTruncations (s : Slicing C) : Prop where
  exists_triangle (A : C) :
    ∃ (X Y : C) (_ : s.gtProp C 0 X) (_ : s.leProp C 0 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C

/-- A slicing with phase truncations determines a t-structure.  Its heart uses
the half-open convention `P((0, 1])`. -/
def Slicing.toTStructure (s : Slicing C) [s.HasPhaseTruncations C] :
    CategoryTheory.Triangulated.TStructure C where
  le n := s.gtProp C (-n)
  ge n := s.leProp C (1 - n)
  le_isClosedUnderIsomorphisms _ := inferInstance
  ge_isClosedUnderIsomorphisms _ := inferInstance
  le_shift n a n' h X hX := by
    have ha : (a : ℝ) + n' = n := by exact_mod_cast h
    have phase : (-n' : ℝ) = -n + a := by linarith
    rw [phase]
    exact s.gtProp_shift C _ X a hX
  ge_shift n a n' h X hX := by
    have ha : (a : ℝ) + n' = n := by exact_mod_cast h
    have phase : (1 - n' : ℝ) = (1 - n) + a := by linarith
    rw [phase]
    exact s.leProp_shift C _ X a hX
  zero' {X Y} f hX hY := by
    exact s.zero_of_gtProp_leProp C (by simpa using hX) (by simpa using hY) f
  le_zero_le := by
    simpa using s.gtProp_anti C (show (-1 : ℝ) ≤ 0 by norm_num)
  ge_one_le := by
    simpa using s.leProp_mono C (show (0 : ℝ) ≤ 1 by norm_num)
  exists_triangle_zero_one A := by
    obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ :=
      Slicing.HasPhaseTruncations.exists_triangle (s := s) A
    exact ⟨X, Y, by simpa using hX, by simpa using hY, f, g, h, hT⟩

@[simp]
theorem Slicing.toTStructure_heart_iff (s : Slicing C) [s.HasPhaseTruncations C]
    (E : C) : (s.toTStructure C).heart E ↔ s.gtProp C 0 E ∧ s.leProp C 1 E := by
  change (s.toTStructure C).le 0 E ∧ (s.toTStructure C).ge 0 E ↔ _
  simp only [Slicing.toTStructure, Int.cast_zero, neg_zero, sub_zero]

end BridgelandStabLean.Foundation
