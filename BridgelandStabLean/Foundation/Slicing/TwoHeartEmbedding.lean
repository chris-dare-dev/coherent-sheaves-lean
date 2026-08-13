/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Deformation.IntervalHeart
import BridgelandStabLean.Foundation.Slicing.BoundaryTruncation

/-!
# Two-heart embeddings of owner interval categories

Every phase interval of width at most one embeds fully faithfully into two
adjacent abelian slicing hearts.  The left heart controls kernels and images;
the right half-open heart controls cokernels and coimages.  This is the owner
foundation for the quasi-abelian interval machinery used by target transport.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace BridgelandStabLean.Foundation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- Owner interval objects lie in the left adjacent slicing heart
`P((a,a+1])`. -/
theorem Slicing.intervalProp_implies_leftHeart (s : Slicing C)
    {a b : ℝ} (hab : b - a ≤ 1) {E : C}
    (hE : s.intervalProp C a b E) :
    ((s.phaseShift C a).toTStructure C).heart E := by
  apply s.mem_phaseShiftHeart_of_intervalProp C hE
  linarith

/-- The dual half-open t-structure associated to an owner slicing.  Its
heart is `P([0,1))`. -/
def Slicing.toDualTStructure (s : Slicing C) :
    CategoryTheory.Triangulated.TStructure C where
  le n := s.geProp C (-n)
  ge n := s.ltProp C (1 - n)
  le_isClosedUnderIsomorphisms _ := inferInstance
  ge_isClosedUnderIsomorphisms _ := inferInstance
  le_shift n a n' h X hX := by
    have ha : (a : ℝ) + n' = n := by exact_mod_cast h
    have phase : (-n' : ℝ) = -n + a := by linarith
    rw [phase]
    exact s.geProp_shift C _ X a hX
  ge_shift n a n' h X hX := by
    have ha : (a : ℝ) + n' = n := by exact_mod_cast h
    have phase : (1 - n' : ℝ) = (1 - n) + a := by linarith
    rw [phase]
    exact s.ltProp_shift C _ X a hX
  zero' {X Y} f hX hY := by
    exact s.zero_of_geProp_ltProp C (by simpa using hX) (by simpa using hY) f
  le_zero_le := by
    simpa using s.geProp_anti C (show (-1 : ℝ) ≤ 0 by norm_num)
  ge_one_le := by
    simpa using s.ltProp_mono C (show (0 : ℝ) ≤ 1 by norm_num)
  exists_triangle_zero_one A := by
    obtain ⟨F⟩ := s.hn_exists A
    obtain ⟨X, Y, hX, hY, f, g, h, hT⟩ :=
      s.exists_dual_phase_truncation C A F
    exact ⟨X, Y, by simpa using hX, by simpa using hY, f, g, h, hT⟩

@[simp]
theorem Slicing.toDualTStructure_heart_iff (s : Slicing C) (E : C) :
    (s.toDualTStructure C).heart E ↔
      s.geProp C 0 E ∧ s.ltProp C 1 E := by
  change (s.toDualTStructure C).le 0 E ∧
      (s.toDualTStructure C).ge 0 E ↔ _
  simp only [Slicing.toDualTStructure, Int.cast_zero, neg_zero, sub_zero]

/-- Owner interval objects lie in the right adjacent half-open slicing heart
`P([b-1,b))`. -/
theorem Slicing.intervalProp_implies_rightHeart (s : Slicing C)
    {a b : ℝ} (hab : b - a ≤ 1) {E : C}
    (hE : s.intervalProp C a b E) :
    ((s.phaseShift C (b - 1)).toDualTStructure C).heart E := by
  rw [(s.phaseShift C (b - 1)).toDualTStructure_heart_iff C]
  constructor
  · rw [s.phaseShift_geProp_zero C]
    exact s.geProp_anti C (by linarith) E
      (s.geProp_of_gtProp C E (s.gtProp_of_intervalProp C hE))
  · rw [s.phaseShift_ltProp C]
    have heq : 1 + (b - 1) = b := by linarith
    rw [heq]
    exact s.ltProp_of_intervalProp C hE

/-- Fully faithful inclusion of an owner interval category into its left
adjacent heart. -/
abbrev Slicing.IntervalCat.toLeftHeart (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    s.IntervalCat C a b ⥤
      ((s.phaseShift C a).toTStructure C).heart.FullSubcategory where
  obj X := ⟨X.obj, s.intervalProp_implies_leftHeart C hab X.property⟩
  map f := ObjectProperty.homMk f.hom

instance Slicing.IntervalCat.toLeftHeart_full (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Full (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab) where
  map_surjective {_ _} f := ⟨ObjectProperty.homMk f.hom, rfl⟩

instance Slicing.IntervalCat.toLeftHeart_faithful (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Faithful (Slicing.IntervalCat.toLeftHeart (C := C) (s := s) a b hab) where
  map_injective := by
    intro X Y f g h
    cases f
    cases g
    cases h
    rfl

/-- Fully faithful inclusion of an owner interval category into its right
adjacent half-open heart. -/
abbrev Slicing.IntervalCat.toRightHeart (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    s.IntervalCat C a b ⥤
      ((s.phaseShift C (b - 1)).toDualTStructure C).heart.FullSubcategory where
  obj X := ⟨X.obj, s.intervalProp_implies_rightHeart C hab X.property⟩
  map f := ObjectProperty.homMk f.hom

instance Slicing.IntervalCat.toRightHeart_full (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Full (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab) where
  map_surjective {_ _} f := ⟨ObjectProperty.homMk f.hom, rfl⟩

instance Slicing.IntervalCat.toRightHeart_faithful (s : Slicing C) (a b : ℝ)
    (hab : b - a ≤ 1) :
    Functor.Faithful (Slicing.IntervalCat.toRightHeart (C := C) (s := s) a b hab) where
  map_injective := by
    intro X Y f g h
    cases f
    cases g
    cases h
    rfl

end BridgelandStabLean.Foundation
