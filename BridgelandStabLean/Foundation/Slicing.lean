/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.PostnikovTower
import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Data.Real.Basic

/-!
# Owner-authored Harder--Narasimhan filtrations and slicings

These are the root data structures for the repository-owned stability API.
They are deliberately small: operations on filtrations, interval categories,
local finiteness, and stability conditions are migrated in later slices.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v

namespace BridgelandStabLean.Foundation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- A Harder--Narasimhan filtration: a Postnikov tower whose factors have
strictly decreasing phases and lie in their corresponding phase slices. -/
structure HNFiltration (P : ℝ → ObjectProperty C) (E : C)
    extends PostnikovTower C E where
  /-- Phase of each factor. -/
  φ : Fin n → ℝ
  /-- Factor phases are strictly decreasing. -/
  hφ : StrictAnti φ
  /-- Each factor belongs to its recorded phase slice. -/
  semistable : ∀ j, P (φ j) (toPostnikovTower.factor j)

/-- A Bridgeland slicing on a pretriangulated category. -/
structure Slicing where
  /-- Semistable objects of phase `φ`. -/
  P : ℝ → ObjectProperty C
  /-- Phase slices are invariant under isomorphism. -/
  closedUnderIso : ∀ φ, (P φ).IsClosedUnderIsomorphisms
  /-- The zero object belongs to every phase slice. -/
  zero_mem : ∀ φ, P φ (0 : C)
  /-- Shifting by one increases phase by one. -/
  shift_iff : ∀ φ X, P φ X ↔ P (φ + 1) (X⟦(1 : ℤ)⟧)
  /-- Morphisms from higher phase to lower phase vanish. -/
  hom_vanishing : ∀ φ₁ φ₂ A B,
    φ₂ < φ₁ → P φ₁ A → P φ₂ B → ∀ f : A ⟶ B, f = 0
  /-- Every object admits an HN filtration. -/
  hn_exists : ∀ E, Nonempty (HNFiltration C P E)

attribute [instance] Slicing.closedUnderIso

@[ext]
theorem Slicing.ext {s t : Slicing C} (hP : s.P = t.P) : s = t := by
  cases s
  cases t
  simp_all

/-- A zero object belongs to every phase slice, not only the chosen zero
object used by the structure field. -/
theorem Slicing.zero_mem_of_isZero (s : Slicing C) (φ : ℝ) (X : C) (hX : IsZero X) :
    s.P φ X :=
  ObjectProperty.prop_of_iso _ ((isZero_zero C).iso hX) (s.zero_mem φ)

/-- Forward form of the shift axiom. -/
theorem Slicing.shift (s : Slicing C) (φ : ℝ) (X : C) (h : s.P φ X) :
    s.P (φ + 1) (X⟦(1 : ℤ)⟧) :=
  (s.shift_iff φ X).mp h

/-- Backward form of the shift axiom. -/
theorem Slicing.unshift (s : Slicing C) (φ : ℝ) (X : C)
    (h : s.P (φ + 1) (X⟦(1 : ℤ)⟧)) : s.P φ X :=
  (s.shift_iff φ X).mpr h

end BridgelandStabLean.Foundation
