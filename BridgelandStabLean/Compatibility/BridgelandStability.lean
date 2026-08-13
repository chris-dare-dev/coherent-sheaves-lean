/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation
import BridgelandStability.Slicing.Defs

/-!
# Compatibility with the vendored BridgelandStability API

This file is the explicit boundary between the repository-owned MIT API and
the temporarily retained Apache-2.0 vendor API. The conversions are lossless;
they allow downstream modules to migrate one layer at a time without making
the owner-authored foundation depend conceptually on vendor definitions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace BridgelandStabLean.Compatibility.BridgelandStability

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace PostnikovTower

/-- Convert an owner-authored Postnikov tower to the vendored representation. -/
def toVendor {E : C} (P : Foundation.PostnikovTower C E) :
    CategoryTheory.Triangulated.PostnikovTower C E where
  n := P.n
  chain := P.chain
  triangle := P.triangle
  triangle_dist := P.triangle_dist
  triangle_obj₁ := P.triangle_obj₁
  triangle_obj₂ := P.triangle_obj₂
  base_isZero := P.base_isZero
  top_iso := P.top_iso
  zero_isZero := P.zero_isZero

/-- Convert a vendored Postnikov tower to the owner-authored representation. -/
def ofVendor {E : C} (P : CategoryTheory.Triangulated.PostnikovTower C E) :
    Foundation.PostnikovTower C E where
  n := P.n
  chain := P.chain
  triangle := P.triangle
  triangle_dist := P.triangle_dist
  triangle_obj₁ := P.triangle_obj₁
  triangle_obj₂ := P.triangle_obj₂
  base_isZero := P.base_isZero
  top_iso := P.top_iso
  zero_isZero := P.zero_isZero

@[simp]
theorem ofVendor_toVendor {E : C} (P : Foundation.PostnikovTower C E) :
    ofVendor C (toVendor C P) = P := by
  cases P
  rfl

@[simp]
theorem toVendor_ofVendor {E : C} (P : CategoryTheory.Triangulated.PostnikovTower C E) :
    toVendor C (ofVendor C P) = P := by
  cases P
  rfl

end PostnikovTower

namespace HNFiltration

/-- Convert an owner-authored HN filtration to the vendored representation. -/
def toVendor {P : ℝ → ObjectProperty C} {E : C} (F : Foundation.HNFiltration C P E) :
    CategoryTheory.Triangulated.HNFiltration C P E where
  toPostnikovTower := PostnikovTower.toVendor C F.toPostnikovTower
  φ := F.φ
  hφ := F.hφ
  semistable := F.semistable

/-- Convert a vendored HN filtration to the owner-authored representation. -/
def ofVendor {P : ℝ → ObjectProperty C} {E : C}
    (F : CategoryTheory.Triangulated.HNFiltration C P E) : Foundation.HNFiltration C P E where
  toPostnikovTower := PostnikovTower.ofVendor C F.toPostnikovTower
  φ := F.φ
  hφ := F.hφ
  semistable := F.semistable

@[simp]
theorem ofVendor_toVendor {P : ℝ → ObjectProperty C} {E : C}
    (F : Foundation.HNFiltration C P E) : ofVendor C (toVendor C F) = F := by
  cases F
  rfl

@[simp]
theorem toVendor_ofVendor {P : ℝ → ObjectProperty C} {E : C}
    (F : CategoryTheory.Triangulated.HNFiltration C P E) : toVendor C (ofVendor C F) = F := by
  cases F
  rfl

end HNFiltration

namespace Slicing

/-- Convert an owner-authored slicing to the vendored representation. -/
def toVendor (s : Foundation.Slicing C) : CategoryTheory.Triangulated.Slicing C where
  P := s.P
  closedUnderIso := s.closedUnderIso
  zero_mem := s.zero_mem
  shift_iff := s.shift_iff
  hom_vanishing := s.hom_vanishing
  hn_exists E := Nonempty.map (HNFiltration.toVendor C) (s.hn_exists E)

/-- Convert a vendored slicing to the owner-authored representation. -/
def ofVendor (s : CategoryTheory.Triangulated.Slicing C) : Foundation.Slicing C where
  P := s.P
  closedUnderIso := s.closedUnderIso
  zero_mem := s.zero_mem
  shift_iff := s.shift_iff
  hom_vanishing := s.hom_vanishing
  hn_exists E := Nonempty.map (HNFiltration.ofVendor C) (s.hn_exists E)

@[simp]
theorem toVendor_P (s : Foundation.Slicing C) : (toVendor C s).P = s.P := rfl

@[simp]
theorem ofVendor_P (s : CategoryTheory.Triangulated.Slicing C) : (ofVendor C s).P = s.P := rfl

@[simp]
theorem ofVendor_toVendor (s : Foundation.Slicing C) : ofVendor C (toVendor C s) = s :=
  Foundation.Slicing.ext C rfl

@[simp]
theorem toVendor_ofVendor (s : CategoryTheory.Triangulated.Slicing C) : toVendor C (ofVendor C s) = s :=
  CategoryTheory.Triangulated.Slicing.ext C rfl

end Slicing

end BridgelandStabLean.Compatibility.BridgelandStability
