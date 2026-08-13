/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation
import BridgelandStability.GrothendieckGroup.Basic
import BridgelandStability.Slicing.Defs
import BridgelandStability.StabilityCondition.Defs

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

namespace GrothendieckGroup

instance vendorOf_isTriangleAdditive :
    Foundation.IsTriangleAdditive (fun X => CategoryTheory.Triangulated.K₀.of C X) where
  additive T hT := CategoryTheory.Triangulated.K₀.of_triangle C T hT

/-- Convert an owner Grothendieck class to the retained vendor quotient. -/
def toVendor : Foundation.K₀ C →+ CategoryTheory.Triangulated.K₀ C :=
  Foundation.K₀.lift C (fun X => CategoryTheory.Triangulated.K₀.of C X)

@[simp]
theorem toVendor_of (X : C) :
    toVendor C (Foundation.K₀.of C X) = CategoryTheory.Triangulated.K₀.of C X :=
  Foundation.K₀.lift_of C _ X

instance ownerOf_isTriangleAdditive :
    CategoryTheory.Triangulated.IsTriangleAdditive (fun X => Foundation.K₀.of C X) where
  additive T hT := Foundation.K₀.of_triangle C T hT

/-- Convert a retained vendor Grothendieck class to the owner quotient. -/
def ofVendor : CategoryTheory.Triangulated.K₀ C →+ Foundation.K₀ C :=
  CategoryTheory.Triangulated.K₀.lift C (fun X => Foundation.K₀.of C X)

@[simp]
theorem ofVendor_of (X : C) :
    ofVendor C (CategoryTheory.Triangulated.K₀.of C X) = Foundation.K₀.of C X :=
  CategoryTheory.Triangulated.K₀.lift_of C _ X

@[simp]
theorem ofVendor_toVendor : (ofVendor C).comp (toVendor C) = AddMonoidHom.id (Foundation.K₀ C) := by
  apply Foundation.K₀.hom_ext C
  intro X
  simp

@[simp]
theorem toVendor_ofVendor : (toVendor C).comp (ofVendor C) =
    AddMonoidHom.id (CategoryTheory.Triangulated.K₀ C) := by
  apply CategoryTheory.Triangulated.K₀.hom_ext C
  intro X
  simp

/-- The owner and retained Grothendieck quotients are canonically additively
equivalent because they impose the same distinguished-triangle relations. -/
def equiv : Foundation.K₀ C ≃+ CategoryTheory.Triangulated.K₀ C where
  toFun := toVendor C
  invFun := ofVendor C
  left_inv x := by
    have h := DFunLike.congr_fun (ofVendor_toVendor C) x
    exact h
  right_inv x := by
    have h := DFunLike.congr_fun (toVendor_ofVendor C) x
    exact h
  map_add' x y := map_add (toVendor C) x y

end GrothendieckGroup

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

namespace PreStabilityCondition

variable {Λ : Type*} [AddCommGroup Λ]

/-- Convert an owner pre-stability condition to the retained representation.
The retained class map is obtained by precomposing with the canonical map from
the retained Grothendieck quotient to the owner quotient. -/
def toVendor {v : Foundation.K₀ C →+ Λ}
    (σ : Foundation.PreStabilityCondition.WithClassMap C v) :
    CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap C
      (v.comp (GrothendieckGroup.ofVendor C)) where
  slicing := Slicing.toVendor C σ.slicing
  Z := σ.Z
  compat' φ E hP hE := by
    simpa [Foundation.PreStabilityCondition.WithClassMap.charge_def] using
      σ.compat φ E hP hE

/-- Convert a retained pre-stability condition whose class map comes from the
owner quotient back to the owner representation. -/
def ofVendor {v : Foundation.K₀ C →+ Λ}
    (σ : CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap C
      (v.comp (GrothendieckGroup.ofVendor C))) :
    Foundation.PreStabilityCondition.WithClassMap C v where
  slicing := Slicing.ofVendor C σ.slicing
  Z := σ.Z
  compatible φ E hP hE := by
    simpa [CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge_def,
      CategoryTheory.Triangulated.cl] using
      σ.compat φ E hP hE

private theorem vendor_ext {v : CategoryTheory.Triangulated.K₀ C →+ Λ}
    {σ τ : CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap C v}
    (hslicing : σ.slicing = τ.slicing) (hZ : σ.Z = τ.Z) : σ = τ := by
  rcases σ with ⟨sσ, Zσ, cσ⟩
  rcases τ with ⟨sτ, Zτ, cτ⟩
  simp at hslicing hZ
  cases hslicing
  cases hZ
  cases Subsingleton.elim cσ cτ
  rfl

@[simp]
theorem ofVendor_toVendor {v : Foundation.K₀ C →+ Λ}
    (σ : Foundation.PreStabilityCondition.WithClassMap C v) :
    ofVendor C (toVendor C σ) = σ :=
  Foundation.PreStabilityCondition.WithClassMap.ext rfl rfl

@[simp]
theorem toVendor_ofVendor {v : Foundation.K₀ C →+ Λ}
    (σ : CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap C
      (v.comp (GrothendieckGroup.ofVendor C))) :
    toVendor C (ofVendor C σ) = σ :=
  vendor_ext (C := C) (CategoryTheory.Triangulated.Slicing.ext C rfl) rfl

/-- Owner and retained pre-stability conditions are equivalent after the class
map is transported across the canonical Grothendieck-group equivalence. -/
def equiv (v : Foundation.K₀ C →+ Λ) :
    Foundation.PreStabilityCondition.WithClassMap C v ≃
      CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap C
        (v.comp (GrothendieckGroup.ofVendor C)) where
  toFun := toVendor C
  invFun := ofVendor C
  left_inv := ofVendor_toVendor C
  right_inv := toVendor_ofVendor C

end PreStabilityCondition

end BridgelandStabLean.Compatibility.BridgelandStability
