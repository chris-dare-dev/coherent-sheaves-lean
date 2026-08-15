/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Stability functions on abelian categories

This file introduces the repository-owned stability-function interface.  Its
central charge is additive on short exact sequences and sends every nonzero
object to the semi-closed upper half-plane.  Phase, stability, and
semistability are then defined intrinsically from that charge.

The module is Mathlib-only and is the canonical stability-function interface
for this repository.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Complex Real

universe u v

namespace CategoryTheory.Triangulated

/-- The semi-closed upper half-plane used for central charges: positive
imaginary part together with the negative real axis. -/
def semiClosedUpperHalfPlane : Set ℂ :=
  {z : ℂ | 0 < z.im} ∪ {z : ℂ | z.im = 0 ∧ z.re < 0}

theorem semiClosedUpperHalfPlane_ne_zero {z : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane) : z ≠ 0 := by
  rcases hz with him | ⟨him, hre⟩
  · exact ne_of_apply_ne im him.ne'
  · exact ne_of_apply_ne re hre.ne

theorem arg_pos_of_mem_semiClosedUpperHalfPlane {z : ℂ}
    (hz : z ∈ semiClosedUpperHalfPlane) : 0 < arg z := by
  rcases hz with him | ⟨him, hre⟩
  · refine lt_of_le_of_ne (arg_nonneg_iff.mpr him.le) ?_
    exact fun h => him.ne' (arg_eq_zero_iff.mp h.symm).2
  · have hz : z = (z.re : ℂ) := Complex.ext rfl (by simpa using him)
    rw [hz, arg_ofReal_of_neg hre]
    exact Real.pi_pos

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- An additive central charge on an abelian category whose nonzero values lie
in the semi-closed upper half-plane. -/
structure StabilityFunction where
  /-- The central charge on objects. -/
  charge : A → ℂ
  /-- Zero objects have zero charge. -/
  map_zero : ∀ E : A, IsZero E → charge E = 0
  /-- Isomorphic objects have the same charge. -/
  map_iso : ∀ {E F : A}, (E ≅ F) → charge E = charge F
  /-- The charge is additive on short exact sequences. -/
  additive : ∀ S : ShortComplex A, S.ShortExact →
    charge S.X₂ = charge S.X₁ + charge S.X₃
  /-- Every nonzero object has charge in the allowed half-plane. -/
  nonzero_mem : ∀ E : A, ¬IsZero E → charge E ∈ semiClosedUpperHalfPlane

namespace StabilityFunction

variable {A}

@[ext]
theorem ext {Z W : StabilityFunction A} (hcharge : Z.charge = W.charge) : Z = W := by
  cases Z
  cases W
  simp_all only

/-- The phase of an object, normalized to lie in `(0, 1]` when the object is
nonzero.  The phase of a zero object is `0`. -/
def phase (Z : StabilityFunction A) (E : A) : ℝ :=
  arg (Z.charge E) / Real.pi

theorem phase_pos (Z : StabilityFunction A) (E : A) (hE : ¬IsZero E) :
    0 < Z.phase E := by
  exact div_pos
    (arg_pos_of_mem_semiClosedUpperHalfPlane (Z.nonzero_mem E hE))
    Real.pi_pos

theorem phase_le_one (Z : StabilityFunction A) (E : A) : Z.phase E ≤ 1 := by
  exact div_le_one_of_le₀ (arg_le_pi (Z.charge E)) Real.pi_pos.le

theorem phase_mem_Ioc (Z : StabilityFunction A) (E : A) (hE : ¬IsZero E) :
    Z.phase E ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨Z.phase_pos E hE, Z.phase_le_one E⟩

/-- A nonzero object is semistable when no nonzero subobject has larger
phase. -/
def IsSemistable (Z : StabilityFunction A) (E : A) : Prop :=
  ¬IsZero E ∧ ∀ B : Subobject E, ¬IsZero (B : A) →
    Z.phase (B : A) ≤ Z.phase E

/-- A nonzero object is stable when every nonzero proper subobject has strictly
smaller phase. -/
def IsStable (Z : StabilityFunction A) (E : A) : Prop :=
  ¬IsZero E ∧ ∀ B : Subobject E, ¬IsZero (B : A) → B ≠ ⊤ →
    Z.phase (B : A) < Z.phase E

theorem exists_destabilizing_of_not_semistable (Z : StabilityFunction A)
    (E : A) (hE : ¬IsZero E) (h : ¬Z.IsSemistable E) :
    ∃ B : Subobject E, ¬IsZero (B : A) ∧ Z.phase E < Z.phase (B : A) := by
  simp only [IsSemistable, not_and_or, not_forall, not_le, exists_prop] at h
  rcases h with h | ⟨B, hB, hphase⟩
  · exact absurd hE h
  · exact ⟨B, hB, hphase⟩

theorem charge_eq_of_iso (Z : StabilityFunction A) {E F : A} (e : E ≅ F) :
    Z.charge E = Z.charge F :=
  Z.map_iso e

theorem phase_eq_of_iso (Z : StabilityFunction A) {E F : A} (e : E ≅ F) :
    Z.phase E = Z.phase F := by
  simp only [phase, Z.charge_eq_of_iso e]

theorem isSemistable_of_iso (Z : StabilityFunction A) {E F : A}
    (e : E ≅ F) (h : Z.IsSemistable E) : Z.IsSemistable F := by
  refine ⟨fun hF => h.1 (hF.of_iso e), fun B hB => ?_⟩
  let B' : Subobject E := Subobject.mk (B.arrow ≫ e.inv)
  have hB' : ¬IsZero (B' : A) := by
    intro hzero
    exact hB (hzero.of_iso (Subobject.underlyingIso (B.arrow ≫ e.inv)).symm)
  have hle := h.2 B' hB'
  rw [Z.phase_eq_of_iso (Subobject.underlyingIso (B.arrow ≫ e.inv))] at hle
  rwa [Z.phase_eq_of_iso e] at hle

theorem isSemistable_iff_of_iso (Z : StabilityFunction A) {E F : A}
    (e : E ≅ F) : Z.IsSemistable E ↔ Z.IsSemistable F :=
  ⟨Z.isSemistable_of_iso e, Z.isSemistable_of_iso e.symm⟩

end StabilityFunction

end CategoryTheory.Triangulated
