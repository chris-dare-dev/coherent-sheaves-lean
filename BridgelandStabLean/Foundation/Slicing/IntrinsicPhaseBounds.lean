/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Slicing.IntrinsicPhases

/-!
# Intrinsic phase bounds and interval membership

This module characterizes owner interval membership using intrinsic highest
and lowest phases.  It also supplies the interval-widening operations used by
the deformed-slicing construction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace BridgelandStabLean.Foundation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- Enlarging both endpoints preserves owner interval membership. -/
theorem Slicing.intervalProp_mono (s : Slicing C) {a₁ a₂ b₁ b₂ : ℝ}
    (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    s.intervalProp C a₁ b₁ ≤ s.intervalProp C a₂ b₂ := by
  intro E hE
  rcases hE with hE | ⟨F, hF⟩
  · exact Or.inl hE
  · exact Or.inr ⟨F, fun i => ⟨ha.trans_lt (hF i).1, (hF i).2.trans_le hb⟩⟩

/-- A radius increase widens a centered owner interval. -/
theorem Slicing.intervalProp_widen (s : Slicing C) {E : C} {φ ε δ : ℝ}
    (hE : s.intervalProp C (φ - ε) (φ + ε) E) (hεδ : ε ≤ δ) :
    s.intervalProp C (φ - δ) (φ + δ) E :=
  s.intervalProp_mono C (by linarith) (by linarith) E hE

/-- Interval membership bounds the intrinsic highest phase from above. -/
theorem Slicing.phiPlus_lt_of_intervalProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ} (hI : s.intervalProp C a b E) :
    s.phiPlus C E hE < b := by
  rcases hI with hzero | ⟨F, hF⟩
  · exact (hE hzero).elim
  · have hn : 0 < F.n := F.n_pos C hE
    obtain ⟨G, hG, hfirst⟩ := s.exists_hn_nonzero_first C hE
    calc
      s.phiPlus C E hE = G.phiPlus C hG := s.phiPlus_eq C E hE G hG hfirst
      _ ≤ F.phiPlus C hn := G.phiPlus_le_of_firstFactor_nonzero C s F hG hn hfirst
      _ < b := (hF ⟨0, hn⟩).2

/-- Interval membership bounds the intrinsic lowest phase from below. -/
theorem Slicing.phiMinus_gt_of_intervalProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ} (hI : s.intervalProp C a b E) :
    a < s.phiMinus C E hE := by
  rcases hI with hzero | ⟨F, hF⟩
  · exact (hE hzero).elim
  · have hn : 0 < F.n := F.n_pos C hE
    obtain ⟨G, hG, hlast⟩ := s.exists_hn_nonzero_last C hE
    calc
      a < F.phiMinus C hn := (hF ⟨F.n - 1, by omega⟩).1
      _ ≤ G.phiMinus C hG := F.phiMinus_le_of_lastFactor_nonzero C s G hn hG hlast
      _ = s.phiMinus C E hE := (s.phiMinus_eq C E hE G hG hlast).symm

/-- Interval membership bounds the intrinsic highest phase from below. -/
theorem Slicing.phiPlus_gt_of_intervalProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ} (hI : s.intervalProp C a b E) :
    a < s.phiPlus C E hE :=
  (s.phiMinus_gt_of_intervalProp C hE hI).trans_le
    (s.phiMinus_le_phiPlus C E hE)

/-- Interval membership bounds the intrinsic lowest phase from above. -/
theorem Slicing.phiMinus_lt_of_intervalProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ} (hI : s.intervalProp C a b E) :
    s.phiMinus C E hE < b :=
  (s.phiMinus_le_phiPlus C E hE).trans_lt
    (s.phiPlus_lt_of_intervalProp C hE hI)

/-- Intrinsic phase bounds imply owner interval membership. -/
theorem Slicing.intervalProp_of_intrinsic_phases (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ}
    (hminus : a < s.phiMinus C E hE) (hplus : s.phiPlus C E hE < b) :
    s.intervalProp C a b E := by
  obtain ⟨F, hn, hFplus, hFminus⟩ := s.exists_hn_intrinsic_width C hE
  refine Or.inr ⟨F, fun i => ⟨?_, ?_⟩⟩
  · calc
      a < s.phiMinus C E hE := hminus
      _ = F.phiMinus C hn := hFminus.symm
      _ ≤ F.φ i := (F.phase_mem_range C hn i).1
  · calc
      F.φ i ≤ F.phiPlus C hn := (F.phase_mem_range C hn i).2
      _ = s.phiPlus C E hE := hFplus
      _ < b := hplus

/-- For a nonzero object, owner interval membership is equivalent to bounds
on both intrinsic phase extrema. -/
theorem Slicing.intervalProp_iff_intrinsic_phases (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ} :
    s.intervalProp C a b E ↔
      a < s.phiMinus C E hE ∧ s.phiPlus C E hE < b := by
  constructor
  · intro hI
    exact ⟨s.phiMinus_gt_of_intervalProp C hE hI,
      s.phiPlus_lt_of_intervalProp C hE hI⟩
  · rintro ⟨hminus, hplus⟩
    exact s.intervalProp_of_intrinsic_phases C hE hminus hplus

/-- All four intrinsic extrema of a nonzero interval object lie between the
interval endpoints. -/
theorem Slicing.intrinsic_phases_mem_interval (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a b : ℝ} (hI : s.intervalProp C a b E) :
    a < s.phiPlus C E hE ∧ s.phiPlus C E hE < b ∧
      a < s.phiMinus C E hE ∧ s.phiMinus C E hE < b :=
  ⟨s.phiPlus_gt_of_intervalProp C hE hI,
    s.phiPlus_lt_of_intervalProp C hE hI,
    s.phiMinus_gt_of_intervalProp C hE hI,
    s.phiMinus_lt_of_intervalProp C hE hI⟩

/-- A strict bound on the intrinsic lowest phase yields the corresponding
strict lower phase cut. -/
theorem Slicing.gtProp_of_phiMinus_gt (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a : ℝ} (h : a < s.phiMinus C E hE) :
    s.gtProp C a E := by
  obtain ⟨F, hn, _, hminus⟩ := s.exists_hn_intrinsic_width C hE
  exact Or.inr ⟨F, hn, by rw [hminus]; exact h⟩

/-- A weak bound on the intrinsic lowest phase yields the corresponding weak
lower phase cut. -/
theorem Slicing.geProp_of_phiMinus_ge (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a : ℝ} (h : a ≤ s.phiMinus C E hE) :
    s.geProp C a E := by
  obtain ⟨F, hn, _, hminus⟩ := s.exists_hn_intrinsic_width C hE
  exact Or.inr ⟨F, hn, by rw [hminus]; exact h⟩

/-- A weak bound on the intrinsic highest phase yields the corresponding weak
upper phase cut. -/
theorem Slicing.leProp_of_phiPlus_le (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {b : ℝ} (h : s.phiPlus C E hE ≤ b) :
    s.leProp C b E := by
  obtain ⟨F, hn, hplus, _⟩ := s.exists_hn_intrinsic_width C hE
  exact Or.inr ⟨F, hn, by rw [hplus]; exact h⟩

/-- A strict bound on the intrinsic highest phase yields the corresponding
strict upper phase cut. -/
theorem Slicing.ltProp_of_phiPlus_lt (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {b : ℝ} (h : s.phiPlus C E hE < b) :
    s.ltProp C b E := by
  obtain ⟨F, hn, hplus, _⟩ := s.exists_hn_intrinsic_width C hE
  exact Or.inr ⟨F, hn, by rw [hplus]; exact h⟩

end BridgelandStabLean.Foundation
