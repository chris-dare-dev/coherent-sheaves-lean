/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Slicing.PhaseCutClosure

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

/-- Membership in two owner intervals implies membership in their
intersection. -/
theorem Slicing.intervalProp_intersection (s : Slicing C) {E : C}
    {a b c d : ℝ} (hab : s.intervalProp C a b E)
    (hcd : s.intervalProp C c d E) :
    s.intervalProp C (max a c) (min b d) E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  · apply s.intervalProp_of_intrinsic_phases C hE
    · exact max_lt
        (s.phiMinus_gt_of_intervalProp C hE hab)
        (s.phiMinus_gt_of_intervalProp C hE hcd)
    · exact lt_min
        (s.phiPlus_lt_of_intervalProp C hE hab)
        (s.phiPlus_lt_of_intervalProp C hE hcd)

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

/-- Membership in a strict lower phase cut bounds the intrinsic lowest phase. -/
theorem Slicing.phiMinus_gt_of_gtProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a : ℝ} (h : s.gtProp C a E) :
    a < s.phiMinus C E hE := by
  rcases h with hzero | ⟨F, hn, hminus⟩
  · exact (hE hzero).elim
  · obtain ⟨G, hG, hlast⟩ := s.exists_hn_nonzero_last C hE
    calc
      a < F.phiMinus C hn := hminus
      _ ≤ G.phiMinus C hG :=
        F.phiMinus_le_of_lastFactor_nonzero C s G hn hG hlast
      _ = s.phiMinus C E hE := (s.phiMinus_eq C E hE G hG hlast).symm

/-- Membership in a weak lower phase cut bounds the intrinsic lowest phase. -/
theorem Slicing.phiMinus_ge_of_geProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {a : ℝ} (h : s.geProp C a E) :
    a ≤ s.phiMinus C E hE := by
  rcases h with hzero | ⟨F, hn, hminus⟩
  · exact (hE hzero).elim
  · obtain ⟨G, hG, hlast⟩ := s.exists_hn_nonzero_last C hE
    calc
      a ≤ F.phiMinus C hn := hminus
      _ ≤ G.phiMinus C hG :=
        F.phiMinus_le_of_lastFactor_nonzero C s G hn hG hlast
      _ = s.phiMinus C E hE := (s.phiMinus_eq C E hE G hG hlast).symm

/-- Membership in a weak upper phase cut bounds the intrinsic highest phase. -/
theorem Slicing.phiPlus_le_of_leProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {b : ℝ} (h : s.leProp C b E) :
    s.phiPlus C E hE ≤ b := by
  rcases h with hzero | ⟨F, hn, hplus⟩
  · exact (hE hzero).elim
  · obtain ⟨G, hG, hfirst⟩ := s.exists_hn_nonzero_first C hE
    calc
      s.phiPlus C E hE = G.phiPlus C hG :=
        s.phiPlus_eq C E hE G hG hfirst
      _ ≤ F.phiPlus C hn :=
        G.phiPlus_le_of_firstFactor_nonzero C s F hG hn hfirst
      _ ≤ b := hplus

/-- Membership in a strict upper phase cut bounds the intrinsic highest phase. -/
theorem Slicing.phiPlus_lt_of_ltProp (s : Slicing C) {E : C}
    (hE : ¬IsZero E) {b : ℝ} (h : s.ltProp C b E) :
    s.phiPlus C E hE < b := by
  rcases h with hzero | ⟨F, hn, hplus⟩
  · exact (hE hzero).elim
  · obtain ⟨G, hG, hfirst⟩ := s.exists_hn_nonzero_first C hE
    calc
      s.phiPlus C E hE = G.phiPlus C hG :=
        s.phiPlus_eq C E hE G hG hfirst
      _ ≤ F.phiPlus C hn :=
        G.phiPlus_le_of_firstFactor_nonzero C s F hG hn hfirst
      _ < b := hplus

/-- A weak upper phase bound becomes a strict upper phase bound after strictly
enlarging its endpoint. -/
theorem Slicing.ltProp_of_leProp_of_lt (s : Slicing C) {a b : ℝ}
    (hab : a < b) : s.leProp C a ≤ s.ltProp C b := by
  rintro E (hE | ⟨F, hF, hle⟩)
  · exact Or.inl hE
  · exact Or.inr ⟨F, hF, hle.trans_lt hab⟩

/-- In a distinguished triangle `K → E → Q → K[1]`, an upper phase bound
on `E` and a compatible weak upper bound on `Q` bound `K` from above. -/
theorem Slicing.phiPlus_lt_of_triangle_with_leProp (s : Slicing C)
    {K E Q : C} (hK : ¬IsZero K) {b : ℝ}
    (hE_lt : ∀ hE : ¬IsZero E, s.phiPlus C E hE < b)
    {c : ℝ} (hQ_le : s.leProp C c Q) (hcb : c < b + 1)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    s.phiPlus C K hK < b := by
  let T := Triangle.mk f₁ f₂ f₃
  have hE_upper : s.ltProp C b E := by
    by_cases hE : IsZero E
    · exact Or.inl hE
    · exact s.ltProp_of_phiPlus_lt C hE (hE_lt hE)
  have hQ_shift : s.leProp C (c + ((-1 : ℤ) : ℝ)) (Q⟦(-1 : ℤ)⟧) :=
    s.leProp_shift C c Q (-1) hQ_le
  have hQ_upper : s.ltProp C b (Q⟦(-1 : ℤ)⟧) :=
    s.ltProp_of_leProp_of_lt C (by push_cast; linarith) _ hQ_shift
  have hK_upper : s.ltProp C b K := by
    simpa [T] using s.ltProp_of_triangle C b hQ_upper hE_upper
      (inv_rot_of_distTriang T hT)
  exact s.phiPlus_lt_of_ltProp C hK hK_upper

/-- In a distinguished triangle `K → E → Q → K[1]`, a lower phase bound
on `E` and a compatible strict lower bound on `K` bound `Q` from below. -/
theorem Slicing.phiMinus_gt_of_triangle_with_gtProp (s : Slicing C)
    {K E Q : C} (hQ : ¬IsZero Q) {a : ℝ}
    (hE_gt : ∀ hE : ¬IsZero E, a < s.phiMinus C E hE)
    {c : ℝ} (hK_gt : s.gtProp C c K) (hca : a < c + 1)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    a < s.phiMinus C Q hQ := by
  let T := Triangle.mk f₁ f₂ f₃
  have hE_lower : s.gtProp C a E := by
    by_cases hE : IsZero E
    · exact Or.inl hE
    · exact s.gtProp_of_phiMinus_gt C hE (hE_gt hE)
  have hK_shift : s.gtProp C (c + ((1 : ℤ) : ℝ)) (K⟦(1 : ℤ)⟧) :=
    s.gtProp_shift C c K 1 hK_gt
  have hK_lower : s.gtProp C a (K⟦(1 : ℤ)⟧) :=
    s.gtProp_anti C (by push_cast; linarith) _ hK_shift
  have hQ_lower : s.gtProp C a Q := by
    simpa [T] using s.gtProp_of_triangle C a hE_lower hK_lower
      (rot_of_distTriang T hT)
  exact s.phiMinus_gt_of_gtProp C hQ hQ_lower

/-- The first vertex of a distinguished triangle stays in an open phase
interval when its middle vertex is in that interval and the first and third
vertices satisfy the one-sided bounds supplied by a common heart. -/
theorem Slicing.first_intervalProp_of_triangle (s : Slicing C)
    {a b : ℝ} (hab : a < b) {K E Q : C}
    (hE : s.intervalProp C a b E)
    (hQ_le : s.leProp C (a + 1) Q)
    (hK_gt : s.gtProp C a K)
    {f₁ : K ⟶ E} {f₂ : E ⟶ Q} {f₃ : Q ⟶ K⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang C) :
    s.intervalProp C a b K := by
  by_cases hK : IsZero K
  · exact Or.inl hK
  · apply s.intervalProp_of_intrinsic_phases C hK
    · exact s.phiMinus_gt_of_gtProp C hK hK_gt
    · exact s.phiPlus_lt_of_triangle_with_leProp C hK
        (fun hEne => s.phiPlus_lt_of_intervalProp C hEne hE)
        hQ_le (by linarith) hT

/-- The intersection of strict lower and upper owner cuts is the corresponding
open owner phase interval. -/
theorem Slicing.intervalProp_of_gtProp_ltProp (s : Slicing C) {E : C}
    {a b : ℝ} (hgt : s.gtProp C a E) (hlt : s.ltProp C b E) :
    s.intervalProp C a b E := by
  by_cases hE : IsZero E
  · exact Or.inl hE
  · exact s.intervalProp_of_intrinsic_phases C hE
      (s.phiMinus_gt_of_gtProp C hE hgt)
      (s.phiPlus_lt_of_ltProp C hE hlt)

end BridgelandStabLean.Foundation
