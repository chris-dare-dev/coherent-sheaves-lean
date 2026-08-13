/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Deformation.DeformedPredicate

/-!
# Phase control inside an owner deformed interval

The stability-seminorm estimate controls the perturbed phase of every old
semistable factor.  This module specializes that estimate to the midpoint
branch used by owner skewed stability data and records the interval forms
needed by phase-confinement and HN-assembly arguments.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ENNReal

universe u v u'

namespace BridgelandStabLean.Foundation

open Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

/-- Thinness places every phase in `(a,b)` inside the midpoint branch used by
the owner skewed stability function. -/
theorem midpoint_branch_contains {a b φ ε : ℝ}
    (haφ : a < φ) (hφb : φ < b) (hε : 0 < ε)
    (hthin : b - a + 2 * ε < 1) :
    φ ∈ Set.Ioo ((a + b) / 2 - 1 / 2) ((a + b) / 2 + 1 / 2) := by
  constructor <;> linarith

namespace StabilityCondition.WithClassMap

/-- Every old nonzero semistable factor in a thin witness interval has its
perturbed phase within `ε` of its old phase. -/
theorem skewedPhase_sub_lt_of_stabilitySeminorm
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b φ ε : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (haφ : a < φ) (hφb : φ < b) :
    |(skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E - φ| < ε := by
  apply relativePhase_perturbation_of_stabilitySeminorm C σ W hP hE
  · exact midpoint_branch_contains haφ hφb hε hthin
  · exact hε
  · exact hε2
  · exact hsin

/-- Interval form of the owner factor phase-control estimate. -/
theorem skewedPhase_mem_interval_of_stabilitySeminorm
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b φ ε : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (haφ : a < φ) (hφb : φ < b) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E ∈
      Set.Ioo (φ - ε) (φ + ε) := by
  have h := σ.skewedPhase_sub_lt_of_stabilitySeminorm C W hr0 hr1 hW hab
    hε hε2 hthin hsin hP hE haφ hφb
  rw [abs_lt] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The thin-witness factor phase lies in the common branch based at the
lower endpoint. -/
theorem skewedPhase_mem_lower_branch
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b φ ε : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (haφ : a < φ) (hφb : φ < b) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E ∈
      Set.Ioo (a - ε) (a - ε + 1) := by
  have hphase := σ.skewedPhase_mem_interval_of_stabilitySeminorm C W hr0 hr1 hW
    hab hε hε2 hthin hsin hP hE haφ hφb
  rcases hphase with ⟨hlo, hhi⟩
  constructor <;> linarith

/-- The thin-witness factor phase lies in the common branch based at the
upper endpoint. -/
theorem skewedPhase_mem_upper_branch
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b φ ε : ℝ} (hab : a < b) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthin : b - a + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E : C} (hP : σ.slicing.P φ E) (hE : ¬IsZero E)
    (haφ : a < φ) (hφb : φ < b) :
    (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).phase E ∈
      Set.Ioo (b + ε - 1) (b + ε) := by
  have hphase := σ.skewedPhase_mem_interval_of_stabilitySeminorm C W hr0 hr1 hW
    hab hε hε2 hthin hsin hP hE haφ hφb
  rcases hphase with ⟨hlo, hhi⟩
  constructor <;> linarith

end StabilityCondition.WithClassMap

end BridgelandStabLean.Foundation
