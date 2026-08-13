/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Deformation.DeformedPhaseControl

/-!
# Interval independence for owner deformed slices

The owner candidate slicing is defined using an existential thin old interval.
This module supplies the comparison lemmas that let later constructions replace
one interval witness by a compatible smaller witness without changing the
perturbed phase or semistability condition.
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

namespace StabilityCondition.WithClassMap

/-- A deformed-slice witness may be replaced by a compatible thin subinterval
that still envelops the recorded perturbed phase. -/
theorem deformedPred_rewitness_subinterval
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {a b c d ε ψ : ℝ} (hab : a < b) (hcd : c < d)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hthinSource : b - a + 2 * ε < 1)
    (hthinTarget : d - c + 2 * ε < 1)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hleft : (c + d) / 2 - 1 < a - ε)
    (hright : b + ε ≤ (c + d) / 2 + 1)
    (hcψ : c + ε ≤ ψ) (hψd : ψ ≤ d - ε)
    (hmono : σ.slicing.intervalProp C c d ≤ σ.slicing.intervalProp C a b)
    {E : C} (hI : σ.slicing.intervalProp C c d E)
    (hSS : (skewedStabilityFunctionOfSeminormLtOne C σ W hr0 hr1 hW hab).IsSemistable
      E ψ) :
    σ.deformedPred C W hr0 hr1 hW ε ψ E := by
  right
  exact ⟨c, d, hcd, hthinTarget, hcψ, hψd,
    σ.skewedSemistable_of_subinterval C W hr0 hr1 hW hab hcd hε hε2
      hthinSource hsin hleft hright hmono hI hSS⟩

end StabilityCondition.WithClassMap

end BridgelandStabLean.Foundation
