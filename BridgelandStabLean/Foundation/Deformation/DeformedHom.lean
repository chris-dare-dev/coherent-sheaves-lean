/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Deformation.DeformedTriangulated
import BridgelandStabLean.Foundation.Deformation.MidpointHeart

/-!
# Hom-vanishing preparations for owner deformed slices

This module separates the formal interval-orthogonality part of sharp
deformed Hom-vanishing from the phase-confinement and midpoint-heart image
arguments which supply its hypotheses.
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

/-- Objects intrinsically confined to radius `ε` around phases separated by
more than `2ε` have no morphisms from the larger phase to the smaller one. -/
theorem hom_eq_zero_of_intrinsic_deformed_gap
    (σ : StabilityCondition.WithClassMap C κ)
    {E F : C} {ψ₁ ψ₂ ε : ℝ}
    (hE : ¬IsZero E) (hF : ¬IsZero F)
    (hElo : ψ₁ - ε < σ.slicing.phiMinus C E hE)
    (hEhi : σ.slicing.phiPlus C E hE < ψ₁ + ε)
    (hFlo : ψ₂ - ε < σ.slicing.phiMinus C F hF)
    (hFhi : σ.slicing.phiPlus C F hF < ψ₂ + ε)
    (hgap : ψ₂ + 2 * ε < ψ₁) (f : E ⟶ F) : f = 0 := by
  let δ := (ψ₁ - ψ₂ - 2 * ε) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hEI : σ.slicing.intervalProp C (ψ₁ - ε - δ) (ψ₁ + ε + δ) E :=
    σ.slicing.intervalProp_of_intrinsic_phases C hE
      (by linarith) (by linarith)
  have hFI : σ.slicing.intervalProp C (ψ₂ - ε - δ) (ψ₂ + ε + δ) F :=
    σ.slicing.intervalProp_of_intrinsic_phases C hF
      (by linarith) (by linarith)
  exact σ.slicing.intervalHom_eq_zero C hEI hFI (by dsimp [δ]; linarith) f

/-- Large-gap Hom-vanishing for owner deformed predicates once the phase
confinement estimates for their nonzero witnesses are available. -/
theorem hom_eq_zero_of_deformedPred_large_gap
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ₁ ψ₂ : ℝ} {E F : C}
    (hE : σ.deformedPred C W hr0 hr1 hW ε ψ₁ E)
    (hF : σ.deformedPred C W hr0 hr1 hW ε ψ₂ F)
    (hconf : ∀ {X : C} {ψ : ℝ}
      (_ : σ.deformedPred C W hr0 hr1 hW ε ψ X)
      (hX : ¬IsZero X),
      ψ - ε < σ.slicing.phiMinus C X hX ∧
        σ.slicing.phiPlus C X hX < ψ + ε)
    (hgap : ψ₂ + 2 * ε < ψ₁) (f : E ⟶ F) : f = 0 := by
  by_cases hEZ : IsZero E
  · exact hEZ.eq_of_src f 0
  by_cases hFZ : IsZero F
  · exact hFZ.eq_of_tgt f 0
  exact σ.hom_eq_zero_of_intrinsic_deformed_gap C hEZ hFZ
    (hconf hE hEZ).1 (hconf hE hEZ).2
    (hconf hF hFZ).1 (hconf hF hFZ).2 hgap f

end StabilityCondition.WithClassMap

end BridgelandStabLean.Foundation
