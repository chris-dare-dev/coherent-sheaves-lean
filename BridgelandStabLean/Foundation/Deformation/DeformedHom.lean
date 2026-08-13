/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Deformation.DeformedTriangulated
import BridgelandStabLean.Foundation.Deformation.MidpointHeart
import BridgelandStabLean.Foundation.Deformation.PhaseConfinement

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
    (hElo : ψ₁ - ε ≤ σ.slicing.phiMinus C E hE)
    (hEhi : σ.slicing.phiPlus C E hE ≤ ψ₁ + ε)
    (hFlo : ψ₂ - ε ≤ σ.slicing.phiMinus C F hF)
    (hFhi : σ.slicing.phiPlus C F hF ≤ ψ₂ + ε)
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

/-- Large-gap Hom-vanishing for owner deformed predicates from weak intrinsic
phase confinement. -/
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
      ψ - ε ≤ σ.slicing.phiMinus C X hX ∧
        σ.slicing.phiPlus C X hX ≤ ψ + ε)
    (hgap : ψ₂ + 2 * ε < ψ₁) (f : E ⟶ F) : f = 0 := by
  by_cases hEZ : IsZero E
  · exact hEZ.eq_of_src f 0
  by_cases hFZ : IsZero F
  · exact hFZ.eq_of_tgt f 0
  exact σ.hom_eq_zero_of_intrinsic_deformed_gap C hEZ hFZ
    (hconf hE hEZ).1 (hconf hE hEZ).2
    (hconf hF hFZ).1 (hconf hF hFZ).2 hgap f

/-- Owner deformed slices separated by more than twice the deformation radius
are Hom-orthogonal. -/
theorem hom_eq_zero_of_deformedPred_gap
    [IsTriangulated C]
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε ψ₁ ψ₂ : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    {E F : C}
    (hE : σ.deformedPred C W hr0 hr1 hW ε ψ₁ E)
    (hF : σ.deformedPred C W hr0 hr1 hW ε ψ₂ F)
    (hgap : ψ₂ + 2 * ε < ψ₁) (f : E ⟶ F) : f = 0 := by
  apply σ.hom_eq_zero_of_deformedPred_large_gap C W hr0 hr1 hW hE hF
  · intro X ψ hX hXne
    obtain ⟨a, b, hab, hthin, haψ, hψb, hSS⟩ :=
      σ.exists_deformedPred_witness C W hr0 hr1 hW hX hXne
    exact ⟨σ.skewed_phiMinus_ge C W hr0 hr1 hW hab hε hε2 hthin hsin
        haψ hψb hSS,
      σ.skewed_phiPlus_le C W hr0 hr1 hW hab hε hε2 hthin hsin
        haψ hψb hSS⟩
  · exact hgap

/-- Extension-closed owner deformed cuts are Hom-orthogonal once their cutoffs
are separated by twice the deformation radius. -/
theorem hom_eq_zero_of_deformedCuts_gap
    [IsTriangulated C]
    (σ : StabilityCondition.WithClassMap C κ)
    (W : Λ →+ ℂ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hW : stabilitySeminorm C σ (W - σ.Z) ≤ ENNReal.ofReal r)
    {ε t₁ t₂ : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hsin : stabilitySeminorm C σ (W - σ.Z) <
      ENNReal.ofReal (Real.sin (Real.pi * ε)))
    (hsep : t₂ + 2 * ε ≤ t₁) {E F : C}
    (hE : σ.deformedGtPred C W hr0 hr1 hW ε t₁ E)
    (hF : σ.deformedLePred C W hr0 hr1 hW ε t₂ F)
    (f : E ⟶ F) : f = 0 := by
  apply ExtensionClosure.hom_eq_zero _ hE hF f
  intro X Y hX hY
  obtain ⟨ψ₁, htψ, hPredX⟩ := hX
  obtain ⟨ψ₂, hψt, hPredY⟩ := hY
  exact σ.hom_eq_zero_of_deformedPred_gap C W hr0 hr1 hW hε hε2 hsin
    hPredX hPredY (by linarith)

end StabilityCondition.WithClassMap

end BridgelandStabLean.Foundation
