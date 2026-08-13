/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Deformation.PhaseArithmetic
import BridgelandStabLean.Foundation.Slicing.PhaseBounds
import BridgelandStabLean.Foundation.TriangulatedGrothendieck

/-!
# Rotated charge sums along owner filtrations

Rotated imaginary parts are additive along owner Postnikov towers.  Strict
signs on all nonzero HN factors therefore give a strict sign on the ambient
object as soon as one factor is known to be nonzero.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace BridgelandStabLean.Foundation

open Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

/-- Rotated imaginary part of a perturbed charge decomposes over an owner
Postnikov tower. -/
theorem rotatedIm_charge_eq_sum (W : Λ →+ ℂ) {E : C}
    (P : PostnikovTower C E) (ψ : ℝ) :
    rotatedIm (W (classOf C κ E)) ψ =
      ∑ i : Fin P.n, rotatedIm (W (classOf C κ (P.factor i))) ψ := by
  rw [classOf_postnikovTower_eq_sum C κ P, map_sum]
  unfold rotatedIm
  rw [Finset.sum_mul]
  exact map_sum Complex.imAddGroupHom _ _

/-- If all nonzero HN factors have negative rotated charge and the first
factor is nonzero, then the ambient charge has negative rotated part. -/
theorem rotatedIm_charge_neg_of_hn (W : Λ →+ ℂ)
    {P : ℝ → ObjectProperty C} {E : C} (F : HNFiltration C P E)
    (hn : 0 < F.n) (hfirst : ¬IsZero (F.factor ⟨0, hn⟩)) (ψ : ℝ)
    (hneg : ∀ i : Fin F.n, ¬IsZero (F.factor i) →
      rotatedIm (W (classOf C κ (F.factor i))) ψ < 0) :
    rotatedIm (W (classOf C κ E)) ψ < 0 := by
  rw [rotatedIm_charge_eq_sum C W F.toPostnikovTower ψ]
  suffices h : 0 < ∑ i : Fin F.n,
      -rotatedIm (W (classOf C κ (F.factor i))) ψ by
    linarith [Finset.sum_neg_distrib (G := ℝ) (s := Finset.univ)
      (f := fun i => rotatedIm (W (classOf C κ (F.factor i))) ψ)]
  apply lt_of_lt_of_le (neg_pos.mpr (hneg ⟨0, hn⟩ hfirst))
  apply Finset.single_le_sum
    (f := fun i => -rotatedIm (W (classOf C κ (F.factor i))) ψ)
  · intro i _
    by_cases hi : IsZero (F.factor i)
    · simp [classOf_isZero C κ hi, rotatedIm]
    · exact (neg_pos.mpr (hneg i hi)).le
  · exact Finset.mem_univ _

/-- If all nonzero HN factors have positive rotated charge and the first
factor is nonzero, then the ambient charge has positive rotated part. -/
theorem rotatedIm_charge_pos_of_hn (W : Λ →+ ℂ)
    {P : ℝ → ObjectProperty C} {E : C} (F : HNFiltration C P E)
    (hn : 0 < F.n) (hfirst : ¬IsZero (F.factor ⟨0, hn⟩)) (ψ : ℝ)
    (hpos : ∀ i : Fin F.n, ¬IsZero (F.factor i) →
      0 < rotatedIm (W (classOf C κ (F.factor i))) ψ) :
    0 < rotatedIm (W (classOf C κ E)) ψ := by
  rw [rotatedIm_charge_eq_sum C W F.toPostnikovTower ψ]
  apply lt_of_lt_of_le (hpos ⟨0, hn⟩ hfirst)
  apply Finset.single_le_sum
    (f := fun i => rotatedIm (W (classOf C κ (F.factor i))) ψ)
  · intro i _
    by_cases hi : IsZero (F.factor i)
    · simp [classOf_isZero C κ hi, rotatedIm]
    · exact (hpos i hi).le
  · exact Finset.mem_univ _

end BridgelandStabLean.Foundation
