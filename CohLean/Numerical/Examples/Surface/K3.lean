/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Numerical.RiemannRoch.K3
import CohLean.Numerical.Examples.Surface.RankOne

/-!
# A K3 surface of Picard rank one

The first model of `NumericalVariety` in dimension two. Before it, every statement in
`CohLean/Numerical/Specializations/Surface.lean` and `CohLean/Numerical/K3.lean` was conditional on a
`NumericalVariety 2 A N` existing at all — only the dimension-zero point had been exhibited.

The surface is a K3 `X` with `Pic X = ℤ·H` and `H² = 2d`. The ring, grading and degree map
come from `Examples/RankOneSurface.lean`; all this file supplies is the Todd class

`td(X) = 1 + 0 + (1/d)·H²`,

so that `td₁ = 0` and `∫_X td₂ = 2` — which is exactly `K3.IsK3`, proved here rather than
assumed.

`d` is a parameter, not fixed to 1: the Bridgeland wall structure on a K3 depends on the
degree. It is a natural number rather than a rational because `χ` must land in `ℤ` —
Riemann–Roch on this model reads `χ(r, c, s) = 2r + 2ds`.
-/

open Polynomial Submodule Set

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- Chern-character coefficients: the class `(r, c, s)` has `ch = r + c·H + s·H²`. -/
noncomputable def k3ChCoeff (E : SurfaceNum) : ℕ → ℚ
  | 0 => (E.1 : ℚ)
  | 1 => (E.2.1 : ℚ)
  | 2 => (E.2.2 : ℚ)
  | _ + 3 => 0

theorem k3ChCoeff_add (E F : SurfaceNum) (i : ℕ) :
    k3ChCoeff (E + F) i = k3ChCoeff E i + k3ChCoeff F i := by
  match i with
  | 0 =>
    show ((E + F).1 : ℚ) = (E.1 : ℚ) + (F.1 : ℚ)
    rw [show ((E + F).1 : ℤ) = E.1 + F.1 from rfl, Int.cast_add]
  | 1 =>
    show ((E + F).2.1 : ℚ) = (E.2.1 : ℚ) + (F.2.1 : ℚ)
    rw [show ((E + F).2.1 : ℤ) = E.2.1 + F.2.1 from rfl, Int.cast_add]
  | 2 =>
    show ((E + F).2.2 : ℚ) = (E.2.2 : ℚ) + (F.2.2 : ℚ)
    rw [show ((E + F).2.2 : ℤ) = E.2.2 + F.2.2 from rfl, Int.cast_add]
  | _ + 3 => show (0 : ℚ) = 0 + 0; rw [add_zero]

/-- The Todd class of a K3: `td₁ = 0`, and `td₂` normalised so that `∫_X td₂ = 2`. -/
noncomputable def k3Todd (d : ℚ) : ℕ → SurfaceRing
  | 0 => 1
  | 1 => 0
  | 2 => algebraMap ℚ SurfaceRing (1 / d) * H ^ 2
  | _ + 3 => 0

theorem k3Todd_mem (d : ℚ) (i : ℕ) :
    k3Todd d i ∈ gradedPiece (⇑surfacePB.basis) surfaceW i := by
  match i with
  | 0 => exact surface_one_mem
  | 1 => exact Submodule.zero_mem _
  | 2 => exact algebraMap_mul_mem _ Hsq_mem_piece_two
  | _ + 3 => exact Submodule.zero_mem _

theorem k3Todd_sum (d : ℚ) :
    (∑ j ∈ Finset.range (2 + 1), k3Todd d j)
      = 1 + algebraMap ℚ SurfaceRing 0 * H + algebraMap ℚ SurfaceRing (1 / d) * H ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  simp [k3Todd]

/-- **The model.** A K3 surface of degree `H² = 2d`, `d > 0`. -/
@[reducible]
noncomputable def k3NumericalVariety (d : ℕ) (hd : d ≠ 0) :
    NumericalVariety 2 SurfaceRing SurfaceNum where
  toNumericalRing := surfaceNumericalRing (2 * (d : ℚ))
  rank := { toFun := fun E => E.1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  chComp := surfaceCh k3ChCoeff
  chComp_mem := surfaceCh_mem k3ChCoeff
  chComp_zero := fun _ => rfl
  chComp_add := surfaceCh_add k3ChCoeff k3ChCoeff_add
  toddComp := k3Todd (d : ℚ)
  toddComp_mem := k3Todd_mem (d : ℚ)
  toddComp_zero := rfl
  chi :=
    { toFun := fun E => 2 * E.1 + 2 * (d : ℤ) * E.2.2
      map_zero' := by simp
      map_add' := by intro a b; show 2 * (a.1 + b.1) + 2 * (d : ℤ) * (a.2.2 + b.2.2) = _; ring }
  hirzebruch_riemannRoch := by
    intro E
    show ((2 * E.1 + 2 * (d : ℤ) * E.2.2 : ℤ) : ℚ) = surfaceDegree (2 * (d : ℚ)) _
    rw [surfaceCh_sum, k3Todd_sum, surfaceDegree_ch_mul_todd]
    have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
    show _ = 2 * (d : ℚ) * ((E.1 : ℚ) * (1 / (d : ℚ)) + (E.2.1 : ℚ) * 0 + (E.2.2 : ℚ))
    push_cast
    field_simp
    ring

/-- The model really is a K3: `td₁ = 0` and `∫_X td₂ = χ(O_X) = 2`.

With this instance every theorem in `CohLean/Numerical/K3.lean` — Riemann–Roch, the Mukai
self-pairing, `⟨v,v⟩ = ∫Δ − 2r²` — is a statement about an object that exists. -/
theorem k3_isK3 (d : ℕ) (hd : d ≠ 0) :
    letI := k3NumericalVariety d hd
    K3.IsK3 SurfaceRing SurfaceNum := by
  -- the `letI` in the statement is zeta-reduced away, so re-establish the instance here
  letI := k3NumericalVariety d hd
  refine ⟨rfl, ?_⟩
  show surfaceDegree (2 * (d : ℚ)) (algebraMap ℚ SurfaceRing (1 / (d : ℚ)) * H ^ 2) = 2
  rw [surfaceDegree_algebraMap_mul, surfaceDegree_Hsq]
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  field_simp

end Examples

end AlgebraicGeometry.Numerical
