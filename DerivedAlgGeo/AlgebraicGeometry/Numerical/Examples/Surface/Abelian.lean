/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Examples.Surface.K3
import DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface

/-!
# A polarised abelian surface

The third surface model, and the degenerate one: on an abelian surface `c₁ = c₂ = 0`, so

`td(A) = 1 + 0 + 0`

and Riemann–Roch collapses to `χ(E) = ∫_A ch₂(E)`. Both other terms of `Surface.chi_eq`
vanish, and they vanish for different reasons than on a K3 — there `∫td₂ = 2` keeps the rank
term alive, here it is `0`.

That makes this the surface model where `χ` sees neither the rank nor `c₁`, which is the
two-dimensional shadow of `CalabiYauThreefold.chi_eq_of_chComp_eq`. It is worth having for
exactly that reason: a Bridgeland central charge normalised against `χ` degenerates here in
a way it does not on a K3, and a statement that silently assumed `∫td₂ ≠ 0` would pass on
both other surface models.

`A` carries a polarisation `H` of type `(1, d)`, so `∫_A H² = 2d`. The evenness is not a
convention: Riemann–Roch on this very model gives `χ(H) = ∫ch₂(H) = H²/2`, an integer.

## Chern-character coordinates

These are the same as the K3's — a class `(r, c, s)` has `ch = r + c·H + s·H²` in the basis
`1, H, H²` — so `k3ChCoeff` is reused rather than copied. That is the design
`Examples/Surface/RankOne.lean` states outright: within Picard rank one, a new model costs a
Todd class and nothing else.

`s` ranging over `ℤ` makes `N` the sublattice of classes whose `ch₂` is an integer multiple
of `H²`, which is a genuine restriction — `O(mH)` has `ch₂ = (m²/2)H²` and so lies in it
only for even `m`. The K3 model carries the same restriction and for the same reason; where
a model needs the full lattice it must reparametrise, as `Examples/Surface/ProjectivePlane.lean`
does.

## Main definitions

* `abelianNumericalVariety` — the model.

## Main results

* `abelianChiStructureSheaf` — `∫_A td₂ = χ(O_A) = 0`.
* `abelianToddComp_one` — `td₁ = 0`, i.e. the canonical class is trivial.
* `abelianChi_eq_of_chComp_two_eq` — `χ` is blind to the rank and to `c₁`.
-/

open Polynomial Submodule Set

namespace AlgebraicGeometry.Numerical

namespace Examples

/-- The Todd class of an abelian surface: `c₁ = c₂ = 0`, so every component above `td₀`
vanishes. -/
noncomputable def abelianTodd : ℕ → SurfaceRing
  | 0 => 1
  | _ + 1 => 0

theorem abelianTodd_mem (i : ℕ) :
    abelianTodd i ∈ gradedPiece (⇑surfacePB.basis) surfaceW i := by
  match i with
  | 0 => exact surface_one_mem
  | _ + 1 => exact Submodule.zero_mem _

theorem abelianTodd_sum :
    (∑ j ∈ Finset.range (2 + 1), abelianTodd j)
      = 1 + algebraMap ℚ SurfaceRing 0 * H + algebraMap ℚ SurfaceRing 0 * H ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  simp [abelianTodd]

/-- **The model.** An abelian surface with a polarisation of type `(1, d)`, so `∫_A H² = 2d`,
and trivial Todd class. -/
@[reducible]
noncomputable def abelianNumericalVariety (d : ℕ) :
    NumericalVariety 2 SurfaceRing SurfaceNum where
  toNumericalRing := surfaceNumericalRing (2 * (d : ℚ))
  rank := { toFun := fun E => E.1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  chComp := surfaceCh k3ChCoeff
  chComp_mem := surfaceCh_mem k3ChCoeff
  chComp_zero := fun _ => rfl
  chComp_add := surfaceCh_add k3ChCoeff k3ChCoeff_add
  toddComp := abelianTodd
  toddComp_mem := abelianTodd_mem
  toddComp_zero := rfl
  chi :=
    { toFun := fun E => 2 * (d : ℤ) * E.2.2
      map_zero' := by simp
      map_add' := by intro a b; show 2 * (d : ℤ) * (a.2.2 + b.2.2) = _; ring }
  hirzebruch_riemannRoch := by
    intro E
    show ((2 * (d : ℤ) * E.2.2 : ℤ) : ℚ) = surfaceDegree (2 * (d : ℚ)) _
    rw [surfaceCh_sum, abelianTodd_sum, surfaceDegree_ch_mul_todd]
    show _ = 2 * (d : ℚ) * ((E.1 : ℚ) * 0 + (E.2.1 : ℚ) * 0 + (E.2.2 : ℚ))
    push_cast
    ring

/-- `td₁ = 0`: the canonical class of an abelian surface is trivial. -/
theorem abelianToddComp_one (d : ℕ) :
    letI := abelianNumericalVariety d
    NumericalVariety.toddComp (A := SurfaceRing) (N := SurfaceNum) 1 = 0 := rfl

/-- `∫_A td₂ = χ(O_A) = 0`. Together with `abelianToddComp_one` this is the abelian-surface
analogue of `k3_isK3`, stated as two theorems because — unlike K3s and Calabi–Yau
threefolds — abelian surfaces have no class in this library to inhabit. -/
theorem abelianChiStructureSheaf (d : ℕ) :
    letI := abelianNumericalVariety d
    Surface.chiStructureSheaf SurfaceRing SurfaceNum = 0 := by
  letI := abelianNumericalVariety d
  show surfaceDegree (2 * (d : ℚ)) (abelianTodd 2) = 0
  show surfaceDegree (2 * (d : ℚ)) 0 = 0
  rw [map_zero]

/-- On an abelian surface `χ` sees neither the rank nor `c₁`: two classes agreeing in
codimension two have the same Euler characteristic, however their ranks and first Chern
classes differ.

This is the two-dimensional shadow of `CalabiYauThreefold.chi_eq_of_chComp_eq`, and it is
the reason to carry this model alongside the K3: on a K3 the rank term survives with
coefficient `∫td₂ = 2`, so the same statement is false there. -/
theorem abelianChi_eq_of_chComp_two_eq (d : ℕ) (E F : SurfaceNum) (h : E.2.2 = F.2.2) :
    letI := abelianNumericalVariety d
    NumericalVariety.chi (A := SurfaceRing) E = NumericalVariety.chi (A := SurfaceRing) F := by
  letI := abelianNumericalVariety d
  show 2 * (d : ℤ) * E.2.2 = 2 * (d : ℤ) * F.2.2
  rw [h]

end Examples

end AlgebraicGeometry.Numerical
