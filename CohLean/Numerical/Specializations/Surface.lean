/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import CohLean.Numerical.GrothendieckGroup.Discriminant

/-!
# Display formulas for numerical surfaces

The `n = 2` specialisation of `AlgebraicGeometry.Numerical.NumericalVariety.chi_eq_sum`.

This is an optional display specialization of the dimension-general API. It contains no
foundational surface object: `NumericalVariety 2 A N` is the general variety interface at
dimension two, and the discriminant itself now lives in
`Numerical/GrothendieckGroup/Discriminant.lean` for
arbitrary dimension.

## Main results

* `chi_eq` — `χ(E) = r·∫td₂(X) + ∫c₁(E)·td₁(X) + ∫ch₂(E)`.
* compatibility aliases for the dimension-general numerical discriminant.

Writing `td₁(X) = −K_X/2` and `ch₂(E) = (c₁² − 2c₂)/2` turns `chi_eq` into the classical
`χ(E) = r·χ(O_X) + ½c₁(c₁ − K_X) − c₂`. Those substitutions need `K_X` and `c₂`, which are
Layer B objects, so they are *not* asserted here.
-/

universe u v

namespace AlgebraicGeometry.Numerical

namespace Surface

open NumericalRing NumericalVariety Finset

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety 2 A N]

/-- `χ(O_X)` for a surface, read off the top Todd component: taking `E` of rank one with
vanishing higher Chern components in `chi_eq` leaves exactly `∫_X td₂(X)`. -/
noncomputable abbrev chiStructureSheaf (A : Type u) (N : Type v) [CommRing A] [Algebra ℚ A]
    [AddCommGroup N] [NumericalVariety 2 A N] : ℚ :=
  NumericalVariety.structureSheafEulerCharacteristic (n := 2) (A := A) (N := N)

/-- **Riemann–Roch for surfaces.**

`χ(E) = rank(E) · ∫_X td₂(X) + ∫_X c₁(E)·td₁(X) + ∫_X ch₂(E)`. -/
theorem chi_eq (E : N) :
    (chi (A := A) E : ℚ)
      = (rank (A := A) E : ℚ) * degree (n := 2) (toddComp (A := A) (N := N) 2)
        + degree (n := 2) (chComp (A := A) E 1 * toddComp (N := N) 1)
        + degree (n := 2) (chComp (A := A) E 2) := by
  have h := chi_eq_sum (A := A) E
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add] at h
  simp only [show (2 : ℕ) - 0 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
    show (2 : ℕ) - 2 = 0 from rfl] at h
  rw [h, chComp_zero, degree_algebraMap_mul, toddComp_zero, mul_one]

/-- The **Bogomolov–Gieseker discriminant** `Δ(E) = c₁(E)² − 2·rank(E)·ch₂(E)`, a class in
codimension two.

Equivalently `Δ(E) = 2·r·c₂(E) − (r − 1)·c₁(E)²` once `c₂` is available; the `ch`-form is
used here because `c₂` is a Layer B object. Bogomolov's inequality — `∫_X Δ(E) ≥ 0` for
`E` slope-semistable with respect to a polarisation — is *not* stated at this layer: there
is no stability notion in `NumericalVariety`, and asserting it here would hide a real
theorem behind a class field. -/
noncomputable abbrev discriminant (E : N) : A :=
  NumericalVariety.discriminant (A := A) E

/-- The discriminant lives in codimension two. -/
theorem discriminant_mem_piece_two (E : N) :
    discriminant (A := A) E ∈ piece (n := 2) 2 := by
  exact NumericalVariety.discriminant_mem_piece_two (A := A) E

/-- `∫_X Δ(E) = ∫_X c₁(E)² − 2·rank(E)·∫_X ch₂(E)`: the scalar the
Bogomolov–Gieseker inequality is about. -/
theorem degree_discriminant (E : N) :
    degree (n := 2) (discriminant (A := A) E)
      = degree (n := 2) (chComp (A := A) E 1 * chComp (A := A) E 1)
        - 2 * (rank (A := A) E : ℚ) * degree (n := 2) (chComp (A := A) E 2) := by
  exact NumericalVariety.degree_discriminant (A := A) E

end Surface

end AlgebraicGeometry.Numerical
