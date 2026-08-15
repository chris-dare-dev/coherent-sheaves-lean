/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.General

/-!
# Display formulas for numerical fourfolds

The `n = 4` specialisation of `AlgebraicGeometry.Numerical.NumericalVariety.chi_eq_sum`,
closing out the dimensions this repo targets.

This file is mechanical on purpose. It is the check that `degree_ch_mul_todd` really is
dimension-general: the `n = 2`, `n = 3` and `n = 4` files differ only in how many times
`Finset.sum_range_succ` fires and in which `n - i` reductions are handed to `simp`. Nothing
in Layer A was tuned to a dimension.

## Main results

* `Fourfold.chi_eq` —
  `χ(E) = r·∫td₄(X) + ∫c₁(E)·td₃(X) + ∫ch₂(E)·td₂(X) + ∫ch₃(E)·td₁(X) + ∫ch₄(E)`.

## Not proved here

No fourfold *model* exists in `Numerical/Examples/`, so the statement is conditional on a
`NumericalVariety 4 A N` existing at all. The rank-one analogue would be `ℚ[t]/(t⁵)` with
`∫t⁴ = d`, built the same way as `Examples/RankOneSurface.lean`.

Hyperkähler fourfolds — the case the Bridgeland side would want next — are *not* given a
class here. Unlike `K3.IsK3` and `CalabiYauThreefold.IsCalabiYau`, their numerical
signature is not two conditions on the Todd class: the Fujiki relations constrain the whole
intersection form, and asserting a fragment of that as a class field would hide a real
theorem the way the module docstring of `Numerical/Defs.lean` forbids.
-/

universe u v

namespace AlgebraicGeometry.Numerical

namespace Fourfold

open NumericalRing NumericalVariety Finset

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety 4 A N]

/-- `χ(O_X)` for a fourfold, read off the top Todd component: taking `E` of rank one with
vanishing higher Chern components in `chi_eq` leaves exactly `∫_X td₄(X)`. -/
noncomputable abbrev chiStructureSheaf (A : Type u) (N : Type v) [CommRing A] [Algebra ℚ A]
    [AddCommGroup N] [NumericalVariety 4 A N] : ℚ :=
  NumericalVariety.structureSheafEulerCharacteristic (n := 4) (A := A) (N := N)

/-- **Riemann–Roch for fourfolds.**

`χ(E) = rank(E) · ∫_X td₄(X) + ∫_X c₁(E)·td₃(X) + ∫_X ch₂(E)·td₂(X) + ∫_X ch₃(E)·td₁(X)
+ ∫_X ch₄(E)`. -/
theorem chi_eq (E : N) :
    (chi (A := A) E : ℚ)
      = (rank (A := A) E : ℚ) * degree (n := 4) (toddComp (A := A) (N := N) 4)
        + degree (n := 4) (chComp (A := A) E 1 * toddComp (N := N) 3)
        + degree (n := 4) (chComp (A := A) E 2 * toddComp (N := N) 2)
        + degree (n := 4) (chComp (A := A) E 3 * toddComp (N := N) 1)
        + degree (n := 4) (chComp (A := A) E 4) := by
  have h := chi_eq_sum (A := A) E
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  simp only [show (4 : ℕ) - 0 = 4 from rfl, show (4 : ℕ) - 1 = 3 from rfl,
    show (4 : ℕ) - 2 = 2 from rfl, show (4 : ℕ) - 3 = 1 from rfl,
    show (4 : ℕ) - 4 = 0 from rfl] at h
  rw [h, chComp_zero, degree_algebraMap_mul, toddComp_zero, mul_one]

end Fourfold

end AlgebraicGeometry.Numerical
