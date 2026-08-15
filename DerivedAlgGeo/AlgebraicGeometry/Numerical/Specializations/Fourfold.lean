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
* `CalabiYauFourfold.IsCalabiYau` — the numerical signature of a Calabi–Yau fourfold.
* `CalabiYauFourfold.chi_eq` — `χ(E) = 2·rank(E) + ∫ch₂(E)·td₂(X) + ∫ch₄(E)` on such a
  fourfold.

Models live in `Numerical/Examples/Fourfold/`: `ℙ⁴`, whose Todd class has no vanishing
component, and the sextic Calabi–Yau, which inhabits `CalabiYauFourfold.IsCalabiYau`.

## Not proved here

Hyperkähler fourfolds — the case the Bridgeland side would want next — are *not* given a
class here. Unlike `K3.IsK3`, `CalabiYauThreefold.IsCalabiYau` and `IsCalabiYau` below,
their numerical signature is not a few conditions on the Todd class: the Fujiki relations
constrain the whole intersection form, and asserting a fragment of that as a class field
would hide a real theorem the way the module docstring of `Numerical/Core/Definitions.lean`
forbids.
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

namespace CalabiYauFourfold

open NumericalRing NumericalVariety

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety 4 A N]

/-- The numerical signature of a **Calabi–Yau fourfold**: trivial canonical class and
`χ(O_X) = 2`.

The three conditions are the odd Todd components vanishing — `td₁ = −K_X/2 = 0` and
`td₃ = c₁c₂/24 = 0`, both consequences of `c₁ = 0` — together with `∫_X td₄ = 2`, which is
`χ(O_X) = 1 − 0 + 0 − 0 + 1` for `h^{0,i}(X) = 1, 0, 0, 0, 1`.

The `2` is the one place a fourfold differs qualitatively from the threefold, where the
corresponding value is `0`: `χ` still sees the rank here, so unlike
`CalabiYauThreefold.chi_eq_of_chComp_eq` there is no rank-blindness statement to make. -/
class IsCalabiYau (A : Type u) (N : Type v) [CommRing A] [Algebra ℚ A] [AddCommGroup N]
    [NumericalVariety 4 A N] : Prop where
  /-- `td₁(X) = −K_X/2 = 0`. -/
  toddComp_one : toddComp (A := A) (N := N) 1 = 0
  /-- `td₃(X) = c₁c₂/24 = 0`. -/
  toddComp_three : toddComp (A := A) (N := N) 3 = 0
  /-- `∫_X td₄(X) = χ(O_X) = 2`. -/
  degree_toddComp_four : degree (n := 4) (toddComp (A := A) (N := N) 4) = 2

variable [IsCalabiYau A N]

/-- **Riemann–Roch on a Calabi–Yau fourfold**:
`χ(E) = 2·rank(E) + ∫_X ch₂(E)·td₂(X) + ∫_X ch₄(E)`.

Two of the five terms of `Fourfold.chi_eq` vanish, both because an odd Todd component does;
the rank term survives with the coefficient `∫td₄ = 2`. -/
theorem chi_eq (E : N) :
    (chi (A := A) E : ℚ)
      = 2 * (rank (A := A) E : ℚ)
        + degree (n := 4) (chComp (A := A) E 2 * toddComp (N := N) 2)
        + degree (n := 4) (chComp (A := A) E 4) := by
  rw [Fourfold.chi_eq E, IsCalabiYau.toddComp_one, IsCalabiYau.toddComp_three,
    IsCalabiYau.degree_toddComp_four]
  simp only [mul_zero, map_zero]
  ring

end CalabiYauFourfold

end AlgebraicGeometry.Numerical
