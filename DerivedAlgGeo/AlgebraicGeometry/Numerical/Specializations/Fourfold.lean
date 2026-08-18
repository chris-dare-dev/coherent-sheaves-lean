/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.General

/-!
# Display formulas for numerical fourfolds

The `n = 4` specialisation of `AlgebraicGeometry.Numerical.NumericalVarietyData.chi_eq_sum`,
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

open NumericalRingData NumericalVarietyData Finset

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData 4 A N)

/-- `χ(O_X)` for a fourfold, read off the top Todd component: taking `E` of rank one with
vanishing higher Chern components in `chi_eq` leaves exactly `∫_X td₄(X)`. -/
noncomputable abbrev chiStructureSheaf : ℚ := V.structureSheafEulerCharacteristic

/-- **Riemann–Roch for fourfolds.**

`χ(E) = rank(E) · ∫_X td₄(X) + ∫_X c₁(E)·td₃(X) + ∫_X ch₂(E)·td₂(X) + ∫_X ch₃(E)·td₁(X)
+ ∫_X ch₄(E)`. -/
theorem chi_eq (hV : V.SatisfiesHRR) (E : N) :
    (V.chi E : ℚ)
      = (V.rank E : ℚ) * V.ring.degree (V.toddComp 4)
        + V.ring.degree (V.chComp E 1 * V.toddComp 3)
        + V.ring.degree (V.chComp E 2 * V.toddComp 2)
        + V.ring.degree (V.chComp E 3 * V.toddComp 1)
        + V.ring.degree (V.chComp E 4) := by
  have h := V.chi_eq_sum hV E
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  simp only [show (4 : ℕ) - 0 = 4 from rfl, show (4 : ℕ) - 1 = 3 from rfl,
    show (4 : ℕ) - 2 = 2 from rfl, show (4 : ℕ) - 3 = 1 from rfl,
    show (4 : ℕ) - 4 = 0 from rfl] at h
  rw [h, V.chComp_zero, V.ring.degree_algebraMap_mul, V.toddComp_zero, mul_one]

end Fourfold

namespace CalabiYauFourfold

open NumericalRingData NumericalVarietyData

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N]
variable (V : NumericalVarietyData 4 A N)

/-- The numerical signature of a **Calabi–Yau fourfold**: trivial canonical class and
`χ(O_X) = 2`.

The three conditions are the odd Todd components vanishing — `td₁ = −K_X/2 = 0` and
`td₃ = c₁c₂/24 = 0`, both consequences of `c₁ = 0` — together with `∫_X td₄ = 2`, which is
`χ(O_X) = 1 − 0 + 0 − 0 + 1` for `h^{0,i}(X) = 1, 0, 0, 0, 1`.

The `2` is the one place a fourfold differs qualitatively from the threefold, where the
corresponding value is `0`: `χ` still sees the rank here, so unlike
`CalabiYauThreefold.chi_eq_of_chComp_eq` there is no rank-blindness statement to make. -/
structure IsCalabiYau : Prop where
  /-- `td₁(X) = −K_X/2 = 0`. -/
  toddComp_one : V.toddComp 1 = 0
  /-- `td₃(X) = c₁c₂/24 = 0`. -/
  toddComp_three : V.toddComp 3 = 0
  /-- `∫_X td₄(X) = χ(O_X) = 2`. -/
  degree_toddComp_four : V.ring.degree (V.toddComp 4) = 2

/-- **Riemann–Roch on a Calabi–Yau fourfold**:
`χ(E) = 2·rank(E) + ∫_X ch₂(E)·td₂(X) + ∫_X ch₄(E)`.

Two of the five terms of `Fourfold.chi_eq` vanish, both because an odd Todd component does;
the rank term survives with the coefficient `∫td₄ = 2`. -/
theorem chi_eq (hHRR : V.SatisfiesHRR) (hCY : IsCalabiYau V) (E : N) :
    (V.chi E : ℚ)
      = 2 * (V.rank E : ℚ)
        + V.ring.degree (V.chComp E 2 * V.toddComp 2)
        + V.ring.degree (V.chComp E 4) := by
  rw [Fourfold.chi_eq V hHRR E, hCY.toddComp_one, hCY.toddComp_three,
    hCY.degree_toddComp_four]
  simp only [mul_zero, map_zero]
  ring

end CalabiYauFourfold

end AlgebraicGeometry.Numerical
