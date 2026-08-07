/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Numerical.Defs

/-!
# Extracting the top-codimension part of `ch(E) · td(X)`

`hirzebruch_riemannRoch` states `χ(E) = ∫_X ch(E) · td(X)` with both factors written as
sums over all codimensions. Every dimension-specific Riemann–Roch formula is obtained by
expanding that product and discarding the terms whose total codimension is not `n`.

`degree_ch_mul_todd` does that once, in arbitrary dimension. The surface, threefold and
fourfold formulas are then finite specialisations of a single identity rather than three
separate computations — which is the point of stating Layer A for general `n`.
-/

universe u v

namespace AlgebraicGeometry.Numerical

namespace NumericalVariety

open NumericalRing Finset

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety n A N]

/-- **The Riemann–Roch expansion.** Integrating `ch(E) · td(X)` leaves exactly the
`n + 1` terms of total codimension `n`:

`∫_X ch(E) · td(X) = Σ_{i=0}^{n} ∫_X chᵢ(E) · td_{n-i}(X)`. -/
theorem degree_ch_mul_todd (E : N) :
    degree (n := n) (ch (A := A) E * todd n A (N := N))
      = ∑ i ∈ range (n + 1),
          degree (n := n) (chComp (A := A) E i * toddComp (N := N) (n - i)) := by
  simp only [ch, todd]
  rw [Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [map_sum]
  refine Finset.sum_eq_single (n - i) (fun b _ hb => ?_) (fun hmem => ?_)
  · refine degree_chComp_mul_toddComp_eq_zero E fun hib => hb ?_
    omega
  · exact absurd (Finset.mem_range.mpr (by omega)) hmem

/-- Riemann–Roch with the product already expanded:
`χ(E) = Σ_{i=0}^{n} ∫_X chᵢ(E) · td_{n-i}(X)`. -/
theorem chi_eq_sum (E : N) :
    (chi (A := A) E : ℚ)
      = ∑ i ∈ range (n + 1),
          degree (n := n) (chComp (A := A) E i * toddComp (N := N) (n - i)) := by
  rw [hrr E, degree_ch_mul_todd]

end NumericalVariety

end AlgebraicGeometry.Numerical
