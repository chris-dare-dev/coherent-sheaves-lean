/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.Discriminant

/-!
# K3 surfaces, numerically

A K3 surface is a smooth projective surface with trivial canonical bundle and no first
cohomology. Numerically that is exactly two conditions on the Todd class:

* `td₁(X) = −K_X/2 = 0`;
* `∫_X td₂(X) = χ(O_X) = 2`.

`IsK3` asserts those two and nothing else, so every consequence below is a consequence of
*those two facts about the Todd class*, not of anything else one knows about K3 surfaces.

## Main results

* `chi_eq` — `χ(E) = 2·rank(E) + ∫_X ch₂(E)`.
* `mukaiSelfPairing_eq` — `⟨v(E), v(E)⟩ = ∫_X Δ(E) − 2·rank(E)²`, relating the Mukai
  self-pairing to the Bogomolov–Gieseker discriminant.

The second identity is what makes the Mukai lattice and the discriminant two views of one
object: `v² ≥ −2` (the condition for a moduli space to be nonempty) and `∫Δ ≥ 0`
(Bogomolov) differ by exactly `2r²`.

## Not proved here

That the axioms have a K3 *model*: a concrete `NumericalVariety 2 A N` with
`A = ℚ[t]/(t³)`, `∫t² = 2d`, satisfying `IsK3`. Only the dimension-zero witness in
`Numerical/Examples/Point.lean` exists so far, so the statements below are conditional on a
`NumericalVariety 2 A N` existing at all. Building that model is the next task; it needs the
internality of the grading, i.e. linear independence of `1, t, t²`.
-/

universe u v

namespace AlgebraicGeometry.Numerical

namespace K3

open NumericalRing NumericalVariety Finset

variable {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety 2 A N]

/-- The numerical signature of a K3 surface: trivial canonical class and `χ(O_X) = 2`. -/
class IsK3 (A : Type u) (N : Type v) [CommRing A] [Algebra ℚ A] [AddCommGroup N]
    [NumericalVariety 2 A N] : Prop where
  /-- `td₁(X) = −K_X/2 = 0`. -/
  toddComp_one : toddComp (A := A) (N := N) 1 = 0
  /-- `∫_X td₂(X) = χ(O_X) = 2`. -/
  degree_toddComp_two : degree (n := 2) (toddComp (A := A) (N := N) 2) = 2

variable [IsK3 A N]

/-- **Riemann–Roch on a K3 surface**: `χ(E) = 2·rank(E) + ∫_X ch₂(E)`.

The `c₁`-term of the surface formula drops out because `td₁ = 0`; this is the whole of what
triviality of the canonical class buys. -/
theorem chi_eq (E : N) :
    (chi (A := A) E : ℚ) = 2 * (rank (A := A) E : ℚ) + degree (n := 2) (chComp (A := A) E 2) := by
  have h := chi_eq_sum (A := A) E
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add] at h
  simp only [show (2 : ℕ) - 0 = 2 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
    show (2 : ℕ) - 2 = 0 from rfl] at h
  rw [h, chComp_zero, degree_algebraMap_mul, toddComp_zero, mul_one,
    IsK3.toddComp_one, IsK3.degree_toddComp_two, mul_zero, map_zero]
  ring

/-- The third component of the Mukai vector `v(E) = (r, c₁, s)`, integrated:
`s = rank(E) + ∫_X ch₂(E)`.

For a K3, `v(E) = ch(E)·√td(X)` with `√td(X) = 1 + [pt]`, so the top component of `v` is
`ch₂(E) + rank(E)·[pt]`; `mukaiS` is its degree. -/
noncomputable def mukaiS (E : N) : ℚ :=
  (rank (A := A) E : ℚ) + degree (n := 2) (chComp (A := A) E 2)

/-- Riemann–Roch in Mukai coordinates: `χ(E) = r + s`. -/
theorem chi_eq_rank_add_mukaiS (E : N) :
    (chi (A := A) E : ℚ) = (rank (A := A) E : ℚ) + mukaiS (A := A) E := by
  rw [chi_eq E, mukaiS]
  ring

/-- The Mukai self-pairing `⟨v(E), v(E)⟩ = c₁² − 2rs`. -/
noncomputable def mukaiSelfPairing (E : N) : ℚ :=
  degree (n := 2) (chComp (A := A) E 1 * chComp (A := A) E 1)
    - 2 * (rank (A := A) E : ℚ) * mukaiS (A := A) E

omit [IsK3 A N] in
/-- **The Mukai pairing and the Bogomolov–Gieseker discriminant differ by `2r²`**:

`⟨v(E), v(E)⟩ = ∫_X Δ(E) − 2·rank(E)²`.

So `v² ≥ −2` and `∫Δ ≥ 0` are statements about the same quantity, shifted.

`IsK3` is `omit`ted deliberately: this identity is arithmetic relating two definitions and
holds on *any* surface. Only the reading of `(r, c₁, s)` as a Mukai vector is K3-specific. -/
theorem mukaiSelfPairing_eq (E : N) :
    mukaiSelfPairing (A := A) E
      = degree (n := 2) (discriminant (A := A) E) - 2 * (rank (A := A) E : ℚ) ^ 2 := by
  rw [mukaiSelfPairing, mukaiS, degree_discriminant]
  ring

omit [IsK3 A N] in
/-- A rank-zero object has `⟨v, v⟩ = ∫_X c₁²`. Also independent of `IsK3`. -/
theorem mukaiSelfPairing_of_rank_eq_zero (E : N) (hE : rank (A := A) E = 0) :
    mukaiSelfPairing (A := A) E
      = degree (n := 2) (chComp (A := A) E 1 * chComp (A := A) E 1) := by
  rw [mukaiSelfPairing, hE]
  push_cast
  ring

end K3

end AlgebraicGeometry.Numerical
