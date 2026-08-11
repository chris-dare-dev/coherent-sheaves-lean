/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Numerical.RiemannRoch.General

/-!
# The numerical discriminant in arbitrary dimension

The Bogomolov discriminant is built from the first two components of the Chern character,
so its definition does not depend on the dimension of the ambient variety. Surface geometry
is where its degree enters the Bogomolov--Gieseker inequality, but the class itself belongs
to the dimension-general numerical API.
-/

universe u v

namespace AlgebraicGeometry.Numerical

namespace NumericalVariety

open NumericalRing

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety n A N]

/-- The numerical discriminant `Δ(E) = ch₁(E)² - 2 rank(E) ch₂(E)`.

It is defined for a numerical variety of any dimension. When `n < 2`, its membership in the
second graded piece forces it to vanish; when `n = 2`, its degree is the quantity appearing
in the Bogomolov--Gieseker inequality. -/
noncomputable def discriminant (E : N) : A :=
  chComp (A := A) E 1 * chComp (A := A) E 1
    - algebraMap ℚ A (2 * (rank (A := A) E : ℚ)) * chComp (A := A) E 2

/-- The discriminant lives in codimension two, independently of the ambient dimension. -/
theorem discriminant_mem_piece_two (E : N) :
    discriminant (A := A) E ∈ piece (n := n) 2 := by
  refine Submodule.sub_mem _ ?_ ?_
  · exact mul_mem_piece (chComp_mem E 1) (chComp_mem E 1)
  · exact mul_mem_piece (algebraMap_mem_piece_zero _) (chComp_mem E 2)

/-- Integrating the discriminant pulls its scalar coefficient outside the degree map. -/
theorem degree_discriminant (E : N) :
    degree (n := n) (discriminant (A := A) E)
      = degree (n := n) (chComp (A := A) E 1 * chComp (A := A) E 1)
        - 2 * (rank (A := A) E : ℚ) * degree (n := n) (chComp (A := A) E 2) := by
  simp only [discriminant, map_sub, degree_algebraMap_mul]

end NumericalVariety

end AlgebraicGeometry.Numerical
