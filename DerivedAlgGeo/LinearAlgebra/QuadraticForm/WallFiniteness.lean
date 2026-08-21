/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.PeriodDomain
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Finitely many spherical walls pass through a point of the period domain

`PeriodDomain.neg_of_mem_orthogonal` makes `Q` negative definite on `Wᗮ` for
every positive plane `W` of a space of signature `(2, n - 2)`. This file spends
that definiteness: a definite form has bounded level sets, a lattice meets a
bounded set finitely, and the spherical classes orthogonal to `W` are exactly
the walls through `W`.

## Main results

* `QuadraticMap.PosDef.exists_pos_mul_norm_sq_le` — a positive definite form on
  a finite-dimensional real normed space is coercive: `c * ‖x‖ ^ 2 ≤ Q x` for
  some `c > 0`. The pinned Mathlib has no such lemma; it is proved here from
  compactness of the unit sphere, and the constant is returned rather than
  hidden because the region-wise statement will need it.
* `QuadraticMap.PosDef.isBounded_setOf_eq` — hence bounded level sets.
* `PeriodDomain.finite_sphericalOrthogonal_inter` — **for a lattice `Λ`, only
  finitely many spherical classes of `Λ` are orthogonal to a given positive
  plane**, i.e. `finite_walls_through`: finitely many spherical walls pass
  through a point of the period domain.

## What is *not* proved here, and why it is not an oversight

The region-wise statement — finitely many walls meet a *family* of positive
planes — does not follow. The coercivity constant of `-Q` on `Wᗮ` depends on
`W` and degrades to `0` as the plane approaches the boundary of the
positive-plane locus, so a bounded family of planes does not by itself supply a
uniform constant. This is one of the two gaps in Bridgeland's own §11 argument.
The other chart already answers it the honest way: `Walls/Spherical/Finiteness.lean`
makes `coercivity` an explicit field of `BoundedRegion` rather than deriving it.
A region-wise route (A) statement must do the same, and is deliberately left to
its own change.

Everything below is about an arbitrary real quadratic space and its lattices;
`Λ` is the `ℤ`-span of an `ℝ`-basis and is **not** asserted to be `N(X)`, in the
discipline of `LinearAlgebra/Lattice/Mukai/Basic.lean`.
-/

open Bornology QuadraticMap

namespace QuadraticMap

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]

/-- A quadratic form on a finite-dimensional real normed space is continuous:
it is the diagonal of its polar form, which is a linear map into the operator
space and so continuous, composed with the (bounded bilinear) evaluation. -/
theorem continuous_of_finiteDimensional (Q : QuadraticForm ℝ M) : Continuous ⇑Q := by
  set f : M →ₗ[ℝ] (M →L[ℝ] ℝ) :=
    (LinearMap.toContinuousLinearMap : (M →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (M →L[ℝ] ℝ)).toLinearMap.comp
      Q.polarBilin with hf
  have hcont : Continuous fun x : M => (f x) x :=
    isBoundedBilinearMap_apply.continuous.comp
      ((LinearMap.continuous_of_finiteDimensional f).prodMk continuous_id)
  have hEq : (fun x : M => ((f x) x) / 2) = ⇑Q := by
    funext x
    have hx : (f x) x = Q x + Q x := by
      have hpolar : (f x) x = polar (⇑Q) x x := rfl
      rw [hpolar, polar_self, two_nsmul]
    rw [hx]; ring
  rw [← hEq]
  exact hcont.div_const 2

/-- **A positive definite form on a finite-dimensional real space is coercive.**

The minimum of `Q` on the unit sphere is attained and positive, and every vector
is a positive multiple of a unit vector. Not in Mathlib at the pin. -/
theorem PosDef.exists_pos_mul_norm_sq_le {Q : QuadraticForm ℝ M} (hQ : Q.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : M, c * ‖x‖ ^ 2 ≤ Q x := by
  rcases subsingleton_or_nontrivial M with _ | _
  · refine ⟨1, one_pos, fun x => ?_⟩
    rw [Subsingleton.elim x 0]
    simp
  · obtain ⟨x₀, hx₀, hmin⟩ :=
      (isCompact_sphere (0 : M) 1).exists_isMinOn (NormedSpace.sphere_nonempty.mpr zero_le_one)
        (continuous_of_finiteDimensional Q).continuousOn
    have hx₀0 : x₀ ≠ 0 := by
      intro h
      rw [mem_sphere_iff_norm, sub_zero, h, norm_zero] at hx₀
      exact zero_ne_one hx₀
    refine ⟨Q x₀, hQ x₀ hx₀0, fun x => ?_⟩
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hnx : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
      have hmem : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : M) 1 := by
        rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, norm_norm]
        field_simp
      have hkey : Q x₀ ≤ (‖x‖⁻¹ * ‖x‖⁻¹) * Q x := by
        have h := isMinOn_iff.mp hmin _ hmem
        rwa [QuadraticMap.map_smul, smul_eq_mul] at h
      have h2 := mul_le_mul_of_nonneg_right hkey (sq_nonneg ‖x‖)
      rwa [show (‖x‖⁻¹ * ‖x‖⁻¹) * Q x * ‖x‖ ^ 2 = Q x by field_simp] at h2

/-- A positive definite form has bounded level sets. -/
theorem PosDef.isBounded_setOf_eq {Q : QuadraticForm ℝ M} (hQ : Q.PosDef) (r : ℝ) :
    IsBounded {x : M | Q x = r} := by
  obtain ⟨c, hc, hle⟩ := hQ.exists_pos_mul_norm_sq_le
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Real.sqrt (r / c), fun x hx => ?_⟩
  have h := hle x
  rw [Set.mem_setOf_eq] at hx
  rw [hx] at h
  have hr : 0 ≤ r := le_trans (mul_nonneg hc.le (sq_nonneg _)) h
  have hsq : ‖x‖ ^ 2 ≤ r / c := by
    rw [le_div_iff₀ hc]
    linarith
  exact (Real.le_sqrt (norm_nonneg x) (div_nonneg hr hc.le)).mpr hsq

end QuadraticMap

namespace PeriodDomain

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [FiniteDimensional ℝ M]
variable {Q : QuadraticForm ℝ M} {W : Submodule ℝ M}

/-- The spherical classes orthogonal to `W`. By `mem_wall_iff_mem_orthogonal`
these are exactly the classes whose wall passes through `W`. -/
def sphericalOrthogonal (Q : QuadraticForm ℝ M) (W : Submodule ℝ M) : Set M :=
  {δ | IsSphericalClass Q δ ∧ δ ∈ orthogonal Q W}

/-- **The spherical classes orthogonal to a positive plane form a bounded set.**

`Q` is negative definite on `Wᗮ`, so `-Q` is a positive definite form there and
`-Q δ = 1` confines `δ` to a level set, which is bounded. -/
theorem isBounded_sphericalOrthogonal (hsig : HasSignatureTwo Q)
    (hW : IsPositivePlane Q W) : IsBounded (sphericalOrthogonal Q W) := by
  obtain ⟨c, hc, hle⟩ := (negDef_orthogonal hsig hW).exists_pos_mul_norm_sq_le
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Real.sqrt (1 / c), ?_⟩
  rintro δ ⟨hsph, hmem⟩
  have h := hle ⟨δ, hmem⟩
  have hval : ((-Q).restrict (orthogonal Q W)) ⟨δ, hmem⟩ = 1 := by
    rw [restrict_apply]
    simp [isSphericalClass_iff_apply.mp hsph]
  rw [hval] at h
  have hnorm : ‖(⟨δ, hmem⟩ : orthogonal Q W)‖ = ‖δ‖ := rfl
  rw [hnorm] at h
  have hsq : ‖δ‖ ^ 2 ≤ 1 / c := by
    rw [le_div_iff₀ hc]
    linarith
  exact (Real.le_sqrt (norm_nonneg δ) (by positivity)).mpr hsq

/-- **Only finitely many spherical classes of a lattice are orthogonal to a
given positive plane.**

Bounded by `isBounded_sphericalOrthogonal`, and a lattice meets a bounded set
finitely. `Λ` is the `ℤ`-span of an `ℝ`-basis; nothing identifies it with a
geometric lattice. -/
theorem finite_sphericalOrthogonal_inter (hsig : HasSignatureTwo Q)
    (hW : IsPositivePlane Q W) {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ M) :
    (sphericalOrthogonal Q W ∩ (Submodule.span ℤ (Set.range b) : Set M)).Finite :=
  ZSpan.setFinite_inter b (isBounded_sphericalOrthogonal hsig hW)

/-- **Finitely many spherical walls pass through a point of the period domain.**

The same statement as `finite_sphericalOrthogonal_inter`, said in walls: this is
what a local-finiteness argument for route (A) starts from, and the pointwise
case is unconditional where the region-wise case is not. -/
theorem finite_walls_through (hsig : HasSignatureTwo Q) (hW : IsPositivePlane Q W)
    {ι : Type*} [Finite ι] (b : Module.Basis ι ℝ M) :
    {δ : M | IsSphericalClass Q δ ∧ W ∈ wall Q δ ∧
      δ ∈ (Submodule.span ℤ (Set.range b) : Set M)}.Finite := by
  refine Set.Finite.subset (finite_sphericalOrthogonal_inter hsig hW b) ?_
  rintro δ ⟨hsph, hwall, hlat⟩
  exact ⟨⟨hsph, (mem_wall_iff_mem_orthogonal hW).mp hwall⟩, hlat⟩

end PeriodDomain
