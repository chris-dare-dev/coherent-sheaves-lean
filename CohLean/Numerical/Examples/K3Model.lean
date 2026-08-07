/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Numerical.K3
import CohLean.Numerical.OfGradedBasis
import Mathlib.RingTheory.AdjoinRoot

/-!
# A K3 surface of Picard rank one

The first model of `NumericalVariety` in dimension two. Until this file, every statement in
`CohLean/Numerical/Surface.lean` and `CohLean/Numerical/K3.lean` was conditional on a
`NumericalVariety 2 A N` existing at all — only the dimension-zero point had been exhibited.

The model is a K3 surface `X` with `Pic X = ℤ·H` and `H² = 2d`:

* intersection ring `A = ℚ[t]/(t³)`, realised as `AdjoinRoot (X³)`, with `t = H`;
* degree map normalised so that `∫_X H² = 2d`;
* `N(X) = ℤ³`, an object `(r, c, s)` having `ch = r + c·H + s·H²`;
* `td(X) = 1 + 0 + (1/d)·H²`, so `td₁ = 0` and `∫_X td₂ = 2`, which is exactly `IsK3`.

`d` is a parameter throughout, not fixed to 1: the Bridgeland wall structure on a K3 depends
on the degree, so a model that only knew `H² = 2` would be the wrong thing to have built.
-/

open Polynomial Submodule Set

namespace AlgebraicGeometry.Numerical

namespace Examples

/-! ### The intersection ring `ℚ[t]/(t³)` -/

/-- The defining relation: nothing survives in codimension three on a surface. -/
noncomputable def k3Rel : ℚ[X] := X ^ 3

theorem k3Rel_ne_zero : k3Rel ≠ 0 :=
  pow_ne_zero 3 Polynomial.X_ne_zero

/-- The numerical intersection ring `A^•(X)_ℚ = ℚ[t]/(t³)` of a Picard-rank-one surface. -/
abbrev K3Ring : Type := AdjoinRoot k3Rel

/-- The power basis `1, H, H²`. -/
noncomputable def k3PB : PowerBasis ℚ K3Ring := AdjoinRoot.powerBasis k3Rel_ne_zero

theorem k3PB_dim : k3PB.dim = 3 := by
  rw [k3PB, AdjoinRoot.powerBasis_dim, k3Rel, Polynomial.natDegree_X_pow]

/-- The ample generator of the Picard group. -/
noncomputable def H : K3Ring := AdjoinRoot.root k3Rel

theorem k3PB_gen : k3PB.gen = H := AdjoinRoot.powerBasis_gen _

theorem k3PB_basis_apply (i : Fin k3PB.dim) : k3PB.basis i = H ^ (i : ℕ) := by
  rw [k3PB.basis_eq_pow, k3PB_gen]

/-- `H³ = 0`: the relation, in the ring. -/
theorem H_pow_three : H ^ 3 = 0 := by
  have h := AdjoinRoot.eval₂_root k3Rel
  simpa [k3Rel, H] using h

/-- The codimension of `Hⁱ` is `i`. -/
def k3W : Fin k3PB.dim → ℕ := fun i => (i : ℕ)

-- `k3PB.dim` cannot be rewritten inside a hypothesis mentioning `i : Fin k3PB.dim` — the
-- motive does not typecheck. Feed the equation to `omega` as a fact about naturals instead.
theorem k3W_le (i : Fin k3PB.dim) : k3W i ≤ 2 := by
  have h := i.isLt
  have hd := k3PB_dim
  show (i : ℕ) ≤ 2
  omega

theorem two_lt_dim : (2 : ℕ) < k3PB.dim := by rw [k3PB_dim]; norm_num

/-- The index of `H²`, the top graded piece. -/
def idx2 : Fin k3PB.dim := ⟨2, two_lt_dim⟩

theorem k3_one_mem : (1 : K3Ring) ∈ gradedPiece (⇑k3PB.basis) k3W 0 := by
  have h0 : (0 : ℕ) < k3PB.dim := by rw [k3PB_dim]; norm_num
  have hb : k3PB.basis ⟨0, h0⟩ = 1 := by rw [k3PB_basis_apply]; simp
  have hmem := mem_gradedPiece (b := ⇑k3PB.basis) (w := k3W) ⟨0, h0⟩
  rwa [hb] at hmem

theorem k3_mul_mem (p q : Fin k3PB.dim) :
    k3PB.basis p * k3PB.basis q ∈ gradedPiece (⇑k3PB.basis) k3W (k3W p + k3W q) := by
  rw [k3PB_basis_apply, k3PB_basis_apply, ← pow_add]
  by_cases hpq : (p : ℕ) + (q : ℕ) < k3PB.dim
  · have hmem := mem_gradedPiece (b := ⇑k3PB.basis) (w := k3W) ⟨(p : ℕ) + (q : ℕ), hpq⟩
    rwa [k3PB_basis_apply] at hmem
  · have hd := k3PB_dim
    have h3 : 3 ≤ (p : ℕ) + (q : ℕ) := by omega
    have hzero : H ^ ((p : ℕ) + (q : ℕ)) = 0 := by
      obtain ⟨m, hm⟩ : ∃ m, (p : ℕ) + (q : ℕ) = 3 + m := ⟨(p : ℕ) + (q : ℕ) - 3, by omega⟩
      rw [hm, pow_add, H_pow_three, zero_mul]
    rw [hzero]
    exact Submodule.zero_mem _

/-- `∫_X`, normalised so that `∫_X H² = 2d`. -/
noncomputable def k3Degree (d : ℚ) : K3Ring →ₗ[ℚ] ℚ := (2 * d) • k3PB.basis.coord idx2

-- `simp` is the wrong tool here: `PowerBasis.coe_basis` fires first and turns `basis i` into
-- `gen ^ i`, after which `Basis.repr_self` no longer matches. Rewrite by hand.
theorem k3Degree_basis_of_ne (d : ℚ) (i : Fin k3PB.dim) (hi : k3W i ≠ 2) :
    k3Degree d (k3PB.basis i) = 0 := by
  have hne : i ≠ idx2 := fun h => hi (by rw [h]; rfl)
  show ((2 * d) • k3PB.basis.coord idx2) (k3PB.basis i) = 0
  rw [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
  simp [hne]

/-- `∫_X H² = 2d`: the degree of the surface. -/
theorem k3Degree_basis_two (d : ℚ) : k3Degree d (k3PB.basis idx2) = 2 * d := by
  show ((2 * d) • k3PB.basis.coord idx2) (k3PB.basis idx2) = 2 * d
  rw [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
  simp

/-- The numerical intersection ring of a K3 of degree `2d`. -/
@[reducible]
noncomputable def k3NumericalRing (d : ℚ) : NumericalRing 2 K3Ring :=
  NumericalRing.ofGradedBasis 2 k3PB.basis k3W k3W_le k3_one_mem k3_mul_mem
    (k3Degree d) (k3Degree_basis_of_ne d)

/-! ### Where the classes live -/

theorem H_mem_piece_one : H ∈ gradedPiece (⇑k3PB.basis) k3W 1 := by
  have h1 : (1 : ℕ) < k3PB.dim := by rw [k3PB_dim]; norm_num
  have hb : k3PB.basis ⟨1, h1⟩ = H := by rw [k3PB_basis_apply]; simp
  have hmem := mem_gradedPiece (b := ⇑k3PB.basis) (w := k3W) ⟨1, h1⟩
  rwa [hb] at hmem

theorem Hsq_mem_piece_two : H ^ 2 ∈ gradedPiece (⇑k3PB.basis) k3W 2 := by
  have hb : k3PB.basis idx2 = H ^ 2 := by rw [k3PB_basis_apply]; rfl
  have hmem := mem_gradedPiece (b := ⇑k3PB.basis) (w := k3W) idx2
  rwa [hb] at hmem

theorem algebraMap_mul_mem {i : ℕ} {x : K3Ring} (q : ℚ)
    (hx : x ∈ gradedPiece (⇑k3PB.basis) k3W i) :
    algebraMap ℚ K3Ring q * x ∈ gradedPiece (⇑k3PB.basis) k3W i := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hx

/-! ### The degree map on the normal form -/

theorem k3Degree_one (d : ℚ) : k3Degree d 1 = 0 := by
  have h0 : (0 : ℕ) < k3PB.dim := by rw [k3PB_dim]; norm_num
  have hb : k3PB.basis ⟨0, h0⟩ = 1 := by rw [k3PB_basis_apply]; simp
  rw [← hb]
  exact k3Degree_basis_of_ne d _ (by show (0 : ℕ) ≠ 2; decide)

theorem k3Degree_H (d : ℚ) : k3Degree d H = 0 := by
  have h1 : (1 : ℕ) < k3PB.dim := by rw [k3PB_dim]; norm_num
  have hb : k3PB.basis ⟨1, h1⟩ = H := by rw [k3PB_basis_apply]; simp
  rw [← hb]
  exact k3Degree_basis_of_ne d _ (by show (1 : ℕ) ≠ 2; decide)

theorem k3Degree_Hsq (d : ℚ) : k3Degree d (H ^ 2) = 2 * d := by
  have hb : k3PB.basis idx2 = H ^ 2 := by rw [k3PB_basis_apply]; rfl
  rw [← hb]
  exact k3Degree_basis_two d

theorem k3Degree_algebraMap_mul (d q : ℚ) (x : K3Ring) :
    k3Degree d (algebraMap ℚ K3Ring q * x) = q * k3Degree d x := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- `∫_X` on the normal form `a + b·H + c·H²`. Only the top coefficient survives. -/
theorem k3Degree_normalForm (d a b c : ℚ) :
    k3Degree d (algebraMap ℚ K3Ring a + algebraMap ℚ K3Ring b * H
      + algebraMap ℚ K3Ring c * H ^ 2) = 2 * d * c := by
  rw [map_add, map_add, k3Degree_algebraMap_mul, k3Degree_algebraMap_mul, k3Degree_H,
    k3Degree_Hsq, mul_zero, add_zero]
  rw [show algebraMap ℚ K3Ring a = algebraMap ℚ K3Ring a * 1 by rw [mul_one],
    k3Degree_algebraMap_mul, k3Degree_one, mul_zero, zero_add]
  ring

/-! ### The numerical Grothendieck group and the variety -/

/-- `N(X) = ℤ³`: the class `(r, c, s)` has `ch = r + c·H + s·H²`. -/
abbrev K3Num : Type := ℤ × ℤ × ℤ

/-- The Chern character, by graded component. -/
noncomputable def k3Ch (E : K3Num) : ℕ → K3Ring
  | 0 => algebraMap ℚ K3Ring (E.1 : ℚ)
  | 1 => algebraMap ℚ K3Ring (E.2.1 : ℚ) * H
  | 2 => algebraMap ℚ K3Ring (E.2.2 : ℚ) * H ^ 2
  | _ + 3 => 0

/-- The Todd class of a K3 of degree `2d`: `td₁ = 0` and `∫td₂ = 2`. -/
noncomputable def k3Todd (d : ℚ) : ℕ → K3Ring
  | 0 => 1
  | 1 => 0
  | 2 => algebraMap ℚ K3Ring (1 / d) * H ^ 2
  | _ + 3 => 0

theorem k3Ch_mem (E : K3Num) (i : ℕ) : k3Ch E i ∈ gradedPiece (⇑k3PB.basis) k3W i := by
  match i with
  | 0 =>
    show algebraMap ℚ K3Ring ((E.1 : ℚ)) ∈ _
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ k3_one_mem
  | 1 => exact algebraMap_mul_mem _ H_mem_piece_one
  | 2 => exact algebraMap_mul_mem _ Hsq_mem_piece_two
  | _ + 3 => exact Submodule.zero_mem _

theorem k3Todd_mem (d : ℚ) (i : ℕ) : k3Todd d i ∈ gradedPiece (⇑k3PB.basis) k3W i := by
  match i with
  | 0 => exact k3_one_mem
  | 1 => exact Submodule.zero_mem _
  | 2 => exact algebraMap_mul_mem _ Hsq_mem_piece_two
  | _ + 3 => exact Submodule.zero_mem _

/-- **The model.** A K3 surface of degree `H² = 2d`, `d > 0`.

`d : ℕ` rather than `ℚ` because `χ` must land in `ℤ`: Riemann–Roch here reads
`χ(r, c, s) = 2r + 2ds`, which is integral exactly when `d` is. -/
@[reducible]
noncomputable def k3NumericalVariety (d : ℕ) (hd : d ≠ 0) :
    NumericalVariety 2 K3Ring K3Num where
  toNumericalRing := k3NumericalRing (d : ℚ)
  rank := { toFun := fun E => E.1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  chComp := k3Ch
  chComp_mem := k3Ch_mem
  chComp_zero := fun _ => rfl
  chComp_add := by
    intro E F i
    match i with
    | 0 =>
      show algebraMap ℚ K3Ring (((E + F).1 : ℚ))
        = algebraMap ℚ K3Ring ((E.1 : ℚ)) + algebraMap ℚ K3Ring ((F.1 : ℚ))
      rw [show ((E + F).1 : ℤ) = E.1 + F.1 from rfl, Int.cast_add, map_add]
    | 1 =>
      show algebraMap ℚ K3Ring (((E + F).2.1 : ℚ)) * H
        = algebraMap ℚ K3Ring ((E.2.1 : ℚ)) * H + algebraMap ℚ K3Ring ((F.2.1 : ℚ)) * H
      rw [show ((E + F).2.1 : ℤ) = E.2.1 + F.2.1 from rfl, Int.cast_add, map_add, add_mul]
    | 2 =>
      show algebraMap ℚ K3Ring (((E + F).2.2 : ℚ)) * H ^ 2
        = algebraMap ℚ K3Ring ((E.2.2 : ℚ)) * H ^ 2 + algebraMap ℚ K3Ring ((F.2.2 : ℚ)) * H ^ 2
      rw [show ((E + F).2.2 : ℤ) = E.2.2 + F.2.2 from rfl, Int.cast_add, map_add, add_mul]
    | _ + 3 => show (0 : K3Ring) = 0 + 0; rw [add_zero]
  toddComp := k3Todd (d : ℚ)
  toddComp_mem := k3Todd_mem (d : ℚ)
  toddComp_zero := rfl
  chi :=
    { toFun := fun E => 2 * E.1 + 2 * (d : ℤ) * E.2.2
      map_zero' := by simp
      map_add' := by intro a b; show 2 * (a.1 + b.1) + 2 * (d : ℤ) * (a.2.2 + b.2.2) = _; ring }
  hirzebruch_riemannRoch := by
    intro E
    have hsum1 : (∑ i ∈ Finset.range (2 + 1), k3Ch E i)
        = algebraMap ℚ K3Ring ((E.1 : ℚ)) + algebraMap ℚ K3Ring ((E.2.1 : ℚ)) * H
          + algebraMap ℚ K3Ring ((E.2.2 : ℚ)) * H ^ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
      rfl
    have hsum2 : (∑ j ∈ Finset.range (2 + 1), k3Todd (d : ℚ) j)
        = 1 + algebraMap ℚ K3Ring (1 / (d : ℚ)) * H ^ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add]
      simp [k3Todd]
    show ((2 * E.1 + 2 * (d : ℤ) * E.2.2 : ℤ) : ℚ) = k3Degree (d : ℚ) _
    rw [hsum1, hsum2]
    have h4 : H ^ 4 = 0 := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, H_pow_three, zero_mul]
    -- Expand the product; `H³ = H⁴ = 0` kill the two overflow terms.
    have hprod :
        (algebraMap ℚ K3Ring ((E.1 : ℚ)) + algebraMap ℚ K3Ring ((E.2.1 : ℚ)) * H
            + algebraMap ℚ K3Ring ((E.2.2 : ℚ)) * H ^ 2)
          * (1 + algebraMap ℚ K3Ring (1 / (d : ℚ)) * H ^ 2)
        = algebraMap ℚ K3Ring ((E.1 : ℚ)) + algebraMap ℚ K3Ring ((E.2.1 : ℚ)) * H
          + algebraMap ℚ K3Ring ((E.1 : ℚ) * (1 / (d : ℚ)) + (E.2.2 : ℚ)) * H ^ 2 := by
      rw [map_add, map_mul]
      linear_combination
        (algebraMap ℚ K3Ring ((E.2.1 : ℚ)) * algebraMap ℚ K3Ring (1 / (d : ℚ))) * H_pow_three
          + (algebraMap ℚ K3Ring ((E.2.2 : ℚ)) * algebraMap ℚ K3Ring (1 / (d : ℚ))) * h4
    rw [hprod, k3Degree_normalForm]
    have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
    push_cast
    field_simp

/-- The model really is a K3: `td₁ = 0` and `∫_X td₂ = χ(O_X) = 2`.

With this instance every theorem in `CohLean/Numerical/K3.lean` — Riemann–Roch, the Mukai
self-pairing, `⟨v,v⟩ = ∫Δ − 2r²` — is a statement about an object that exists. -/
theorem k3_isK3 (d : ℕ) (hd : d ≠ 0) :
    letI := k3NumericalVariety d hd
    K3.IsK3 K3Ring K3Num := by
  -- the `letI` in the statement is zeta-reduced away, so re-establish the instance here
  letI := k3NumericalVariety d hd
  refine ⟨rfl, ?_⟩
  show k3Degree (d : ℚ) (algebraMap ℚ K3Ring (1 / (d : ℚ)) * H ^ 2) = 2
  rw [k3Degree_algebraMap_mul, k3Degree_Hsq]
  have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  field_simp

end Examples

end AlgebraicGeometry.Numerical
