/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The alternating sum of dimensions along an exact sequence

The Euler characteristic of a bounded exact complex of finite-dimensional
vector spaces vanishes.  This is the arithmetic fact underneath every
"`χ` is additive on distinguished triangles" argument, and Mathlib does not
have it: `Mathlib.Algebra.Homology.EulerCharacteristic` defines `eulerChar`
and `homologyEulerChar` and converts a `finsum` to a finite sum, but proves no
relation between them and nothing about exact complexes.

## The shape of the statement

Everything follows from one identity, `sum_range_succ_smul_finrank`:

`∑_{i ≤ n} (-1)^i · dim Vᵢ = (-1)^n · dim (range dₙ)`,

for a complex `d i : V i →ₗ[k] V (i+1)` that is exact at every positive index
and has `ker d₀ = ⊥`.  The proof is rank--nullity plus an induction in which
the two `range` terms cancel; stating the partial sum as a *rank* rather than
as zero is what makes that induction go through without boundary cases.

Vanishing is then the corollary `sum_range_succ_smul_finrank_eq_zero`, which
needs only that the complex stops: `range dₙ = ⊥`, in practice because
`V (n+1)` is trivial.

Indices are `ℕ` deliberately.  With `ℤ` the exactness hypothesis reads
`ker (d i) = range (d (i-1))`, whose right-hand side lives in `V (i - 1 + 1)`
rather than in `V i`, and every proof then carries a transport along that
equality.  A caller with a `ℤ`-indexed complex supported in `[a, b]`
reindexes once, at the boundary, instead.

## What this file does not do

It says nothing about complexes, homology, `ModuleCat`, or triangulated
categories.  It is linear algebra, and the categorical Euler form that
motivated it has to be assembled elsewhere.
-/

universe u v

namespace DerivedAlgGeo.LinearAlgebra

open Finset Module

variable {k : Type u} [Field k] {V : ℕ → Type v}
  [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, FiniteDimensional k (V i)]

/-- The rank of the `i`-th differential. -/
noncomputable def diffRank (d : ∀ i, V i →ₗ[k] V (i + 1)) (i : ℕ) : ℕ :=
  finrank k (LinearMap.range (d i))

/-- Rank--nullity at index `i`, in the form the induction consumes. -/
theorem finrank_eq_finrank_ker_add_diffRank (d : ∀ i, V i →ₗ[k] V (i + 1))
    (i : ℕ) :
    finrank k (V i) = finrank k (LinearMap.ker (d i)) + diffRank d i := by
  rw [diffRank, add_comm]
  exact (LinearMap.finrank_range_add_finrank_ker (d i)).symm

/-- At an index where the sequence is exact, the kernel contributes the
previous differential's rank. -/
theorem finrank_eq_diffRank_add_diffRank (d : ∀ i, V i →ₗ[k] V (i + 1))
    (i : ℕ) (hex : LinearMap.ker (d (i + 1)) = LinearMap.range (d i)) :
    finrank k (V (i + 1)) = diffRank d i + diffRank d (i + 1) := by
  rw [finrank_eq_finrank_ker_add_diffRank d (i + 1), hex]
  rfl

/-- **The partial alternating sum is the rank of the last differential.**

`∑_{i ≤ n} (-1)^i · dim Vᵢ = (-1)^n · dim (range dₙ)`.

Carrying the rank on the right, rather than proving the sum is zero directly,
is what lets the induction close: the inductive step cancels the two copies of
`diffRank d n` that rank--nullity and exactness produce. -/
theorem sum_range_succ_smul_finrank (d : ∀ i, V i →ₗ[k] V (i + 1))
    (hzero : LinearMap.ker (d 0) = ⊥)
    (hex : ∀ i, LinearMap.ker (d (i + 1)) = LinearMap.range (d i)) (n : ℕ) :
    ∑ i ∈ range (n + 1), (-1 : ℤ) ^ i * finrank k (V i)
      = (-1 : ℤ) ^ n * diffRank d n := by
  induction n with
  | zero =>
    have h : finrank k (V 0) = diffRank d 0 := by
      rw [finrank_eq_finrank_ker_add_diffRank d 0, hzero, finrank_bot, zero_add]
    simp [h]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih,
      finrank_eq_diffRank_add_diffRank d n (hex n)]
    push_cast
    ring

/-- **The alternating sum along a bounded exact sequence vanishes.**

The hypotheses are exactness at every positive index, injectivity at the
bottom, and that the complex stops at `n`.  In practice `hstop` comes from
`V (n+1)` being trivial, for which `diffRank_eq_zero_of_subsingleton` is the
convenience form. -/
theorem sum_range_succ_smul_finrank_eq_zero (d : ∀ i, V i →ₗ[k] V (i + 1))
    (hzero : LinearMap.ker (d 0) = ⊥)
    (hex : ∀ i, LinearMap.ker (d (i + 1)) = LinearMap.range (d i)) (n : ℕ)
    (hstop : diffRank d n = 0) :
    ∑ i ∈ range (n + 1), (-1 : ℤ) ^ i * finrank k (V i) = 0 := by
  rw [sum_range_succ_smul_finrank d hzero hex n, hstop]
  simp

omit [∀ i, FiniteDimensional k (V i)] in
/-- A differential into a trivial space has rank zero — the usual source of
`hstop`. -/
theorem diffRank_eq_zero_of_subsingleton (d : ∀ i, V i →ₗ[k] V (i + 1))
    (n : ℕ) (h : Subsingleton (V (n + 1))) : diffRank d n = 0 := by
  have hbot : LinearMap.range (d n) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x _
    exact Subsingleton.elim x 0
  rw [diffRank, hbot, finrank_bot]

end DerivedAlgGeo.LinearAlgebra
