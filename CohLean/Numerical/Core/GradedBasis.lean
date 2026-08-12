/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import CohLean.Numerical.Core.Definitions
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Constructing a `NumericalRing` from a graded basis

`NumericalRing.isInternal` is the one field of `NumericalRing` that is real work, and it is
the same work every time: exhibit `A` as the direct sum of the spans of the graded pieces of
a basis. This file does it once.

Given a basis `b : Module.Basis ι ℚ A` and a weight `w : ι → ℕ` bounded by `n`, set

```
gradedPiece b w k = span ℚ (b '' (w ⁻¹' {k}))
```

— the span of the basis vectors in codimension `k`. Then `gradedPiece` is internal, vanishes
above `n`, and `NumericalRing.ofGradedBasis` assembles a `NumericalRing n A` from it. The
grading being multiplicative is left as a hypothesis, checked on **basis vectors only**:
that is a finite check per model rather than a statement about arbitrary elements.

## Main definitions

* `gradedPiece` — the span of the weight-`k` basis vectors.
* `NumericalRing.ofGradedBasis` — the constructor.

## Design

`w` is not assumed injective, so a graded piece may be spanned by several basis vectors.
That matters: a K3 of Picard rank `ρ` has `dim A¹ = ρ`, and restricting to injective weights
would cover only `ρ = 1`. The independence argument costs nothing extra —
`LinearIndependent.disjoint_span_image` already handles blocks.
-/

universe u v

open Submodule Set

namespace AlgebraicGeometry.Numerical

variable {ι : Type v} {A : Type u} [CommRing A] [Algebra ℚ A]

/-- The span of the basis vectors of weight `k`: the codimension-`k` graded piece. -/
def gradedPiece (b : ι → A) (w : ι → ℕ) (k : ℕ) : Submodule ℚ A :=
  span ℚ (b '' (w ⁻¹' {k}))

variable {b : ι → A} {w : ι → ℕ} {n : ℕ}

/-- Basis vectors lie in their own graded piece. -/
theorem mem_gradedPiece (i : ι) : b i ∈ gradedPiece b w (w i) :=
  subset_span ⟨i, rfl, rfl⟩

/-- Above the dimension there are no basis vectors, hence no graded piece. -/
theorem gradedPiece_eq_bot (hw : ∀ i, w i ≤ n) {k : ℕ} (hk : n < k) :
    gradedPiece b w k = ⊥ := by
  have hempty : w ⁻¹' {k} = (∅ : Set ι) := by
    ext i
    simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
    intro h
    have := hw i
    omega
  rw [gradedPiece, hempty, image_empty, span_empty]

/-- The graded pieces are independent. This is the block form of linear independence:
distinct weights pull back to disjoint sets of indices, and
`LinearIndependent.disjoint_span_image` turns that into disjointness of spans. -/
theorem gradedPiece_iSupIndep (hb : LinearIndependent ℚ b) :
    iSupIndep (gradedPiece b w) := by
  intro k
  have key : Disjoint (span ℚ (b '' (w ⁻¹' {k}))) (span ℚ (b '' (w ⁻¹' {k})ᶜ)) :=
    hb.disjoint_span_image disjoint_compl_right
  refine Disjoint.mono_right ?_ key
  refine iSup_le fun j => iSup_le fun hj => span_mono (image_mono ?_)
  intro i hi
  simp only [mem_preimage, mem_singleton_iff] at hi
  simp only [mem_compl_iff, mem_preimage, mem_singleton_iff]
  rw [hi]
  exact hj

/-- The graded pieces span. -/
theorem gradedPiece_iSup_eq_top (hsp : span ℚ (range b) = ⊤) :
    ⨆ k, gradedPiece b w k = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← hsp, span_le]
  rintro _ ⟨i, rfl⟩
  exact Submodule.mem_iSup_of_mem (w i) (mem_gradedPiece i)

/-- `A` is the direct sum of the spans of the graded pieces of a basis. -/
theorem gradedPiece_isInternal (hb : LinearIndependent ℚ b) (hsp : span ℚ (range b) = ⊤) :
    DirectSum.IsInternal (gradedPiece b w) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (gradedPiece_iSupIndep hb) (gradedPiece_iSup_eq_top hsp)

/-- Multiplicativity of the grading, promoted from basis vectors to all of `A`.

Checking `b p * b q ∈ gradedPiece b w (w p + w q)` is a finite computation in any concrete
model; this lemma is what makes that finite check sufficient. -/
theorem gradedPiece_mul_mem (hmul : ∀ p q : ι, b p * b q ∈ gradedPiece b w (w p + w q))
    {i j : ℕ} {x y : A} (hx : x ∈ gradedPiece b w i) (hy : y ∈ gradedPiece b w j) :
    x * y ∈ gradedPiece b w (i + j) := by
  have hle : gradedPiece b w i * gradedPiece b w j ≤ gradedPiece b w (i + j) := by
    rw [gradedPiece, gradedPiece, Submodule.span_mul_span, span_le]
    rintro _ ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩
    simp only [mem_preimage, mem_singleton_iff] at hp hq
    rw [← hp, ← hq]
    exact hmul p q
  exact hle (Submodule.mul_mem_mul hx hy)

/-- **Build a `NumericalRing` from a graded basis.**

The caller supplies the basis, the weight function, and three finite checks: that `1` sits in
codimension zero, that products of basis vectors respect the grading, and that the degree map
kills every piece but the top one. Everything structural — internality, vanishing above the
dimension — is discharged here. -/
@[reducible]
noncomputable def NumericalRing.ofGradedBasis (n : ℕ) (b : Module.Basis ι ℚ A) (w : ι → ℕ)
    (hw : ∀ i, w i ≤ n)
    (hone : (1 : A) ∈ gradedPiece (b : ι → A) w 0)
    (hmul : ∀ p q : ι, (b : ι → A) p * (b : ι → A) q ∈
      gradedPiece (b : ι → A) w (w p + w q))
    (deg : A →ₗ[ℚ] ℚ)
    (hdeg : ∀ i : ι, w i ≠ n → deg (b i) = 0) :
    NumericalRing n A where
  piece := gradedPiece (b : ι → A) w
  isInternal := gradedPiece_isInternal b.linearIndependent b.span_eq
  piece_eq_bot_of_lt _ hk := gradedPiece_eq_bot hw hk
  one_mem_piece_zero := hone
  mul_mem_piece hx hy := gradedPiece_mul_mem hmul hx hy
  degree := deg
  degree_eq_zero_of_mem := by
    intro k x hk hx
    -- `deg` vanishes on every basis vector of weight `k ≠ n`, hence on their span.
    have hsub : gradedPiece (b : ι → A) w k ≤ LinearMap.ker deg := by
      rw [gradedPiece, span_le]
      rintro _ ⟨i, hi, rfl⟩
      simp only [mem_preimage, mem_singleton_iff] at hi
      exact hdeg i (hi ▸ hk)
    exact hsub hx

/-! ### Smoke test

A constructor nobody has called is not known to work. This exercises every hypothesis of
`ofGradedBasis` on the smallest possible input — the dimension-zero intersection ring `ℚ` of
a point, one basis vector in codimension zero — and so checks that the five side conditions
are dischargeable in practice, not merely well-typed.

The exported point instance lives in `CohLean/Numerical/Examples/DimensionZero/Point.lean` and is built
directly; this is deliberately a second, independent construction of the same object. -/
section SmokeTest

private noncomputable def pointBasis : Module.Basis Unit ℚ ℚ := Module.Basis.singleton Unit ℚ

private theorem pointGradedPiece_zero :
    gradedPiece (⇑pointBasis) (fun _ : Unit => (0 : ℕ)) 0 = ⊤ := by
  have hpre : (fun _ : Unit => (0 : ℕ)) ⁻¹' {0} = (univ : Set Unit) := by
    ext i; simp
  rw [gradedPiece, hpre, image_univ, pointBasis.span_eq]

@[reducible]
private noncomputable def pointRingViaGradedBasis : NumericalRing 0 ℚ :=
  NumericalRing.ofGradedBasis 0 pointBasis (fun _ => 0) (fun _ => le_refl 0)
    (by rw [pointGradedPiece_zero]; trivial)
    (fun p q => by
      -- the weight index is `(fun _ => 0) p + (fun _ => 0) q`, defeq to `0` but not
      -- syntactically equal to it, so `rw` needs the equation stated at that index
      have h : gradedPiece (⇑pointBasis) (fun _ : Unit => (0 : ℕ))
          ((fun _ : Unit => (0 : ℕ)) p + (fun _ : Unit => (0 : ℕ)) q) = ⊤ :=
        pointGradedPiece_zero
      rw [h]; trivial)
    LinearMap.id
    (fun _ hi => absurd rfl hi)

end SmokeTest

end AlgebraicGeometry.Numerical
