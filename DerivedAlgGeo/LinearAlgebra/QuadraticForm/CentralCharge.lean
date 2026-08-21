/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.LinearAlgebra.QuadraticForm.Orientation
import Mathlib.Data.Complex.Basic

/-!
# The central charge of a positive pair, and the support property

A positive pair `(x, y)` — the real and imaginary parts of `Ω` — determines

```
Z (v) = ⟪x, v⟫ + i ⟪y, v⟫
```

which **is** `⟪Ω, -⟫` written without complexifying the space, since `⟪·,·⟫` is
the polar form. For the exponential pair of a Mukai extension it is Bridgeland's
`Z(β,ω)`.

Nothing below is new mathematics: every statement is something route (A) already
proved, said in charge language, where they read as the data and the axioms of a
stability condition rather than as facts about a quadratic space.

## Main results

* `centralCharge_eq_zero_iff` — **the kernel of `Z` is the orthogonal complement
  of the plane.**
* `neg_of_centralCharge_eq_zero` — **the kernel is negative definite.** This is
  `neg_of_mem_orthogonal`, and it is the **support property**: it is what makes
  the walls locally finite, and route (A)'s engine turns out to be exactly this
  axiom in disguise.
* `centralCharge_ne_zero_of_nonneg` — no class of nonnegative square is in the
  kernel, so there are no walls in the positive cone.
* `mem_wall_iff_centralCharge_eq_zero` — for a spherical class, a wall is a
  vanishing charge.
* `isCompl_ker_centralCharge` — `M = W ⊕ ker Z`.

## What a central charge is not

One datum of a stability condition, not a stability condition. No slicing, no
Harder–Narasimhan filtrations and no `Stab†(X)` appear here or are implied. `Z`
is defined on the lattice; the Mukai vector of an object is geometry and lives
elsewhere.
-/

open QuadraticMap Complex

namespace PeriodDomain

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M}

section Defs

variable (Q)

/-- The **central charge** of an ordered pair: the pairing against `x` and `y`
read as the real and imaginary parts of a complex number. -/
def centralCharge (x y v : M) : ℂ :=
  Complex.ofReal (polar (⇑Q) x v) + Complex.ofReal (polar (⇑Q) y v) * Complex.I

end Defs

@[simp]
theorem centralCharge_re (x y v : M) : (centralCharge Q x y v).re = polar (⇑Q) x v := by
  simp [centralCharge]

@[simp]
theorem centralCharge_im (x y v : M) : (centralCharge Q x y v).im = polar (⇑Q) y v := by
  simp [centralCharge]

theorem centralCharge_add (x y v w : M) :
    centralCharge Q x y (v + w) = centralCharge Q x y v + centralCharge Q x y w := by
  apply Complex.ext <;> simp [polar_add_right]

theorem centralCharge_smul (x y v : M) (a : ℝ) :
    centralCharge Q x y (a • v) = (a : ℂ) * centralCharge Q x y v := by
  apply Complex.ext <;> simp [polar_smul_right]

@[simp]
theorem centralCharge_zero (x y : M) : centralCharge Q x y 0 = 0 := by
  apply Complex.ext <;> simp

/-- **The kernel of the charge is the orthogonal complement of the plane.** -/
theorem centralCharge_eq_zero_iff {x y v : M} :
    centralCharge Q x y v = 0 ↔ v ∈ orthogonal Q (pairSpan x y) := by
  rw [pairSpan, mem_orthogonal_span_pair_iff, Complex.ext_iff]
  simp

/-- The charge kernel as a submodule: the orthogonal complement, named for what
it is in stability language. -/
theorem ker_centralCharge_eq (x y : M) :
    {v : M | centralCharge Q x y v = 0} = (orthogonal Q (pairSpan x y) : Set M) := by
  ext v
  exact centralCharge_eq_zero_iff

section FiniteDimensional

variable [FiniteDimensional ℝ M]

/-- **The support property.** On the kernel of the charge the form is negative
definite.

This is `neg_of_mem_orthogonal` under the identification of the kernel with the
orthogonal complement, and it is the axiom that makes the wall family locally
finite — route (A)'s engine is this statement. -/
theorem neg_of_centralCharge_eq_zero (hsig : HasSignatureTwo Q) {x y : M}
    (hxy : IsPositivePair Q x y) {v : M} (hv : centralCharge Q x y v = 0) (hv0 : v ≠ 0) :
    Q v < 0 :=
  neg_of_mem_orthogonal hsig hxy (centralCharge_eq_zero_iff.mp hv) hv0

/-- **No class of nonnegative square has vanishing charge**, so there are no
walls in the positive cone. -/
theorem centralCharge_ne_zero_of_nonneg (hsig : HasSignatureTwo Q) {x y : M}
    (hxy : IsPositivePair Q x y) {v : M} (hv : 0 ≤ Q v) (hv0 : v ≠ 0) :
    centralCharge Q x y v ≠ 0 := by
  intro hzero
  have := neg_of_centralCharge_eq_zero hsig hxy hzero hv0
  linarith

omit [FiniteDimensional ℝ M] in
/-- **A wall is a vanishing charge**: for a spherical class, the plane lies on its
wall exactly when the class has charge zero. -/
theorem mem_wall_iff_centralCharge_eq_zero {x y : M} (hxy : IsPositivePair Q x y) {δ : M} :
    pairSpan x y ∈ wall Q δ ↔ centralCharge Q x y δ = 0 := by
  rw [mem_wall_iff_mem_orthogonal hxy, centralCharge_eq_zero_iff]

/-- **The charge splits the space**: `M = W ⊕ ker Z`. -/
theorem isCompl_ker_centralCharge {x y : M} (hxy : IsPositivePair Q x y) :
    IsCompl (pairSpan x y) (orthogonal Q (pairSpan x y)) :=
  isCompl_orthogonal hxy

end FiniteDimensional

end PeriodDomain
