/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Numerical data of a smooth projective variety over a field

This is **Layer A** of `CohLean`: the numerical interface that Bridgeland-stability
arguments actually consume from a smooth projective variety, stated for a variety of
*arbitrary* dimension `n` so that the surface case (`n = 2`), the threefold case
(`n = 3`) and the fourfold case (`n = 4`) are specialisations rather than rewrites.

## Design

Two classes:

* `NumericalRing n A` — `A` is the numerical intersection ring `A^•(X)_ℚ`: a commutative
  `ℚ`-algebra graded by codimension, concentrated in degrees `0, …, n`, with a `ℚ`-linear
  degree map `∫_X : A → ℚ` supported in top codimension.
* `NumericalVariety n A N` — adds the numerical Grothendieck group `N`, the Chern
  character, the Todd class of `X` and the Euler characteristic, subject to
  Hirzebruch–Riemann–Roch.

## Trust boundary

Every field of `NumericalVariety` beyond the ring structure is an **axiom**, not a
theorem: in particular `hirzebruch_riemannRoch` is assumed here. Discharging it is the
whole job of Layer B (`CohLean.Coh`), which builds `Coh X`, sheaf cohomology, `χ`, and
intersection numbers from Mathlib's scheme theory. Nothing downstream of this file may
treat these fields as proved.

Graded components of `ch` and `td` are carried as **data** (`chComp`, `toddComp`) rather
than extracted by a projection operator. That is deliberate: it keeps this file free of
graded-decomposition machinery, and every consumer needs the components anyway.

## References

* Hirzebruch, *Topological Methods in Algebraic Geometry*, §21
* Fulton, *Intersection Theory*, ch. 15 and 18
* Huybrechts–Lehn, *The Geometry of Moduli Spaces of Sheaves*, §1.1 and §2.1
-/

universe u v

namespace AlgebraicGeometry.Numerical

/-- A **numerical intersection ring of dimension `n`**: a commutative `ℚ`-algebra `A`
graded by codimension and concentrated in degrees `0, …, n`, together with a `ℚ`-linear
degree map `degree` (written `∫_X` in the literature) supported in top codimension.

`n` is an `outParam`: a given ring is the intersection ring of a variety of one fixed
dimension, so the dimension is determined by the carrier. -/
class NumericalRing (n : outParam ℕ) (A : Type u) [CommRing A] [Algebra ℚ A] where
  /-- The codimension-`i` graded piece `Aⁱ`. -/
  piece : ℕ → Submodule ℚ A
  /-- The pieces decompose `A`, i.e. `A = ⨁ᵢ Aⁱ`. -/
  isInternal : DirectSum.IsInternal piece
  /-- Nothing lives above the dimension: `Aⁱ = 0` for `i > n`. -/
  piece_eq_bot_of_lt : ∀ ⦃i : ℕ⦄, n < i → piece i = ⊥
  /-- `1 ∈ A⁰`. -/
  one_mem_piece_zero : (1 : A) ∈ piece 0
  /-- The grading is multiplicative: `Aⁱ · Aʲ ⊆ Aⁱ⁺ʲ`. -/
  mul_mem_piece : ∀ {i j : ℕ} {x y : A}, x ∈ piece i → y ∈ piece j → x * y ∈ piece (i + j)
  /-- The degree map `∫_X : A → ℚ`. -/
  degree : A →ₗ[ℚ] ℚ
  /-- `∫_X` kills every graded piece other than the top one. -/
  degree_eq_zero_of_mem : ∀ {i : ℕ} {x : A}, i ≠ n → x ∈ piece i → degree x = 0

namespace NumericalRing

variable {n : ℕ} {A : Type u} [CommRing A] [Algebra ℚ A] [NumericalRing n A]

/-- Scalars sit in codimension zero. -/
theorem algebraMap_mem_piece_zero (q : ℚ) :
    algebraMap ℚ A q ∈ piece (n := n) 0 := by
  have h : algebraMap ℚ A q = q • (1 : A) := by
    rw [Algebra.smul_def, mul_one]
  rw [h]
  exact Submodule.smul_mem _ _ one_mem_piece_zero

/-- `∫_X` is `ℚ`-homogeneous in the sense we actually use it: pulling a scalar out of a
product with `algebraMap`. -/
theorem degree_algebraMap_mul (q : ℚ) (x : A) :
    degree (n := n) (algebraMap ℚ A q * x) = q * degree (n := n) x := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- Anything in a piece above the dimension is zero. -/
theorem eq_zero_of_mem_piece_of_lt {i : ℕ} (hi : n < i) {x : A} (hx : x ∈ piece i) :
    x = 0 := by
  rw [piece_eq_bot_of_lt hi] at hx
  simpa using hx

end NumericalRing

/-- **Numerical data of a smooth projective variety of dimension `n` over a field.**

`A` is the numerical intersection ring `A^•(X)_ℚ` and `N` is the numerical Grothendieck
group `N(X) = K(X)/≡`. The Chern character is carried by its graded components
`chComp E i = chᵢ(E)`, the Todd class of `X` by `toddComp i = tdᵢ(X)`.

`hirzebruch_riemannRoch` is an **axiom** at this layer — see the module docstring. -/
class NumericalVariety (n : outParam ℕ) (A : Type u) (N : Type v)
    [CommRing A] [Algebra ℚ A] [AddCommGroup N] extends NumericalRing n A where
  /-- The rank homomorphism `N(X) → ℤ`. -/
  rank : N →+ ℤ
  /-- The codimension-`i` component of the Chern character, `chᵢ(E)`. -/
  chComp : N → ℕ → A
  /-- `chᵢ(E)` lives in codimension `i`. -/
  chComp_mem : ∀ (E : N) (i : ℕ), chComp E i ∈ piece i
  /-- `ch₀(E) = rank E`. -/
  chComp_zero : ∀ E : N, chComp E 0 = algebraMap ℚ A (rank E : ℚ)
  /-- The Chern character is additive on `N(X)`. -/
  chComp_add : ∀ (E F : N) (i : ℕ), chComp (E + F) i = chComp E i + chComp F i
  /-- The codimension-`i` component of the Todd class of `X`. -/
  toddComp : ℕ → A
  /-- `tdᵢ(X)` lives in codimension `i`. -/
  toddComp_mem : ∀ i : ℕ, toddComp i ∈ piece i
  /-- `td₀(X) = 1`. -/
  toddComp_zero : toddComp 0 = (1 : A)
  /-- The Euler characteristic `χ(E) = Σᵢ (-1)ⁱ dim Hⁱ(X, E)`. -/
  chi : N →+ ℤ
  /-- **Hirzebruch–Riemann–Roch**: `χ(E) = ∫_X ch(E) · td(X)`. Assumed at this layer. -/
  hirzebruch_riemannRoch : ∀ E : N,
    (chi E : ℚ) = degree ((∑ i ∈ Finset.range (n + 1), chComp E i) *
      (∑ j ∈ Finset.range (n + 1), toddComp j))

namespace NumericalVariety

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety n A N]

open NumericalRing

/-- The Chern character `ch(E) = Σᵢ chᵢ(E)`. -/
def ch (E : N) : A := ∑ i ∈ Finset.range (n + 1), chComp (A := A) E i

/-- The Todd class `td(X) = Σᵢ tdᵢ(X)`. -/
def todd (n : ℕ) (A : Type u) [CommRing A] [Algebra ℚ A] {N : Type v} [AddCommGroup N]
    [NumericalVariety n A N] : A :=
  ∑ j ∈ Finset.range (n + 1), toddComp (N := N) j

/-- Hirzebruch–Riemann–Roch, restated in terms of `ch` and `todd`. -/
theorem hrr (E : N) :
    (chi (A := A) E : ℚ) = degree (n := n) (ch (A := A) E * todd n A (N := N)) :=
  hirzebruch_riemannRoch E

/-- Components of the Chern character above the dimension vanish. -/
theorem chComp_eq_zero_of_lt (E : N) {i : ℕ} (hi : n < i) :
    chComp (A := A) E i = 0 :=
  eq_zero_of_mem_piece_of_lt hi (chComp_mem E i)

/-- Components of the Todd class above the dimension vanish. -/
theorem toddComp_eq_zero_of_lt {i : ℕ} (hi : n < i) :
    toddComp (A := A) (N := N) i = 0 :=
  eq_zero_of_mem_piece_of_lt hi (toddComp_mem i)

/-- The degree of a mixed term `chᵢ(E) · tdⱼ(X)` vanishes unless `i + j = n`.

This is the single computational fact behind every dimension-specific Riemann–Roch
formula: expanding `ch(E) · td(X)` leaves only the terms of total codimension `n`. -/
theorem degree_chComp_mul_toddComp_eq_zero (E : N) {i j : ℕ} (hij : i + j ≠ n) :
    degree (n := n) (chComp (A := A) E i * toddComp (N := N) j) = 0 :=
  degree_eq_zero_of_mem hij (mul_mem_piece (chComp_mem E i) (toddComp_mem j))

end NumericalVariety

end AlgebraicGeometry.Numerical
