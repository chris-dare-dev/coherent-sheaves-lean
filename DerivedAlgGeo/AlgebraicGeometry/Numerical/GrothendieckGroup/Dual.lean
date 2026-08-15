/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Algebra.Hom
import DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.General

/-!
# The dual involution on a numerical intersection ring

`(-)^∨` acts on the codimension-`i` part of `A^•(X)_ℚ` by `(-1)^i`. It is what turns
Hirzebruch–Riemann–Roch into its bilinear form `χ(E,F) = ∫_X ch(E)^∨ · ch(F) · td(X)`, and
so it is the last piece of Layer A that Bridgeland stability needs: the central charge
factors through `N(X)` modulo the radical of that pairing.

## Why a separate class

`NumericalRingWithDual` is a **mixin** over `NumericalRing`, not a field of it and not an
`extends`. A field would break every existing instance in `Numerical/Examples/`; an
`extends` would put two paths to `NumericalRing n A` in scope whenever a `NumericalVariety`
is also present, and instance search would see a diamond. A mixin taking `[NumericalRing n A]`
as a parameter has neither problem, and a ring that has no dual simply has no instance.

## Main definitions

* `NumericalRingWithDual n A` — the involution, as data plus the axiom that it acts by
  `(-1)^i` on `piece i`.
* `chDual E` — `ch(E)^∨`, written directly as `Σᵢ (-1)ⁱ chᵢ(E)` rather than as `dual (ch E)`.

## Main results

* `dual_ch` — the two descriptions of `ch(E)^∨` agree.
* `dual_involutive_of_mem_piece` — `(-)^∨` is an involution on each graded piece.

## Deliberately not stated

`dual (dual x) = x` for *arbitrary* `x`, and `degree (dual x) = (-1)^n · degree x`. Both are
true, and both need the graded decomposition of `x` — `NumericalRing.isInternal` — rather
than just membership in a single piece. Nothing downstream needs them: every consumer here
reaches `dual` through `chComp` and `toddComp`, which are graded by construction, so the
component-wise lemmas suffice. Adding the general versions means importing
`DirectSum.IsInternal` machinery for no current gain.
-/

universe u v

namespace AlgebraicGeometry.Numerical

open NumericalRing Finset

/-- The **dual involution** on a numerical intersection ring: a `ℚ`-algebra endomorphism
acting on codimension `i` by `(-1)^i`.

Geometrically this is `E ↦ E^∨` read through the Chern character: `chᵢ(E^∨) = (-1)ⁱchᵢ(E)`.
It is carried as data because `NumericalRing` does not expose the graded projections, so
there is nothing to define it *from* at this layer. -/
class NumericalRingWithDual (n : outParam ℕ) (A : Type u) [CommRing A] [Algebra ℚ A]
    [NumericalRing n A] where
  /-- The involution, as a `ℚ`-algebra map. -/
  dual : A →ₐ[ℚ] A
  /-- It acts on codimension `i` by `(-1)^i`. -/
  dual_of_mem_piece : ∀ {i : ℕ} {x : A}, x ∈ piece (n := n) i → dual x = (-1 : ℚ) ^ i • x

namespace NumericalRingWithDual

variable {n : ℕ} {A : Type u} [CommRing A] [Algebra ℚ A] [NumericalRing n A]
variable [NumericalRingWithDual n A]

/-- `(-)^∨` preserves each graded piece: it only rescales it. -/
theorem dual_mem_piece {i : ℕ} {x : A} (hx : x ∈ piece (n := n) i) :
    dual x ∈ piece (n := n) i := by
  rw [dual_of_mem_piece hx]
  exact Submodule.smul_mem _ _ hx

/-- `(-)^∨` is an involution on each graded piece. -/
theorem dual_involutive_of_mem_piece {i : ℕ} {x : A} (hx : x ∈ piece (n := n) i) :
    dual (dual x) = x := by
  rw [dual_of_mem_piece hx, map_smul, dual_of_mem_piece hx, smul_smul, ← pow_add]
  rw [Even.neg_one_pow ⟨i, rfl⟩, one_smul]

/-- Scalars are fixed by `(-)^∨`, since they sit in codimension zero. -/
theorem dual_algebraMap (q : ℚ) : dual (algebraMap ℚ A q) = algebraMap ℚ A q := by
  rw [dual_of_mem_piece (algebraMap_mem_piece_zero (n := n) q), pow_zero, one_smul]

end NumericalRingWithDual

namespace NumericalVariety

open NumericalRingWithDual

variable {n : ℕ} {A : Type u} {N : Type v}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety n A N]

/-- The Chern character is additive, componentwise additivity summed up.

Stated before the dual is in scope because it has nothing to do with it. -/
theorem ch_add (E F : N) : ch (A := A) (E + F) = ch (A := A) E + ch (A := A) F := by
  simp only [ch, chComp_add]
  exact Finset.sum_add_distrib

/-- The **dual Chern character** `ch(E)^∨ = Σᵢ (-1)ⁱ chᵢ(E)`.

Defined from the grading alone, with no `NumericalRingWithDual` instance in sight: the
alternating sum is available on any `NumericalVariety`, and `dual_ch` below is what says it
deserves the name. Everything the Euler pairing needs lives at this level of generality. -/
noncomputable def chDual (E : N) : A :=
  ∑ i ∈ range (n + 1), (-1 : ℚ) ^ i • chComp (A := A) E i

/-- `ch(-)^∨` is additive, componentwise again. -/
theorem chDual_add (E F : N) :
    chDual (A := A) (E + F) = chDual (A := A) E + chDual (A := A) F := by
  simp only [chDual, chComp_add, smul_add]
  exact Finset.sum_add_distrib

variable [NumericalRingWithDual n A]

/-- `chᵢ(E^∨) = (-1)ⁱ chᵢ(E)`. -/
theorem dual_chComp (E : N) (i : ℕ) :
    dual (chComp (A := A) E i) = (-1 : ℚ) ^ i • chComp (A := A) E i :=
  dual_of_mem_piece (chComp_mem E i)

/-- `tdᵢ(X)^∨ = (-1)ⁱ tdᵢ(X)`. -/
theorem dual_toddComp (i : ℕ) :
    dual (toddComp (A := A) (N := N) i) = (-1 : ℚ) ^ i • toddComp (A := A) (N := N) i :=
  dual_of_mem_piece (toddComp_mem i)

/-- `ch(E)^∨` really is `ch(E)` pushed through the involution. -/
theorem dual_ch (E : N) : dual (ch (A := A) E) = chDual (A := A) E := by
  simp only [ch, chDual, map_sum]
  exact Finset.sum_congr rfl fun i _ => dual_chComp E i

end NumericalVariety

end AlgebraicGeometry.Numerical
