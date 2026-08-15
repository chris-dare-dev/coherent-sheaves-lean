/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Numerical.GrothendieckGroup.EulerPairing
import DerivedAlgGeo.LinearAlgebra.Lattice.Mukai.Basic

/-!
# The Mukai vector, and the identification of the two Mukai pairings

`LinearAlgebra/Lattice/Mukai` builds the abstract Mukai extension `ℤ × Λ × ℤ`
of a symmetric bilinear lattice and says, in its own docstring, that the
identification with any geometric lattice **is not made there**.
`Numerical/GrothendieckGroup/EulerPairing` separately defines a `ℚ`-valued
`K3.mukaiPairing` on the numerical Grothendieck group by an explicit formula.
The two have never been connected.  This file connects them.

The obstruction is integrality, not content.  The abstract extension is
`ℤ`-valued; the numerical layer is `ℚ`-valued, because `degree` lands in `ℚ`
and `mukaiS` is a `ℚ`-combination.  On an actual K3 both are integers — `c₁`
lies in the Néron--Severi group with its integral intersection form, and
`s = r + ∫ch₂` is an integer — but neither fact is available at this layer, so
both enter as supplied data.

`IntegralMukaiData` is that data: a lattice `Λ`, an integral symmetric form on
it, integral `c₁` and `s`, and the two compatibility equations saying they
compute the `ℚ`-valued quantities the numerical layer already has.  Given it,
`mukaiVector E = (rank E, c₁ E, s E)` is a genuine element of
`Mukai.MukaiLattice Λ`, and everything the abstract lattice file proves about
sphericity, isotropy and expected dimension becomes a statement about `χ`.

## Main results

* `pairing_mukaiVector` — the abstract pairing computes `K3.mukaiPairing`.
* `chi₂_eq_neg_pairing` — `χ(E,F) = −⟪v(E), v(F)⟫`, now with `⟪-,-⟫` the
  abstract lattice form rather than the ad-hoc formula.
* `isSpherical_mukaiVector_iff` — `v(E)` is spherical exactly when `χ(E,E) = 2`.
* `expectedDim_mukaiVector` — `⟪v,v⟫ + 2 = 2 − χ(E,E)`.

## What this file does not assert

* Nothing constructs an `IntegralMukaiData`.  Producing one is the geometric
  obligation of exhibiting `NS(X)` with its intersection form, and of proving
  the integrality of `∫ch₂ + r`; both are Layer B work.
* `isSpherical_mukaiVector_iff` is numerical.  That an object with `χ(E,E) = 2`
  *is* spherical in the sense of `Hom(E,E) = k` and `Ext²(E,E) = k`
  (Huybrechts, §8.1) needs `Ext` and is not stated here — the converse
  direction is the one that holds, and only numerically.
* `expectedDim` is a definition in the abstract file, not the theorem that a
  moduli space has that dimension.  Nothing here upgrades it.
* No connection is made to `CategoryTheory.Triangulated.K₀` or to the
  Fourier--Mukai lane.  Those use a different Grothendieck group, and no
  bridge between it and this `N` exists anywhere in the repository; asserting
  that a kernel functor acts on the Mukai lattice needs that bridge first.
-/

universe u v w

namespace AlgebraicGeometry.Numerical

namespace K3

open NumericalRing NumericalRingWithDual NumericalVariety

variable {A : Type u} {N : Type v} {Λ : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety 2 A N]
  [AddCommGroup Λ]

/-- The integral structure that makes the numerical Mukai pairing a pairing in
the abstract Mukai extension.

Every field is a claim about a supplied lattice `Λ`, and the two `_spec`
fields are where the geometry would go: `b_spec` says the integral form on `Λ`
computes `∫c₁(E)·c₁(F)`, and `s_spec` says the integer `s E` computes
`mukaiS E = r + ∫ch₂`. -/
structure IntegralMukaiData (A : Type u) (N : Type v) (Λ : Type w)
    [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety 2 A N]
    [AddCommGroup Λ] where
  /-- The first Chern class, valued in the supplied lattice. -/
  c₁ : N → Λ
  /-- The integral third Mukai coordinate. -/
  s : N → ℤ
  /-- The integral symmetric form on `Λ`. -/
  b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ
  /-- The form is symmetric. -/
  b_comm : ∀ x y : Λ, b x y = b y x
  /-- The form computes the intersection number of first Chern classes. -/
  b_spec : ∀ E F : N, (b (c₁ E) (c₁ F) : ℚ)
    = degree (n := 2) (chComp (A := A) E 1 * chComp (A := A) F 1)
  /-- The integral third coordinate computes `mukaiS`. -/
  s_spec : ∀ E : N, (s E : ℚ) = mukaiS (A := A) E

namespace IntegralMukaiData

variable (D : IntegralMukaiData A N Λ)

/-- The Mukai vector `v(E) = (r, c₁, s)` as an element of the abstract Mukai
extension of `Λ`. -/
def mukaiVector (E : N) : Mukai.MukaiLattice Λ :=
  (rank (A := A) E, D.c₁ E, D.s E)

@[simp]
theorem mukaiVector_fst (E : N) : (D.mukaiVector E).1 = rank (A := A) E := rfl

@[simp]
theorem mukaiVector_snd_fst (E : N) : (D.mukaiVector E).2.1 = D.c₁ E := rfl

@[simp]
theorem mukaiVector_snd_snd (E : N) : (D.mukaiVector E).2.2 = D.s E := rfl

/-- **The abstract Mukai pairing computes the numerical one.**  This is the
identification the abstract lattice file declined to make, discharged from the
supplied integral data. -/
theorem pairing_mukaiVector (E F : N) :
    (Mukai.pairing D.b (D.mukaiVector E) (D.mukaiVector F) : ℚ)
      = mukaiPairing (A := A) E F := by
  rw [mukaiVector, mukaiVector, Mukai.pairing_mk, mukaiPairing]
  push_cast
  rw [D.b_spec, D.s_spec, D.s_spec]

/-- The self-pairing of a Mukai vector computes `mukaiSelfPairing`. -/
theorem selfPairing_mukaiVector (E : N) :
    (Mukai.selfPairing D.b (D.mukaiVector E) : ℚ)
      = mukaiSelfPairing (A := A) E := by
  rw [Mukai.selfPairing_eq_pairing, D.pairing_mukaiVector, mukaiPairing_self]

variable [IsK3 A N]

/-- **`χ(E,F) = −⟪v(E), v(F)⟫`**, with `⟪-,-⟫` the abstract Mukai-lattice form.

`K3.chi₂_eq_neg_mukaiPairing` states this against the explicit formula; this
version states it against the lattice, which is what makes the sphericity and
expected-dimension vocabulary of `LinearAlgebra/Lattice/Mukai` applicable to
the Euler form. -/
theorem chi₂_eq_neg_pairing (E F : N) :
    chi₂ (A := A) E F
      = -(Mukai.pairing D.b (D.mukaiVector E) (D.mukaiVector F) : ℚ) := by
  rw [D.pairing_mukaiVector, chi₂_eq_neg_mukaiPairing]

/-- The self-pairing of `v(E)`, cast to `ℚ`, is `−χ(E,E)`. -/
theorem selfPairing_mukaiVector_eq_neg_chi₂ (E : N) :
    (Mukai.selfPairing D.b (D.mukaiVector E) : ℚ) = -chi₂ (A := A) E E := by
  rw [Mukai.selfPairing_eq_pairing, D.chi₂_eq_neg_pairing]
  ring

/-- **A Mukai vector is spherical exactly when `χ(E,E) = 2`.**

Numerically only: this says nothing about `Hom(E,E)` or `Ext²(E,E)`, which
would need an `Ext` this layer does not have. -/
theorem isSpherical_mukaiVector_iff (E : N) :
    Mukai.IsSpherical D.b (D.mukaiVector E) ↔ chi₂ (A := A) E E = 2 := by
  rw [Mukai.isSpherical_iff, ← @Int.cast_inj ℚ,
    D.selfPairing_mukaiVector_eq_neg_chi₂]
  push_cast
  constructor <;> intro h <;> linarith

/-- A Mukai vector is isotropic exactly when `χ(E,E) = 0`. -/
theorem isIsotropic_mukaiVector_iff (E : N) :
    Mukai.IsIsotropic D.b (D.mukaiVector E) ↔ chi₂ (A := A) E E = 0 := by
  rw [Mukai.isIsotropic_iff, ← @Int.cast_inj ℚ,
    D.selfPairing_mukaiVector_eq_neg_chi₂]
  push_cast
  constructor <;> intro h <;> linarith

/-- The expected dimension attached to `v(E)` is `2 − χ(E,E)`.

`Mukai.expectedDim` is a definition, not the moduli-dimension theorem; this
identity relocates it onto the Euler form and asserts nothing geometric. -/
theorem expectedDim_mukaiVector (E : N) :
    (Mukai.expectedDim D.b (D.mukaiVector E) : ℚ) = 2 - chi₂ (A := A) E E := by
  rw [Mukai.expectedDim]
  push_cast
  rw [D.selfPairing_mukaiVector_eq_neg_chi₂]
  ring

end IntegralMukaiData

end K3

end AlgebraicGeometry.Numerical
