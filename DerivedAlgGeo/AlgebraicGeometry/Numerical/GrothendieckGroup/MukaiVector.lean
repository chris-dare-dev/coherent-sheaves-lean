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
`ℤ`-valued; the numerical layer is `ℚ`-valued, because `degree` lands in `ℚ`.

The two coordinates behave differently, and the difference is the whole design
of this file.  The third coordinate is **not** a hypothesis: under `[IsK3]` the
existing `chi_eq_rank_add_mukaiS` gives `χ(E) = r(E) + mukaiS E`, so
`mukaiSInt E := χ(E) − r(E)` is an integer computing `mukaiS E`, proved in
`mukaiSInt_spec`.  Only the lattice-valued first Chern class is supplied, as
`IntegralMukaiData`.

Given it, `mukaiVector E = (r E, c₁ E, mukaiSInt E)` is a genuine element of
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
  obligation of exhibiting `NS(X)` with its intersection form; that is Layer B
  work.
* `c₁` is a bare function and so is `mukaiVector`.  No additivity is assumed,
  hence none is available, and `b_spec` constrains `b` only on the image of
  `c₁` — it does not say `b` is the full intersection form.
* `isSpherical_mukaiVector_iff` is a statement about the lattice, nothing more.
  Sphericity of an *object* on a K3 means the full graded self-Ext algebra is
  `k ⊕ k[-2]` — `Hom(E,E) = k`, `Ext¹(E,E) = 0`, `Ext²(E,E) = k` — and
  recovering that from `χ(E,E) = 2` needs simplicity and Serre duality on top
  of an `Ext` this layer does not have.  Neither direction of that equivalence
  is stated here.
* `expectedDim` is a definition in the abstract file, not the theorem that a
  moduli space has that dimension.  Nothing here upgrades it.
* No connection is made *in this file* to `CategoryTheory.Triangulated.K₀`.
  That bridge is `GrothendieckGroup/Realization.lean`, which supplies the class
  map rather than constructing it.
-/

universe u v w

namespace AlgebraicGeometry.Numerical

namespace K3

open NumericalRing NumericalRingWithDual NumericalVariety

variable {A : Type u} {N : Type v} {Λ : Type w}
variable [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety 2 A N]
  [AddCommGroup Λ]

variable [IsK3 A N]

/-- The integral third Mukai coordinate, `s(E) = χ(E) − r(E)`.

This is a **definition, not supplied data**: on a K3 the existing
`chi_eq_rank_add_mukaiS` already proves `χ(E) = r(E) + mukaiS E`, so the
integrality of `mukaiS` is a theorem rather than a hypothesis. An earlier draft
of `IntegralMukaiData` carried `s` and its specification as fields; that
overstated the trust boundary, and the review that caught it is the reason this
is a `def`. -/
noncomputable def mukaiSInt (E : N) : ℤ :=
  chi (A := A) E - rank (A := A) E

/-- `mukaiSInt` computes `mukaiS`, so the third Mukai coordinate really is an
integer. Proved from `chi_eq_rank_add_mukaiS`; nothing is assumed. -/
theorem mukaiSInt_spec (E : N) :
    (mukaiSInt (A := A) E : ℚ) = mukaiS (A := A) E := by
  have h := chi_eq_rank_add_mukaiS (A := A) E
  rw [mukaiSInt]
  push_cast
  linarith

/-- The integral structure that makes the numerical Mukai pairing a pairing in
the abstract Mukai extension.

`b_spec` is where the geometry goes: it says the integral form on the supplied
lattice `Λ` computes `∫c₁(E)·c₁(F)`. The third Mukai coordinate is **not** a
field — see `mukaiSInt`, which derives it.

Note what `b_spec` does and does not say. It constrains `b` only on the image
of `c₁`; it does not assert that `b` is the full intersection form of a
geometric lattice, and `c₁` is a bare function, not an additive map. This is
deliberately weaker than a geometric lattice package.

Symmetry is **not** a field. On the image of `c₁` it is already a theorem —
`b_spec` and commutativity of `A` force it, see `b_comm_on_realized` — and
off the image it would be exactly the kind of global demand on `Λ` this
structure otherwise avoids; nothing downstream consumes it. An earlier draft
carried a `b_comm` field; the review that measured its use count (zero) is the
reason it is gone. -/
structure IntegralMukaiData (A : Type u) (N : Type v) (Λ : Type w)
    [CommRing A] [Algebra ℚ A] [AddCommGroup N] [NumericalVariety 2 A N]
    [AddCommGroup Λ] where
  /-- The first Chern class, valued in the supplied lattice. -/
  c₁ : N → Λ
  /-- The integral form on `Λ`.  Symmetry is not demanded: on the image of
  `c₁` it follows from `b_spec` (`b_comm_on_realized`), and off the image
  nothing here needs it. -/
  b : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ
  /-- The form computes the intersection number of first Chern classes. -/
  b_spec : ∀ E F : N, (b (c₁ E) (c₁ F) : ℚ)
    = degree (n := 2) (chComp (A := A) E 1 * chComp (A := A) F 1)

namespace IntegralMukaiData

variable (D : IntegralMukaiData A N Λ)

omit [IsK3 A N] in
/-- **On realized classes the form is symmetric**, with no symmetry field:
`b_spec` computes both sides as the same intersection number, `A` is
commutative, and the integer cast is injective. This is all the symmetry the
structure can see; symmetry off the image of `c₁` is neither demanded nor
available. -/
theorem b_comm_on_realized (E F : N) :
    D.b (D.c₁ E) (D.c₁ F) = D.b (D.c₁ F) (D.c₁ E) := by
  have h : (D.b (D.c₁ E) (D.c₁ F) : ℚ) = (D.b (D.c₁ F) (D.c₁ E) : ℚ) := by
    rw [D.b_spec, D.b_spec, mul_comm]
  exact_mod_cast h

/-- The Mukai vector `v(E) = (r, c₁, s)` as an element of the abstract Mukai
extension of `Λ`. Not an additive map: no additivity of `c₁` is assumed, so
none is available here. -/
noncomputable def mukaiVector (E : N) : Mukai.MukaiLattice Λ :=
  (rank (A := A) E, D.c₁ E, mukaiSInt (A := A) E)

omit [IsK3 A N] in
@[simp]
theorem mukaiVector_fst (E : N) : (D.mukaiVector E).1 = rank (A := A) E := rfl

omit [IsK3 A N] in
@[simp]
theorem mukaiVector_snd_fst (E : N) : (D.mukaiVector E).2.1 = D.c₁ E := rfl

omit [IsK3 A N] in
@[simp]
theorem mukaiVector_snd_snd (E : N) :
    (D.mukaiVector E).2.2 = mukaiSInt (A := A) E := rfl

/-- **The abstract Mukai pairing computes the numerical one.**  This is the
identification the abstract lattice file declined to make, discharged from the
supplied integral data. -/
theorem pairing_mukaiVector (E F : N) :
    (Mukai.pairing D.b (D.mukaiVector E) (D.mukaiVector F) : ℚ)
      = mukaiPairing (A := A) E F := by
  rw [mukaiVector, mukaiVector, Mukai.pairing_mk, mukaiPairing]
  push_cast
  rw [D.b_spec, mukaiSInt_spec, mukaiSInt_spec]

/-- The self-pairing of a Mukai vector computes `mukaiSelfPairing`. -/
theorem selfPairing_mukaiVector (E : N) :
    (Mukai.selfPairing D.b (D.mukaiVector E) : ℚ)
      = mukaiSelfPairing (A := A) E := by
  rw [Mukai.selfPairing_eq_pairing, D.pairing_mukaiVector, mukaiPairing_self]

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

This is `Mukai.IsSpherical` — a property of the *lattice vector*, meaning
`⟪v,v⟫ = -2`.  It is not sphericity of the object, which on a K3 asks that the
graded self-Ext algebra be `k ⊕ k[-2]` (so also `Ext¹(E,E) = 0`) and which
would need simplicity and Serre duality to recover from `χ(E,E) = 2`. -/
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
