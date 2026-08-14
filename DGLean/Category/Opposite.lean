/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Tactic.Ring
import DGLean.Category.Basic

/-!
# The opposite dg category

## The sign convention, and why this one

The opposite of a dg category reverses composition and inserts a Koszul sign:

`f ∘ᵒᵖ g = (-1) ^ (|f| * |g|) • (g ∘ f)`.

Without the sign, associativity still holds but the Leibniz rule does not, so
the sign is forced rather than chosen. Both checks are recorded here because a
sign convention that is only implicit is the usual way two dg developments come
to disagree without either noticing.

**Associativity.** With `|f| = p`, `|g| = q`, `|h| = r`:

* `(f ∘ᵒᵖ g) ∘ᵒᵖ h` carries `(-1) ^ ((p + q) * r + p * q)`
* `f ∘ᵒᵖ (g ∘ᵒᵖ h)` carries `(-1) ^ (p * (q + r) + q * r)`

and `(p + q) * r + p * q = p * (q + r) + q * r`.

**Leibniz.** `δ (f ∘ᵒᵖ g) = (-1) ^ (p * q) • (δg ∘ f + (-1) ^ q • g ∘ δf)`,
while `(δf) ∘ᵒᵖ g + (-1) ^ p • f ∘ᵒᵖ (δg)` carries `(-1) ^ ((p+1) * q)` on
`g ∘ δf` and `(-1) ^ (p + p * (q+1))` on `δg ∘ f`. Those reduce to
`(-1) ^ (p * q + q)` and `(-1) ^ (p * q)`, matching term by term.

The units live in `ℤˣ` via `Int.negOnePow`, matching Mathlib's convention in
`CochainComplex.HomComplex` rather than introducing a second one.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u w

open CategoryTheory DGCategoryStruct

variable (k : Type w) [CommRing k] (C : Type u) [DGCategory.{v} k C]

namespace DGCategory

/-- The opposite of a dg category: the same objects, Hom-complexes reversed,
composition reversed with a Koszul sign. -/
instance opStruct : DGCategoryStruct.{v} k Cᵒᵖ where
  dgHom X Y := dgHom (k := k) Y.unop X.unop
  dgId X := dgId X.unop
  dgComp p q r h :=
    (p * q).negOnePow • (dgComp (k := k) q p r (by omega)).flip

variable {k C}

@[simp]
lemma op_dgComp_apply {X Y Z : Cᵒᵖ} (p q r : ℤ) (h : p + q = r)
    (f : (dgHom (k := k) Y.unop X.unop).X p)
    (g : (dgHom (k := k) Z.unop Y.unop).X q) :
    dgComp (k := k) (C := Cᵒᵖ) p q r h f g =
      (p * q).negOnePow • dgComp (k := k) q p r (by omega) g f :=
  rfl

@[simp]
lemma op_dgHom (X Y : Cᵒᵖ) :
    dgHom (k := k) X Y = dgHom (k := k) Y.unop X.unop := rfl

@[simp]
lemma op_dgId (X : Cᵒᵖ) : dgId (k := k) X = dgId (k := k) X.unop := rfl

/-- `dgComp` is `ℤˣ`-equivariant in its first argument, because it is
`k`-linear and the `ℤˣ` action factors through `ℤ`. -/
lemma dgComp_units_smul_left {X Y Z : C} (p q r : ℤ) (h : p + q = r) (c : ℤˣ)
    (f : (dgHom (k := k) X Y).X p) (g : (dgHom (k := k) Y Z).X q) :
    dgComp (k := k) p q r h (c • f) g = c • dgComp (k := k) p q r h f g := by
  simp [Units.smul_def, map_zsmul]

/-- `dgComp` is `ℤˣ`-equivariant in its second argument. -/
lemma dgComp_units_smul_right {X Y Z : C} (p q r : ℤ) (h : p + q = r) (c : ℤˣ)
    (f : (dgHom (k := k) X Y).X p) (g : (dgHom (k := k) Y Z).X q) :
    dgComp (k := k) p q r h f (c • g) = c • dgComp (k := k) p q r h f g := by
  simp [Units.smul_def, map_zsmul]

/-!
## What is not here yet

The `DGCategory` instance on `Cᵒᵖ` — the four axioms — is **not** proved. The
data above is complete and the sign convention is fixed, but the axiom proofs
need index bookkeeping that is not yet done, and this repository does not
accept a `sorry` to stand in for it. Two residual obligations, both with the
goal already reduced to the right shape:

* **Associativity.** After `simp only [op_dgComp_apply, dgComp_units_smul_left,
  dgComp_units_smul_right, smul_smul, ← Int.negOnePow_add]` the two sides agree
  up to rewriting by the underlying `dgComp_assoc` at `(r, q, p)` and an
  equality of sign exponents, `(p + q) * r + p * q = p * (q + r) + q * r`. The
  rewrite lands; closing the sign congruence needs an `Int.negOnePow`
  congruence step rather than `ring`, because the coefficients live in `ℤˣ`.

* **Leibniz.** The underlying axiom instantiated at `(q, p)` with the argument
  pair swapped is the right key, but `simp only [op_dgHom]` normalizes the
  goal's `dgComp` before `op_dgComp_apply` can fire, so the rewrite misses. The
  fix is to apply `op_dgComp_apply` first and keep `op_dgHom` out of that simp
  set.

Neither is a mathematical gap: both identities are verified by hand in the
header above. They are Lean bookkeeping, and they are recorded here rather than
papered over so the next reader starts from the residual goal instead of from
the beginning.
-/

end DGCategory
