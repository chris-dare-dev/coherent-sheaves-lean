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

universe v u

open CategoryTheory DGCategoryStruct

variable (C : Type u) [DGCategory.{v} C]

namespace DGCategory

/-- The opposite of a dg category: the same objects, Hom-complexes reversed,
composition reversed with a Koszul sign. -/
instance opStruct : DGCategoryStruct.{v} Cᵒᵖ where
  dgHom X Y := dgHom Y.unop X.unop
  dgId X := dgId X.unop
  dgComp p q r h :=
    (p * q).negOnePow • (dgComp q p r (by omega)).flip

variable {C}

@[simp]
lemma op_dgComp_apply {X Y Z : Cᵒᵖ} (p q r : ℤ) (h : p + q = r)
    (f : (dgHom Y.unop X.unop).X p)
    (g : (dgHom Z.unop Y.unop).X q) :
    dgComp (C := Cᵒᵖ) p q r h f g =
      (p * q).negOnePow • dgComp q p r (by omega) g f :=
  rfl

@[simp]
lemma op_dgHom (X Y : Cᵒᵖ) :
    dgHom X Y = dgHom Y.unop X.unop := rfl

@[simp]
lemma op_dgId (X : Cᵒᵖ) : dgId X = dgId X.unop := rfl

/-- `dgComp` is `ℤˣ`-equivariant in its first argument, because it is
additive and the `ℤˣ` action factors through `ℤ`. -/
lemma dgComp_units_smul_left {X Y Z : C} (p q r : ℤ) (h : p + q = r) (c : ℤˣ)
    (f : (dgHom X Y).X p) (g : (dgHom Y Z).X q) :
    dgComp p q r h (c • f) g = c • dgComp p q r h f g := by
  simp [Units.smul_def, map_zsmul]

/-- `dgComp` is `ℤˣ`-equivariant in its second argument. -/
lemma dgComp_units_smul_right {X Y Z : C} (p q r : ℤ) (h : p + q = r) (c : ℤˣ)
    (f : (dgHom X Y).X p) (g : (dgHom Y Z).X q) :
    dgComp p q r h f (c • g) = c • dgComp p q r h f g := by
  simp [Units.smul_def, map_zsmul]

/-- A morphism of `AddCommGrpCat` commutes with the `ℤˣ` action, which factors
through `ℤ`. Stated so the sign bookkeeping below can stay in `ℤˣ` instead of
dropping to `ℤ` and back. -/
lemma hom_units_smul {M N : AddCommGrpCat.{v}} (φ : M ⟶ N) (c : ℤˣ) (x : M) :
    φ.hom (c • x) = c • φ.hom x := by
  simp [Units.smul_def, map_zsmul]

/-- The opposite dg category. -/
instance op : DGCategory.{v} Cᵒᵖ where
  dgComp_assoc p q r pq qr pqr hpq hqr hpqr f g h := by
    subst hpq; subst hqr; subst hpqr
    simp only [op_dgComp_apply, dgComp_units_smul_left, dgComp_units_smul_right, smul_smul,
      ← Int.negOnePow_add]
    rw [show (p + q) * r + p * q = p * (q + r) + q * r by ring,
      dgComp_assoc r q p (q + r) (p + q) (p + q + r) (by ring) (by ring) (by ring)]
  dgId_comp p f := by
    simp only [op_dgComp_apply, zero_mul, Int.negOnePow_zero, one_smul]
    exact dgComp_id p f
  dgComp_id p f := by
    simp only [op_dgComp_apply, mul_zero, Int.negOnePow_zero, one_smul]
    exact dgId_comp p f
  dgId_cocycle X := dgId_cocycle X.unop
  dgComp_leibniz p q r r' h hr f g := by
    subst h
    have key := dgComp_leibniz q p (p + q) r' (by ring) (by omega) g f
    simp only [op_dgComp_apply]
    rw [hom_units_smul]
    simp only [op_dgHom]
    rw [key, smul_add, smul_smul, smul_smul, ← Int.negOnePow_add, ← Int.negOnePow_add,
      show p + p * (q + 1) = p * q + 2 * p by ring,
      show ((p * q + 2 * p).negOnePow) = (p * q).negOnePow by
        rw [Int.negOnePow_add, Int.negOnePow_two_mul, mul_one],
      show (p + 1) * q = p * q + q by ring, add_comm]

end DGCategory
