/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Ring
import DGLean.Category.Basic

/-!
# The product of two dg categories

Objects are pairs, and the Hom-complex between two pairs is the degreewise
product of the two Hom-complexes, with componentwise differential, identity and
composition.

Unlike the opposite, no sign enters: the product is a limit construction and
every axiom holds componentwise. The work is entirely in exhibiting the product
complex, because the ambient `ModuleCat` product has to be built rather than
taken from an instance.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u u' w

open CategoryTheory DGCategoryStruct

variable (k : Type w) [CommRing k]

/-- The differential of the degreewise product, named separately: a proof in a
later field of a structure instance cannot see an earlier field given inline,
so `d` has to exist before `shape` and `d_comp_d'` can mention it. -/
def prodD (K L : CochainComplex (ModuleCat.{v} k) ℤ) (p q : ℤ) :
    ModuleCat.of k ((K.X p) × (L.X p)) ⟶ ModuleCat.of k ((K.X q) × (L.X q)) :=
  ModuleCat.ofHom
    (((K.d p q).hom.comp (LinearMap.fst k _ _)).prod ((L.d p q).hom.comp (LinearMap.snd k _ _)))

/-- The degreewise product of two cochain complexes of modules. -/
@[simps]
def prodComplex (K L : CochainComplex (ModuleCat.{v} k) ℤ) :
    CochainComplex (ModuleCat.{v} k) ℤ where
  X p := ModuleCat.of k ((K.X p) × (L.X p))
  d := prodD k K L
  shape p q h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply Prod.ext <;> simp [prodD, K.shape p q h, L.shape p q h]
  d_comp_d' p q r _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x, y⟩
    apply Prod.ext <;>
      simp only [prodD, ModuleCat.hom_ofHom, ModuleCat.hom_comp, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply,
        Function.prod, ModuleCat.hom_zero, LinearMap.zero_apply, Prod.fst_zero, Prod.snd_zero,
        ← ModuleCat.comp_apply, K.d_comp_d, L.d_comp_d, ModuleCat.hom_zero,
        LinearMap.zero_apply]

variable {k}
variable (C : Type u) (D : Type u') [DGCategory.{v} k C] [DGCategory.{v} k D]

/-!
## What is not here yet

`prodComplex` is proved: it is a genuine cochain complex, with the differential
and both obligations discharged. The `DGCategoryStruct` instance on `C × D` is
**not** here, and no `sorry` stands in for it.

The blocker is not the mathematics — every axiom of the product holds
componentwise and no sign enters — but the same carrier opacity that
`DGLean/Category/Instances.lean` documents, in a form the idiom there does not
fix. `((prodComplex k K L).X p)` is `ModuleCat.of k (_ × _)`, whose carrier
instance search will not see through, so the four bilinearity obligations of
`LinearMap.mk₂` cannot be discharged by `Prod.ext` and `simp`: the goal is not
recognised as living in a product type at all. Pinning the type on the lemma
works for a bare `exact` and pinning the binder works inside a field's lambda,
but `mk₂`'s obligations are neither.

The recommended fix is structural rather than tactical: build the product
Hom-complex from Mathlib's biproduct API on `HomologicalComplex` instead of
hand-rolling `ModuleCat.of (_ × _)`, so that `.X p` arrives with the projection
and injection API already attached. That is a construction change, so it is
left for a deliberate decision rather than made here — and it is a third
instance of the same underlying question the `dgHom` codomain raises on
chris-dare-dev/derived-alg-geo-lean#337.
-/


