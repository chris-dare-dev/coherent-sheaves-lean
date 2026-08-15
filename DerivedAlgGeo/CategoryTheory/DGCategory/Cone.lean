/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import DerivedAlgGeo.CategoryTheory.DGCategory.H0
import DerivedAlgGeo.CategoryTheory.DGCategory.Shift

/-!
# Composition with a cocycle, and the hom-complex a cone must have

`dg-enhancements-e5` (#376), second piece. Two things.

First, composing with a **closed** degree-zero element is a map of complexes.
For `f` a cocycle in `dgHom X Y`, post-composition `dgHom W X ⟶ dgHom W Y` and
pre-composition `dgHom Y W ⟶ dgHom X W` both commute with the differential on
the nose. Each is one application of `dgComp_leibniz` in which one term dies
because `f` is closed and the other carries the sign `(-1) ^ 0`. Closedness is
used exactly once in each proof, and it is the only place it is used.

Second, `coneHom` — the hom-complex that a cone of `f` is obliged to have.

## Which variance, and why it is not a matter of taste

`Cone f` should be `X⟦1⟧ ⊕ Y`, so in `C^dg` its covariant hom-complex is

`Hom(W, Cone f) ^ p = Hom(W, X) ^ (p + 1) ⊕ Hom(W, Y) ^ p`

and its contravariant one is `Hom(X, W) ^ (p - 1) ⊕ Hom(Y, W) ^ p`. Mathlib's
`homotopyCofiber φ` for `φ : F ⟶ G` satisfies `X i ≅ F.X j ⊞ G.X i` whenever
`c.Rel i j` — degree `p + 1` on the left summand, `p` on the right. That is the
**covariant** shape, on the nose.

So `coneHom` is defined covariantly, as `CochainComplex.mappingCone` of
post-composition, and #376's instruction to consume `MappingCone` rather than
re-derive it is met literally rather than approximately. Writing the
contravariant version instead would have meant rebuilding the twisted complex
by hand and proving `d ∘ d = 0` from Leibniz — the same theorem Mathlib already
has, in a form that does not match it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct

namespace DGCategory

variable {C : Type u} [DGCategory.{v} C]

/-! ### Post-composition with a cocycle -/

/-- Post-composition with a degree-zero element, degreewise. -/
def postcompHom {X Y : C} (f : (dgHom X Y).X 0) (W : C) (p : ℤ) :
    (dgHom W X).X p ⟶ (dgHom W Y).X p :=
  AddCommGrpCat.ofHom ((dgComp p 0 p (add_zero p)).flip f)

/-- Pre-composition with a degree-zero element, degreewise. -/
def precompHom {X Y : C} (f : (dgHom X Y).X 0) (W : C) (p : ℤ) :
    (dgHom Y W).X p ⟶ (dgHom X W).X p :=
  AddCommGrpCat.ofHom (dgComp 0 p p (zero_add p) f)

/-- `postcompHom` applied to an element: `g` then `f`. -/
lemma postcompHom_apply {X Y : C} (f : (dgHom X Y).X 0) (W : C) (p : ℤ)
    (g : (dgHom W X).X p) :
    (postcompHom f W p).hom g = dgComp p 0 p (add_zero p) g f := rfl

/-- `precompHom` applied to an element: `f` then `g`. -/
lemma precompHom_apply {X Y : C} (f : (dgHom X Y).X 0) (W : C) (p : ℤ)
    (g : (dgHom Y W).X p) :
    (precompHom f W p).hom g = dgComp 0 p p (zero_add p) f g := rfl

/-- **Post-composition with a cocycle is a chain map.** Leibniz at `(p, 0)`
gives `δ (g · f) = g · (δ f) + (-1) ^ 0 • (δ g) · f`; the first term dies
because `f` is closed, and the sign on the second is `+1`. -/
lemma postcompHom_comm {X Y : C} {f : (dgHom X Y).X 0} (hf : f ∈ cocycles X Y)
    (W : C) (p p' : ℤ) (hp : p + 1 = p') :
    postcompHom f W p ≫ (dgHom W Y).d p p' = (dgHom W X).d p p' ≫ postcompHom f W p' := by
  subst hp
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro g
  have hd : ((dgHom X Y).d 0 (0 + 1)).hom f = 0 := by rw [zero_add]; exact hf
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
    postcompHom_apply]
  rw [dgComp_leibniz p 0 p (p + 1) (add_zero p) rfl g f]
  simp only [Int.negOnePow_zero, one_smul, add_eq_right]
  rw [hd, map_zero]

/-- **Pre-composition with a cocycle is a chain map.** Leibniz at `(0, p)`
gives `δ (f · g) = f · (δ g) + (-1) ^ p • (δ f) · g`, and the second term dies
because `f` is closed. -/
lemma precompHom_comm {X Y : C} {f : (dgHom X Y).X 0} (hf : f ∈ cocycles X Y)
    (W : C) (p p' : ℤ) (hp : p + 1 = p') :
    precompHom f W p ≫ (dgHom X W).d p p' = (dgHom Y W).d p p' ≫ precompHom f W p' := by
  subst hp
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro g
  have hd : ((dgHom X Y).d 0 (0 + 1)).hom f = 0 := by rw [zero_add]; exact hf
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply,
    precompHom_apply]
  rw [dgComp_leibniz 0 p p (p + 1) (zero_add p) rfl f g]
  simp only [add_eq_left]
  rw [hd, map_zero, AddMonoidHom.zero_apply, smul_zero]

/-- Post-composition with a cocycle, as a morphism of cochain complexes. -/
noncomputable def postcomp {X Y : C} {f : (dgHom X Y).X 0} (hf : f ∈ cocycles X Y) (W : C) :
    dgHom W X ⟶ dgHom W Y where
  f p := postcompHom f W p
  comm' p p' hp := postcompHom_comm hf W p p' hp

/-- Pre-composition with a cocycle, as a morphism of cochain complexes. -/
noncomputable def precomp {X Y : C} {f : (dgHom X Y).X 0} (hf : f ∈ cocycles X Y) (W : C) :
    dgHom Y W ⟶ dgHom X W where
  f p := precompHom f W p
  comm' p p' hp := precompHom_comm hf W p p' hp

/-- The degreewise components of `postcomp` are `postcompHom`. -/
lemma postcomp_f {X Y : C} {f : (dgHom X Y).X 0} (hf : f ∈ cocycles X Y) (W : C) (p : ℤ) :
    (postcomp hf W).f p = postcompHom f W p := rfl

/-- The degreewise components of `precomp` are `precompHom`. -/
lemma precomp_f {X Y : C} {f : (dgHom X Y).X 0} (hf : f ∈ cocycles X Y) (W : C) (p : ℤ) :
    (precomp hf W).f p = precompHom f W p := rfl

/-! ### The hom-complex a cone is obliged to have -/

/-- The covariant hom-complex of a cone of `f`: Mathlib's mapping cone of
post-composition with `f`. Its degree `p` is `(dgHom W X).X (p + 1) ⊞
(dgHom W Y).X p`, which is what `Hom(W, X⟦1⟧ ⊕ Y)` has to be. -/
noncomputable def coneHom {X Y : C} {f : (dgHom X Y).X 0} (hf : f ∈ cocycles X Y) (W : C) :
    CochainComplex AddCommGrpCat.{v} ℤ :=
  CochainComplex.mappingCone (postcomp hf W)

/-- The degreewise description of `coneHom`, inherited from Mathlib rather than
restated: degree `p` is the biproduct of `(dgHom W X).X (p + 1)` and
`(dgHom W Y).X p`. -/
noncomputable def coneHomXIso {X Y : C} {f : (dgHom X Y).X 0} (hf : f ∈ cocycles X Y)
    (W : C) (p p' : ℤ) (hp : p + 1 = p') :
    (coneHom hf W).X p ≅ (dgHom W X).X p' ⊞ (dgHom W Y).X p :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (postcomp hf W) p p' hp

end DGCategory

end CategoryTheory
