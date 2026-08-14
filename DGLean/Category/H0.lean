/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DGLean.Category.Basic

/-!
# Cocycles, coboundaries, and `Z⁰` of a dg category

The degree-zero cocycles of a dg category form an ordinary category on the same
objects, and the coboundaries sit inside them as an additive subgroup. `H⁰` is
the quotient; this file builds everything the quotient needs.

Both halves rest on the Leibniz rule, at three different pairs of degrees:

* `(0, 0)` — composition of cocycles is a cocycle, so `Z⁰` is a category;
* `(0, -1)` — a cocycle composed with a coboundary is a coboundary;
* `(-1, 0)` — a coboundary composed with a cocycle is a coboundary.

The last two are what make composition descend to `H⁰`. They are the reason the
Leibniz rule is an axiom of `DGCategory` rather than a lemma about a special
case, and the `Const` example in `DGLean/Category/Instances.lean` — whose
differential is zero — tests none of them.

## A wrinkle in the degrees

`dgComp_leibniz` states the shifted degrees as `p + 1`, and those are dependent
arguments: `simp only [zero_add]` cannot normalise `0 + 1` to `1` in a goal
without breaking the motive. Hypotheses are therefore restated at the shifted
degree — they typecheck directly, the degrees being definitionally equal —
rather than rewriting the goal.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

open CategoryTheory DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

/-- The degree-zero cocycles from `X` to `Y`. -/
def cocycles (X Y : C) : AddSubgroup ((dgHom X Y).X 0) :=
  ((dgHom X Y).d 0 1).hom.ker

/-- The degree-zero coboundaries from `X` to `Y`. -/
def coboundaries (X Y : C) : AddSubgroup ((dgHom X Y).X 0) :=
  ((dgHom X Y).d (-1) 0).hom.range

lemma mem_cocycles_iff {X Y : C} (f : (dgHom X Y).X 0) :
    f ∈ cocycles X Y ↔ ((dgHom X Y).d 0 1).hom f = 0 := Iff.rfl

lemma mem_coboundaries_iff {X Y : C} (f : (dgHom X Y).X 0) :
    f ∈ coboundaries X Y ↔ ∃ h, ((dgHom X Y).d (-1) 0).hom h = f := Iff.rfl

/-- Every coboundary is a cocycle: this is `d ∘ d = 0`. -/
lemma coboundaries_le_cocycles (X Y : C) : coboundaries X Y ≤ cocycles X Y := by
  rintro _ ⟨h, rfl⟩
  rw [mem_cocycles_iff, ← AddCommGrpCat.comp_apply, (dgHom X Y).d_comp_d]
  simp

/-- A cocycle composed with a coboundary is a coboundary. Leibniz at `(0, -1)`:
the `δf` term vanishes because `f` is closed, and the sign is `+1`. -/
lemma comp_coboundary_mem {X Y Z : C} {f : (dgHom X Y).X 0} (hf : f ∈ cocycles X Y)
    {b : (dgHom Y Z).X 0} (hb : b ∈ coboundaries Y Z) :
    dgComp 0 0 0 (by omega) f b ∈ coboundaries X Z := by
  obtain ⟨h, rfl⟩ := hb
  refine ⟨dgComp 0 (-1) (-1) (by omega) f h, ?_⟩
  have hf' : ((dgHom X Y).d 0 (0 + 1)).hom f = 0 := hf
  have key := dgComp_leibniz (C := C) 0 (-1) (-1) 0 (by omega) (by omega) f h
  rw [key, hf', map_zero, AddMonoidHom.zero_apply, zero_add, Int.negOnePow_zero, one_smul]
  -- only `-1 + 1` versus `0` in dependent positions remains; they are defeq
  rfl

/-- A coboundary composed with a cocycle is a coboundary. Leibniz at `(-1, 0)`:
the `δg` term vanishes because `g` is closed, so the sign never matters. -/
lemma coboundary_comp_mem {X Y Z : C} {b : (dgHom X Y).X 0} (hb : b ∈ coboundaries X Y)
    {g : (dgHom Y Z).X 0} (hg : g ∈ cocycles Y Z) :
    dgComp 0 0 0 (by omega) b g ∈ coboundaries X Z := by
  obtain ⟨h, rfl⟩ := hb
  refine ⟨dgComp (-1) 0 (-1) (by omega) h g, ?_⟩
  have hg' : ((dgHom Y Z).d 0 (0 + 1)).hom g = 0 := hg
  have key := dgComp_leibniz (C := C) (-1) 0 (-1) 0 (by omega) (by omega) h g
  rw [key, hg', map_zero, smul_zero, add_zero]
  rfl

variable (C)

/-- Objects of `Z⁰`. A type synonym, so the ordinary category structure does not
attach itself to `C`. -/
def Z0 : Type u := C

namespace Z0

/-- The underlying object of `C`. -/
def of (X : Z0 C) : C := X

variable {C}

/-- Composition of cocycles is a cocycle: Leibniz at `(0, 0)`, with both
differential terms vanishing. -/
lemma comp_mem {X Y Z : C} {f : (dgHom X Y).X 0} (hf : f ∈ cocycles X Y)
    {g : (dgHom Y Z).X 0} (hg : g ∈ cocycles Y Z) :
    dgComp 0 0 0 (by omega) f g ∈ cocycles X Z := by
  have hf' : ((dgHom X Y).d 0 (0 + 1)).hom f = 0 := hf
  have hg' : ((dgHom Y Z).d 0 (0 + 1)).hom g = 0 := hg
  have key := dgComp_leibniz (C := C) 0 0 0 1 (by omega) (by omega) f g
  rw [mem_cocycles_iff, key, hf', hg', map_zero, AddMonoidHom.zero_apply, map_zero,
    smul_zero, add_zero]

instance category : Category.{v} (Z0 C) where
  Hom X Y := cocycles (of C X) (of C Y)
  id X := ⟨dgId (of C X), dgId_cocycle _⟩
  comp f g := ⟨dgComp 0 0 0 (by omega) f.1 g.1, comp_mem f.2 g.2⟩
  id_comp f := Subtype.ext (dgId_comp 0 f.1)
  comp_id f := Subtype.ext (dgComp_id 0 f.1)
  assoc f g h := Subtype.ext (dgComp_assoc 0 0 0 0 0 0 rfl rfl rfl f.1 g.1 h.1)

/-! The two computation rules below are stated through `Subtype.val` on the
ascribed subgroup type: `X ⟶ Y` in `Z0 C` *is* `cocycles _ _`, but only
definitionally, so the anonymous coercion does not fire on the `⟶` form. -/

@[simp]
lemma id_val (X : Z0 C) :
    ((𝟙 X : X ⟶ X) : cocycles (of C X) (of C X)).val = dgId (of C X) := rfl

@[simp]
lemma comp_val {X Y Z : Z0 C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((f ≫ g : X ⟶ Z) : cocycles (of C X) (of C Z)).val =
      dgComp 0 0 0 (by omega)
        ((f : cocycles (of C X) (of C Y)).val) ((g : cocycles (of C Y) (of C Z)).val) := rfl

end Z0
