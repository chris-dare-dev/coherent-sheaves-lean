/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DGLean.Category.Basic

/-!
# `Z⁰` of a dg category

The degree-zero cocycles of a dg category form an ordinary category on the same
objects. This is the first half of the passage `H⁰` that the whole track is
named for: `Z⁰` collects the closed degree-zero morphisms, and `H⁰` will divide
them by the exact ones.

Composition is closed under the cocycle condition because of the Leibniz rule
at `p = q = 0`: `δ (f ∘ g) = (δf) ∘ g + f ∘ (δg)`, and both terms vanish when
`f` and `g` are cocycles. That is the only place an axiom of `DGCategory` is
used here, and it is the reason the Leibniz rule is an axiom of the structure
rather than a lemma about a special case.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

open CategoryTheory DGCategoryStruct DGCategory

variable (C : Type u) [DGCategory.{v} C]

/-- Objects of `Z⁰`. A type synonym, so the ordinary category structure does
not attach itself to `C`. -/
def Z0 : Type u := C

namespace Z0

/-- The underlying object of `C`. -/
def of (X : Z0 C) : C := X

variable {C}

/-- A morphism of `Z⁰`: a degree-zero cocycle. -/
structure Hom (X Y : Z0 C) where
  /-- The underlying degree-zero element of the Hom-complex. -/
  val : (dgHom (of C X) (of C Y)).X 0
  /-- It is a cocycle. -/
  isCocycle : ((dgHom (of C X) (of C Y)).d 0 1).hom val = 0

attribute [simp] Hom.isCocycle

@[ext]
lemma Hom.ext {X Y : Z0 C} {f g : Hom X Y} (h : f.val = g.val) : f = g := by
  cases f; cases g; simpa using h

variable (C)

instance category : Category.{v} (Z0 C) where
  Hom X Y := Hom X Y
  id X := ⟨dgId (of C X), dgId_cocycle _⟩
  comp {X Y Z} f g :=
    ⟨dgComp 0 0 0 (by omega) f.val g.val, by
      -- The Leibniz axiom states the shifted degrees as `p + 1`, and those are
      -- dependent arguments, so they cannot be normalised by rewriting. State
      -- the two cocycle conditions at `0 + 1` instead; it is the same statement.
      have hf : ((dgHom (of C X) (of C Y)).d 0 (0 + 1)).hom f.val = 0 := f.isCocycle
      have hg : ((dgHom (of C Y) (of C Z)).d 0 (0 + 1)).hom g.val = 0 := g.isCocycle
      have h := dgComp_leibniz (C := C) 0 0 0 1 (by omega) (by omega) f.val g.val
      rw [h, hf, hg]
      rw [map_zero, AddMonoidHom.zero_apply, map_zero, smul_zero, add_zero]⟩
  id_comp {X Y} f := Hom.ext (dgId_comp 0 f.val)
  comp_id {X Y} f := Hom.ext (dgComp_id 0 f.val)
  assoc {W X Y Z} f g h := Hom.ext (dgComp_assoc 0 0 0 0 0 0 rfl rfl rfl f.val g.val h.val)

@[simp]
lemma id_val (X : Z0 C) : (𝟙 X : Hom X X).val = dgId (of C X) := rfl

@[simp]
lemma comp_val {X Y Z : Z0 C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).val = dgComp 0 0 0 (by omega) f.val g.val := rfl

end Z0
