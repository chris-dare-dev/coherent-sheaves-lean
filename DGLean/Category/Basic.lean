/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# DG categories

A dg category over a commutative ring `k` is a category whose hom-objects are
cochain complexes of `k`-modules, with a composition that is `k`-bilinear,
associative, unital, and satisfies the Leibniz rule.

## The encoding, and why it is this one

`ADR-0010` decides for a bespoke structure rather than
`EnrichedOrdinaryCategory` over `CochainComplex (ModuleCat k) ℤ`. The reason is
measured, not stylistic: at the pinned Mathlib revision
`HomologicalComplex.HasTensor` does not synthesize for the `ℤ`-indexed shape,
because the degree-`n` component of a tensor product is a coproduct over the
infinite set `{(i, j) | i + j = n}` and only the finite-fibre instances exist.
There is therefore no monoidal category available to enrich over. See
`.claude/notes/2026-08-13-dg-surface-reconnaissance.md`.

Composition is consequently given as a family of `k`-bilinear maps on the
graded pieces rather than as a chain map out of a tensor product. Only
`TensorProduct`-free data is used, so nothing here depends on the missing
instances.

## Sign convention

The Leibniz rule is
`δ (f ∘ g) = (δ f) ∘ g + (-1) ^ p • f ∘ (δ g)` for `f` of degree `p`,
which is the convention `CochainComplex.HomComplex.δ_comp` uses in Mathlib at
the pin. Any divergence from Mathlib's convention must be documented as a
divergence here rather than absorbed silently: a sign convention that is only
implicit is the most common source of silent disagreement between two dg
developments.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u w

open CategoryTheory

variable (k : Type w) [CommRing k]

/-- The data of a dg category over `k` on a type of objects `C`: a
cochain complex of `k`-modules for each pair of objects, a degree-zero
identity, and a `k`-bilinear graded composition. -/
class DGCategoryStruct (C : Type u) where
  /-- The hom-complex between two objects. -/
  dgHom : C → C → CochainComplex (ModuleCat.{v} k) ℤ
  /-- The identity, a degree-zero element of the endomorphism complex. -/
  dgId (X : C) : (dgHom X X).X 0
  /-- Graded composition, `k`-bilinear in each variable. -/
  dgComp {X Y Z : C} (p q r : ℤ) (h : p + q = r) :
    (dgHom X Y).X p →ₗ[k] (dgHom Y Z).X q →ₗ[k] (dgHom X Z).X r

/-- A dg category over `k`: the data of `DGCategoryStruct` subject to
associativity, unitality, the identity being a cocycle, and the Leibniz rule.

The differential is written `((dgHom X Y).d p q).hom` rather than through an
abbreviation: the instance is determined by the enclosing class, and an
abbreviation outside it has no instance to pin `k` down. -/
class DGCategory (C : Type u) extends DGCategoryStruct.{v} k C where
  dgComp_assoc {W X Y Z : C} (p q r pq qr pqr : ℤ)
      (hpq : p + q = pq) (hqr : q + r = qr) (hpqr : pq + r = pqr)
      (f : (dgHom W X).X p) (g : (dgHom X Y).X q) (h : (dgHom Y Z).X r) :
    dgComp pq r pqr (by omega) (dgComp p q pq hpq f g) h =
      dgComp p qr pqr (by omega) f (dgComp q r qr hqr g h)
  dgId_comp {X Y : C} (p : ℤ) (f : (dgHom X Y).X p) :
    dgComp 0 p p (zero_add p) (dgId X) f = f
  dgComp_id {X Y : C} (p : ℤ) (f : (dgHom X Y).X p) :
    dgComp p 0 p (add_zero p) f (dgId Y) = f
  dgId_cocycle (X : C) : ((dgHom X X).d 0 1).hom (dgId X) = 0
  dgComp_leibniz {X Y Z : C} (p q r r' : ℤ) (h : p + q = r) (hr : r + 1 = r')
      (f : (dgHom X Y).X p) (g : (dgHom Y Z).X q) :
    ((dgHom X Z).d r r').hom (dgComp p q r h f g) =
      dgComp (p + 1) q r' (by omega) (((dgHom X Y).d p (p + 1)).hom f) g +
        p.negOnePow • dgComp p (q + 1) r' (by omega) f
          (((dgHom Y Z).d q (q + 1)).hom g)
