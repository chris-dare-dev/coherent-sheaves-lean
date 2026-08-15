/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.DGCategory.H0

/-!
# Shifts and cones inside a dg category

`dg-enhancements-e5`. A dg category has no shift functor and no cone
construction the way a triangulated category has: it has *representability
conditions*, and this file states them.

## Why these are predicates rather than constructions

`X[n]` and `Cone f` are not built from `X` and `f`. They are objects of `C`
whose dg module of maps *in* is prescribed:

* `Y` is a shift of `X` by `n` when `dgHom W Y ≅ (dgHom W X)⟦n⟧`, naturally in
  `W`;
* `Z` is a cone on a closed degree-zero `f : X ⟶ Y` when `dgHom W Z` is the
  mapping cone of `dgHom W X → dgHom W Y`, naturally in `W`.

Both are conditions a dg category may or may not satisfy, so `IsPretriangulated`
is a class asserting that it does.

## Naturality is not an axiom here

Each condition is stated as *right composition with one fixed element is
bijective*, and that is what buys the naturality clause for free: composition
with a fixed element commutes with composition on the other side by
`dgComp_assoc`, so there is no square left to impose. Stating the iso of dg
modules directly would put a graded naturality axiom in the structure and then
oblige every witness to prove it.

## The degree conventions

`Hom^d(K, L) = ∏ₚ Hom(Kᵖ, L^{p+d})`, so with `L = X[n]` the identity-like
element of `Hom(X, X[n])` sits in degree `-n`, not `n`. That is why
`IsShiftBy.hom` has degree `-n`, and it matches Mathlib: `mappingCone.inl` is a
`Cochain F (mappingCone φ) (-1)`, the inclusion of `F[1]`.

The cone conditions are transcribed from Mathlib's `mappingCone` API rather than
rederived. `IsConeOf.δ_inl` is `mappingCone.δ_inl`, and the bijectivity clause
is the pair `mappingCone.id` (surjectivity) and `inl_fst`/`inl_snd`/`inr_fst`/
`inr_snd` (injectivity).

## The zero clause is dg-level, and stronger than it needs to be

`IsPretriangulated.exists_zero` asks for an object with `dgId Z = 0`. In a
preadditive category that is exactly "`Z` is a zero object", so the clause says
`Z⁰ C` and `H⁰ C` have a zero object on the nose.

The literature does not axiomatize this: `Cone (𝟙 X)` is contractible, so `H⁰`
gets its zero object from the cone clause alone. Contractibility is a homotopy
statement about `H⁰`, which is `dg-enhancements-e6`'s subject, and deriving the
zero object there rather than assuming it here would invert the dependency. The
clause is kept, and it costs nothing: every model in this repository has a
strict dg zero object.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct DGCategory

variable {C : Type u} [DGCategory.{v} C]

/-- Right composition with a fixed `ε : (dgHom X Y).X n`, as an additive map on
the Hom-complex from any `W`. This is the map every representability condition
below asks to be bijective. -/
def compRight (W : C) {X Y : C} {n : ℤ} (ε : (dgHom X Y).X n) (p q : ℤ) (h : p + n = q) :
    (dgHom W X).X p →+ (dgHom W Y).X q :=
  (dgComp p n q h).flip ε

@[simp]
lemma compRight_apply (W : C) {X Y : C} {n : ℤ} (ε : (dgHom X Y).X n) (p q : ℤ)
    (h : p + n = q) (f : (dgHom W X).X p) :
    compRight W ε p q h f = dgComp p n q h f ε := rfl

/-- `ε` exhibits `Y` as a shift of `X` by `n`: it is closed of degree `-n`, and
right composition with it identifies `dgHom W X` with `dgHom W Y` in every
degree, for every `W`. -/
structure IsShiftBy (X : C) (n : ℤ) (Y : C) where
  /-- The identity-like element, of degree `-n`. -/
  hom : (dgHom X Y).X (-n)
  /-- It is closed. -/
  hom_closed : ((dgHom X Y).d (-n) (-n + 1)).hom hom = 0
  /-- Right composition with it is bijective in every degree, from every object. -/
  bijective (W : C) (p q : ℤ) (h : p + -n = q) :
    Function.Bijective (compRight W hom p q h)

/-- `Z` is a cone on the closed degree-zero morphism `f : X ⟶ Y`: it carries an
inclusion `inr` of `Y` and a degree `-1` inclusion `inl` of `X` whose
differential is `f ≫ inr`, and every map into `Z` splits uniquely along the
two. -/
structure IsConeOf {X Y : C} (f : (dgHom X Y).X 0) (Z : C) where
  /-- The inclusion of `Y`. -/
  inr : (dgHom Y Z).X 0
  /-- It is closed. -/
  inr_closed : ((dgHom Y Z).d 0 1).hom inr = 0
  /-- The inclusion of `X`, of degree `-1`. -/
  inl : (dgHom X Z).X (-1)
  /-- Its differential is `f` followed by `inr`. This is `mappingCone.δ_inl`. -/
  δ_inl : ((dgHom X Z).d (-1) 0).hom inl = dgComp 0 0 0 (by omega) f inr
  /-- Every map into `Z` splits uniquely as `a ≫ inl + b ≫ inr`. -/
  bijective (W : C) (p q : ℤ) (hq : p + 1 = q) :
    Function.Bijective (fun ab : (dgHom W X).X q × (dgHom W Y).X p =>
      dgComp q (-1) p (by omega) ab.1 inl + dgComp p 0 p (by omega) ab.2 inr)

namespace IsShiftBy

/-- Every object is its own shift by zero, witnessed by the identity. The
degree-`-0` and degree-`0` Hom-groups are the same group, so no transport is
needed. -/
def self (X : C) : IsShiftBy X 0 X where
  hom := dgId X
  hom_closed := dgId_cocycle X
  bijective W p q h := by
    have hq : q = p := by omega
    subst hq
    -- `-0` and `0` are the same integer definitionally but not syntactically:
    -- the field's degree is `-n`, so `compRight` here carries `n := -0` while
    -- `dgComp_id` is stated at `0`. `exact` closes the gap and `simp` does not,
    -- so the two directions are term proofs rather than rewrites.
    refine ⟨fun a b hab => ?_, fun c => ⟨c, ?_⟩⟩
    · exact (dgComp_id q a).symm.trans (hab.trans (dgComp_id q b))
    · exact dgComp_id q c

section Inverse

variable {X Y Y' : C} {n : ℤ}

/-- The element inverse to `s.hom`. It exists because right composition with
`s.hom` is surjective onto `(dgHom Y Y).X 0`, which contains `dgId Y`. -/
noncomputable def inv (s : IsShiftBy X n Y) : (dgHom Y X).X n :=
  ((s.bijective Y n 0 (by omega)).surjective (dgId Y)).choose

/-- The defining property of `s.inv`: composing it with `s.hom` is the identity
of `Y`. -/
lemma inv_hom (s : IsShiftBy X n Y) :
    dgComp n (-n) 0 (by omega) s.inv s.hom = dgId Y :=
  ((s.bijective Y n 0 (by omega)).surjective (dgId Y)).choose_spec

/-- And the other way round. `s.hom` is not assumed invertible; this is forced,
because right composition with it is injective on `(dgHom X X).X 0` and both
sides go to `s.hom`. -/
lemma hom_inv (s : IsShiftBy X n Y) :
    dgComp (-n) n 0 (by omega) s.hom s.inv = dgId X := by
  refine (s.bijective X 0 (-n) (by omega)).injective ?_
  show dgComp 0 (-n) (-n) _ (dgComp (-n) n 0 (by omega) s.hom s.inv) s.hom =
    dgComp 0 (-n) (-n) _ (dgId X) s.hom
  rw [dgComp_assoc (-n) n (-n) 0 0 (-n) (by omega) (by omega) (by omega),
    inv_hom, dgComp_id, dgId_comp]

/-- `s.inv` is closed. The Leibniz rule at `(n, -n)` has its first term killed
by `s.hom` being closed and its second scaled by a unit, so the differential of
`s.inv` composes to zero with `s.hom` -- and right composition with `s.hom` is
injective. -/
lemma inv_closed (s : IsShiftBy X n Y) :
    ((dgHom Y X).d n (n + 1)).hom s.inv = 0 := by
  have key := dgComp_leibniz (C := C) n (-n) 0 1 (by omega) (by omega) s.inv s.hom
  rw [inv_hom, dgId_cocycle, s.hom_closed] at key
  -- `key` is now `0 = 0 + (-n).negOnePow • ((δ s.inv) ∘ s.hom)`. The sign is a
  -- unit, so the composite itself vanishes.
  have key2 : dgComp (n + 1) (-n) 1 (by omega)
      (((dgHom Y X).d n (n + 1)).hom s.inv) s.hom = 0 := by
    simpa [smul_eq_zero_iff_eq] using key.symm
  refine (s.bijective Y (n + 1) 1 (by omega)).injective ?_
  show dgComp (n + 1) (-n) 1 _ (((dgHom Y X).d n (n + 1)).hom s.inv) s.hom =
    dgComp (n + 1) (-n) 1 _ 0 s.hom
  rw [key2, map_zero, AddMonoidHom.zero_apply]

end Inverse

section Uniqueness

variable {X Y Y' : C} {n : ℤ}

/-- The comparison between two shifts of `X` by `n`: go back along one and out
along the other. -/
noncomputable def compare (s : IsShiftBy X n Y) (s' : IsShiftBy X n Y') :
    (dgHom Y Y').X 0 :=
  dgComp n (-n) 0 (by omega) s.inv s'.hom

/-- The comparison is closed, so it is a morphism of `Z⁰`. Both factors are
closed, so both Leibniz terms vanish. -/
lemma compare_mem_cocycles (s : IsShiftBy X n Y) (s' : IsShiftBy X n Y') :
    compare s s' ∈ cocycles Y Y' := by
  have key := dgComp_leibniz (C := C) n (-n) 0 1 (by omega) (by omega) s.inv s'.hom
  rw [mem_cocycles_iff, compare, key, s'.hom_closed, s.inv_closed]
  simp

/-- The two comparisons are mutually inverse, so any two shifts of `X` by `n`
are isomorphic in `Z⁰` -- and therefore in `H⁰`. This is what lets a shift
*functor* be built from the existential `IsPretriangulated.exists_shift`
without the choice mattering. -/
lemma compare_comp_compare (s : IsShiftBy X n Y) (s' : IsShiftBy X n Y') :
    dgComp 0 0 0 (by omega) (compare s s') (compare s' s) = dgId Y := by
  rw [compare, compare,
    dgComp_assoc n (-n) 0 0 (-n) 0 (by omega) (by omega) (by omega),
    ← dgComp_assoc (-n) n (-n) 0 0 (-n) (by omega) (by omega) (by omega),
    hom_inv, dgId_comp, inv_hom]

end Uniqueness

end IsShiftBy

namespace IsConeOf

variable {X Y Z : C} {f : (dgHom X Y).X 0}

/-- The composite `X ⟶ Y ⟶ Cone f` is a coboundary: `inl` is its primitive.
This is the whole content of `δ_inl`, restated so that `H⁰` can read it, and it
is what makes the cone sequence a triangle in `dg-enhancements-e6`. -/
lemma comp_inr_mem_coboundaries (hc : IsConeOf f Z) :
    dgComp 0 0 0 (by omega) f hc.inr ∈ coboundaries X Z :=
  ⟨hc.inl, hc.δ_inl⟩

/-- `inr` is a cocycle, so it is a morphism of `Z⁰`. -/
lemma inr_mem_cocycles (hc : IsConeOf f Z) : hc.inr ∈ cocycles Y Z :=
  hc.inr_closed

end IsConeOf

/-- A pretriangulated dg category: it has a zero object, a shift in every
degree, and a cone on every closed degree-zero morphism. -/
class IsPretriangulated (C : Type u) [DGCategory.{v} C] : Prop where
  /-- Some object has zero identity, so `Z⁰ C` and `H⁰ C` have a zero object. -/
  exists_zero : ∃ Z : C, dgId Z = 0
  /-- Every object has a shift in every degree. -/
  exists_shift (X : C) (n : ℤ) : ∃ Y : C, Nonempty (IsShiftBy X n Y)
  /-- Every closed degree-zero morphism has a cone. -/
  exists_cone {X Y : C} (f : (dgHom X Y).X 0) (hf : f ∈ cocycles X Y) :
    ∃ Z : C, Nonempty (IsConeOf f Z)

end CategoryTheory
