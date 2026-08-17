/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.BoundedHomotopyCategory
import DerivedAlgGeo.CategoryTheory.Triangulated.GrothendieckGroup.EulerForm
import Mathlib.Algebra.Category.FGModuleCat.Abelian

/-!
# A concrete `HomFiniteBounded` category (#543)

`EulerForm.lean` introduced `HomFiniteBounded` as supplied data and its own
docstring recorded that no concrete `k`-linear pretriangulated category
existed in this repository for it to be proved about. This file removes that
caveat: the **bounded homotopy category** `Kᵇ(C)` of any Hom-finite `k`-linear
additive category `C` satisfies it, and `Kᵇ(FGModuleCat k)` — bounded
complexes of finite-dimensional vector spaces up to homotopy — is the named
concrete witness.

## Why the homotopy category and not the derived category

For `Dᵇ` the finiteness of Hom-spaces is a theorem *about the localization*,
classically proved through semisimplicity (`Dᵇ(k‑vect) ≃ ℤ`-graded vector
spaces) — machinery neither Mathlib nor this repository has. For `Kᵇ` every
statement is elementary: a chain map out of a complex supported in a finite
window is determined by finitely many components, each in a Hom-finite
Hom-space, and homotopy classes are a quotient of that. Over a field the two
categories are in fact equivalent (bounded complexes of vector spaces are
K-projective), but **that equivalence is neither used nor claimed here**; the
witness stands on its own as an honest `k`-linear pretriangulated category.

## What this file proves and what it does not

* `CochainComplex.module_finite_hom`: a chain-map space out of a strictly
  bounded complex is a finite `k`-module when `C` is Hom-finite. No bound on
  the target is needed.
* `subsingleton_hom_of_le_lt_ge` / `..of_ge_lt_le`: chain maps between
  complexes with disjoint support windows vanish.
* `instHomFiniteBoundedBounded`: `Kᵇ(C)` satisfies `HomFiniteBounded k` for
  Hom-finite `k`-linear `C`; `homFiniteBounded_fgModuleCat` instantiates it
  at `C := FGModuleCat k`.
* **Not** proved: anything about `Dᵇ`, any comparison of `chiHom` on `Kᵇ`
  with an Euler characteristic of homology, or `IsRiemannRoch` for anything.
  The obligation #513 named is discharged in the satisfiability sense only:
  the class has a genuine model, so the Euler-form chain is not vacuous.
-/

universe w v u

open CategoryTheory Limits Pretriangulated ZeroObject

namespace CategoryTheory.Triangulated

variable (k : Type w) [DivisionRing k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

namespace HomFiniteWitness

open HomologicalComplex

/-- Restriction of a chain map to its components in a finite window,
as a linear map. -/
def homRestrict (K L : CochainComplex C ℤ) (s : Finset ℤ) :
    (K ⟶ L) →ₗ[k] Π i : s, (K.X i ⟶ L.X i) where
  toFun f i := f.f i
  map_add' f g := by ext i; simp
  map_smul' a f := by ext i; simp

/-- A chain-map space out of a strictly bounded complex is a finite
`k`-module when the base category is Hom-finite. The target complex needs no
bound. -/
lemma module_finite_hom [∀ X Y : C, Module.Finite k (X ⟶ Y)]
    (K L : CochainComplex C ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    Module.Finite k (K ⟶ L) := by
  refine FiniteDimensional.of_injective (homRestrict k K L (Finset.Icc a b))
    (fun f g h ↦ ?_)
  ext i
  by_cases hi : i ∈ Finset.Icc a b
  · exact congrFun h ⟨i, hi⟩
  · simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · exact (K.isZero_of_isStrictlyGE a i hi).eq_of_src _ _
    · exact (K.isZero_of_isStrictlyLE b i hi).eq_of_src _ _

/-- Chain maps from a complex bounded above into one bounded strictly below
it vanish. -/
lemma subsingleton_hom_of_le_lt_ge (K L : CochainComplex C ℤ) (b c : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyGE c] (h : b < c) :
    Subsingleton (K ⟶ L) := by
  constructor
  intro f g
  ext i
  by_cases hi : c ≤ i
  · exact (K.isZero_of_isStrictlyLE b i (by omega)).eq_of_src _ _
  · exact (L.isZero_of_isStrictlyGE c i (by omega)).eq_of_tgt _ _

/-- Chain maps from a complex bounded below into one bounded strictly above
it vanish. -/
lemma subsingleton_hom_of_ge_lt_le (K L : CochainComplex C ℤ) (a d : ℤ)
    [K.IsStrictlyGE a] [L.IsStrictlyLE d] (h : d < a) :
    Subsingleton (K ⟶ L) := by
  constructor
  intro f g
  ext i
  by_cases hi : a ≤ i
  · exact (L.isZero_of_isStrictlyLE d i (by omega)).eq_of_tgt _ _
  · exact (K.isZero_of_isStrictlyGE a i (by omega)).eq_of_src _ _

variable [HasZeroObject C] [HasBinaryBiproducts C]

set_option backward.isDefEq.respectTransparency false in
/-- The hom-space `X ⟶ Y⟦i⟧` in `Kᵇ(C)`, identified `k`-linearly with a
hom-space between quotient images of honest complexes, along the two
inclusion/quotient `CommShift` isomorphisms and the defining equalities of
the boundedness property. Both instance fields below factor through this. -/
noncomputable def boundedHomEquiv (X Y : HomotopyCategory.Bounded C) (i : ℤ)
    {KX KY : CochainComplex C ℤ}
    (hX : (HomotopyCategory.quotient C (.up ℤ)).obj KX = X.obj)
    (hY : (HomotopyCategory.quotient C (.up ℤ)).obj KY = Y.obj) :
    (X ⟶ Y⟦i⟧) ≃ₗ[k]
      ((HomotopyCategory.quotient C (.up ℤ)).obj KX ⟶
        (HomotopyCategory.quotient C (.up ℤ)).obj (KY⟦i⟧)) :=
  (InducedCategory.homLinearEquiv (R := k)).trans
    (Linear.homCongr k (eqToIso hX).symm
      ((((HomotopyCategory.bounded C).ι.commShiftIso i).app Y) ≪≫
        (shiftFunctor (HomotopyCategory C (.up ℤ)) i).mapIso (eqToIso hY).symm ≪≫
          (((HomotopyCategory.quotient C (.up ℤ)).commShiftIso i).app KY).symm))

end HomFiniteWitness

open HomFiniteWitness in
/-- **`Kᵇ` of a Hom-finite linear category is `HomFiniteBounded`.** Every
hom-space is a quotient of a chain-map space out of a bounded complex, and
disjoint support windows kill all chain maps once the shift is large. -/
instance instHomFiniteBoundedBounded
    [∀ X Y : C, Module.Finite k (X ⟶ Y)] :
    HomFiniteBounded k (HomotopyCategory.Bounded C) where
  finite X Y i := by
    obtain ⟨KX, hKX, hX⟩ := (HomotopyCategory.bounded_iff_exists X.obj).1 X.property
    obtain ⟨KY, hKY, hY⟩ := (HomotopyCategory.bounded_iff_exists Y.obj).1 Y.property
    obtain ⟨⟨a, _⟩, ⟨b, _⟩⟩ := hKX
    have : Module.Finite k (KX ⟶ KY⟦i⟧) := module_finite_hom k KX (KY⟦i⟧) a b
    have : Module.Finite k
        ((HomotopyCategory.quotient C (.up ℤ)).obj KX ⟶
          (HomotopyCategory.quotient C (.up ℤ)).obj (KY⟦i⟧)) :=
      Module.Finite.of_surjective
        ((HomotopyCategory.quotient C (.up ℤ)).mapLinearMap (R := k))
        (HomotopyCategory.quotient C (.up ℤ)).map_surjective
    exact Module.Finite.equiv (boundedHomEquiv k X Y i hX hY).symm
  support_finite X Y := by
    obtain ⟨KX, hKX, hX⟩ := (HomotopyCategory.bounded_iff_exists X.obj).1 X.property
    obtain ⟨KY, hKY, hY⟩ := (HomotopyCategory.bounded_iff_exists Y.obj).1 Y.property
    obtain ⟨⟨a, _⟩, ⟨b, _⟩⟩ := hKX
    obtain ⟨⟨c, _⟩, ⟨d, _⟩⟩ := hKY
    refine Set.Finite.subset (Set.finite_Icc (c - b) (d - a)) (fun i hi ↦ ?_)
    simp only [Function.mem_support, ne_eq] at hi
    by_contra hout
    apply hi
    simp only [Set.mem_Icc, not_and_or, not_le] at hout
    have : (KY⟦i⟧).IsStrictlyGE (c - i) := KY.isStrictlyGE_shift c i (c - i) (by omega)
    have : (KY⟦i⟧).IsStrictlyLE (d - i) := KY.isStrictlyLE_shift d i (d - i) (by omega)
    have hsub : Subsingleton (KX ⟶ KY⟦i⟧) := by
      rcases hout with hout | hout
      · exact subsingleton_hom_of_le_lt_ge KX (KY⟦i⟧) b (c - i) (by omega)
      · exact subsingleton_hom_of_ge_lt_le KX (KY⟦i⟧) a (d - i) (by omega)
    have : Subsingleton
        ((HomotopyCategory.quotient C (.up ℤ)).obj KX ⟶
          (HomotopyCategory.quotient C (.up ℤ)).obj (KY⟦i⟧)) :=
      (HomotopyCategory.quotient C (.up ℤ)).map_surjective.subsingleton
    have : Subsingleton (X ⟶ Y⟦i⟧) :=
      (boundedHomEquiv k X Y i hX hY).toEquiv.subsingleton
    simp [Module.finrank_zero_of_subsingleton]

section FGModuleCat

variable (k : Type u) [Field k]

instance fgModuleCat_hom_finite (V W : FGModuleCat k) : Module.Finite k (V ⟶ W) :=
  Module.Finite.equiv
    ((ModuleCat.homLinearEquiv (M := V.obj) (N := W.obj) (S := k)).symm.trans
      (InducedCategory.homLinearEquiv (R := k)).symm)

/-- **The named concrete witness for #543**: bounded complexes of
finite-dimensional `k`-vector spaces up to homotopy form a `k`-linear
pretriangulated category with finite-dimensional Hom-spaces and finite
Ext-amplitude. The Euler-form chain of `EulerForm.lean` is therefore not
vacuous: `HomFiniteBounded` has a model. -/
theorem homFiniteBounded_fgModuleCat :
    HomFiniteBounded k (HomotopyCategory.Bounded (FGModuleCat k)) :=
  inferInstance

end FGModuleCat

end CategoryTheory.Triangulated
