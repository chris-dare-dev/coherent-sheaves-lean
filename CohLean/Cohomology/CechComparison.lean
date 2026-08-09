/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Cohomology.AffineCech
import CohLean.Cohomology.CechBicomplex
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.GroupTheory.FreeAbelianGroup

/-!
# The Cech-to-derived comparison boundary

This file supplies the first reusable layer of the comparison between Cech cohomology and
derived-functor sheaf cohomology.

Mathlib defines the Cech complex and `Sheaf.H`, but it does not define the cohomology of that
complex, a comparison morphism, or a theorem identifying the two.  We therefore:

* name the homology objects of the Cech complex;
* prove the natural isomorphism `F.H' n T ≃+ F.H n` for a terminal object `T`;
* record the standard acyclicity hypothesis on all finite intersections in a cover;
* package, as a proposition, the exact conclusion a Cech-to-derived comparison theorem must
  produce; and
* prove the positive-degree comparison for the singleton cover of a terminal object, as well as
  the general implication from Cech exactness to derived vanishing once comparison is available.

The remaining nontrivial-cover step is deliberately not hidden behind an axiom: one still has to
prove that `IsCechAcyclicCover U F` implies `CechComputesDerivedCohomologyAt U F n`.  The standard
proof uses an augmented Cech resolution and its Leray spectral sequence.

`CohLean.Cohomology.CechBicomplex` now constructs that bicomplex from an explicit injective
resolution, retains its augmentation, totalizes its column filtration, constructs the spectral
sequence, identifies its entries with `Cech^p(U, I^q)`, computes the initial page as the homology of
an adjacent filtration layer, and names the total-complex abutment candidate.  Three precise
boundaries remain:

* this Mathlib revision has no `EnoughInjectives` instance for abelian sheaves, so an injective
  resolution cannot yet be chosen from the current hypotheses;
* the filtration-layer homology still has to be identified with the appropriate products of
  `F.H' q` and then collapsed under `IsCechAcyclicFor`; and
* Mathlib's `SpectralSequence` structure records pages and page-to-page homology isomorphisms but
  has no convergence or abutment field, so comparison with the named total complex must be proved
  as a separate theorem.
-/

universe i h a v u

open CategoryTheory Limits

namespace CategoryTheory

section CechCohomology

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
  {A : Type a} [Category A] [Abelian A] [HasProducts.{i} A]
  {ι : Type i}

/-- Degree-`n` Cech cohomology is the homology of Mathlib's explicit Cech cochain complex. -/
noncomputable abbrev cechCohomology (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ) : A :=
  ((cechComplexFunctor U).obj P).homology n

/-- Exactness of the explicit Cech complex at `n` kills degree-`n` Cech cohomology. -/
lemma cechCohomology_isZero_of_exactAt (U : ι → C) (P : Cᵒᵖ ⥤ A) (n : ℕ)
    (h : ((cechComplexFunctor U).obj P).ExactAt n) :
    IsZero (cechCohomology U P n) :=
  h.isZero_homology

end CechCohomology

namespace Sheaf

variable {C : Type u} [Category.{a} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{a}]
  [HasExt.{h} (Sheaf J AddCommGrpCat.{a})]
  {ι : Type a}

/-- The free abelian sheaf represented by `X`; this is the first argument of `F.H' n X`. -/
noncomputable abbrev freeAbelianYonedaSheaf (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{a}] (X : C) :
    Sheaf J AddCommGrpCat.{a} :=
  (presheafToSheaf J _).obj (yoneda.obj X ⋙ AddCommGrpCat.free)

/-- At a terminal object, the free abelian representable presheaf is the constant presheaf
`ULift ℤ`. -/
noncomputable def freeAbelianYonedaPresheafIsoConstant {T : C} (hT : IsTerminal T) :
    yoneda.obj T ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)) :=
  NatIso.ofComponents (fun X ↦ by
    letI : Unique (X.unop ⟶ T) :=
      { default := hT.from X.unop
        uniq := fun _ ↦ hT.hom_ext _ _ }
    exact ((FreeAbelianGroup.uniqueEquiv (X.unop ⟶ T)).trans
      AddEquiv.ulift.symm).toAddCommGrpIso) (fun {X Y} f ↦ by
        letI : Unique ((yoneda.obj T).obj X) :=
          { default := hT.from X.unop
            uniq := fun _ ↦ hT.hom_ext _ _ }
        letI : Unique (X.unop ⟶ T) :=
          { default := hT.from X.unop
            uniq := fun _ ↦ hT.hom_ext _ _ }
        letI : Unique ((yoneda.obj T).obj Y) :=
          { default := hT.from Y.unop
            uniq := fun _ ↦ hT.hom_ext _ _ }
        letI : Unique (Y.unop ⟶ T) :=
          { default := hT.from Y.unop
            uniq := fun _ ↦ hT.hom_ext _ _ }
        apply AddCommGrpCat.hom_ext
        apply FreeAbelianGroup.lift_ext
        intro x
        change ULift.up ((FreeAbelianGroup.uniqueEquiv _)
            (FreeAbelianGroup.map _ (FreeAbelianGroup.of x))) =
          ULift.up ((FreeAbelianGroup.uniqueEquiv _) (FreeAbelianGroup.of x))
        rw [FreeAbelianGroup.map_of_apply]
        apply ULift.ext
        change (1 : ℤ) = (FreeAbelianGroup.lift fun _ ↦ 1) (FreeAbelianGroup.of x)
        rw [FreeAbelianGroup.lift_apply_of])

/-- Sheafified form of `freeAbelianYonedaPresheafIsoConstant`. -/
noncomputable def freeAbelianYonedaSheafIsoConstant {T : C} (hT : IsTerminal T) :
    freeAbelianYonedaSheaf J T ≅
      (constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift ℤ)) := by
  simpa only [freeAbelianYonedaSheaf, constantSheaf, Functor.comp_obj] using
    (presheafToSheaf J _).mapIso (freeAbelianYonedaPresheafIsoConstant hT)

/-- The missing terminal-object natural isomorphism noted in Mathlib's sheaf-cohomology API:
cohomology represented by a terminal object agrees with global sheaf cohomology. -/
noncomputable def HPrimeNatIsoH {T : C} (hT : IsTerminal T) (n : ℕ) :
    cohomologyPresheafFunctor J n ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{h}).obj (Opposite.op T) ≅
        cohomologyFunctor J n := by
  change (Abelian.extFunctor n).obj
      (Opposite.op (freeAbelianYonedaSheaf J T)) ≅
    (Abelian.extFunctor n).obj (Opposite.op
      ((constantSheaf J AddCommGrpCat.{a}).obj (AddCommGrpCat.of (ULift ℤ))))
  exact (Abelian.extFunctor n).mapIso
    (freeAbelianYonedaSheafIsoConstant (J := J) hT).symm.op

/-- Pointwise additive equivalence supplied by `HPrimeNatIsoH`. -/
noncomputable def HPrimeAddEquivH {T : C} (hT : IsTerminal T)
    (F : Sheaf J AddCommGrpCat.{a}) (n : ℕ) : F.H' n T ≃+ F.H n :=
  ((HPrimeNatIsoH (J := J) hT n).app F).addCommGroupIsoToAddEquiv

/-- Vanishing of terminal-object cohomology in the `H'` presentation is equivalent to vanishing
of global sheaf cohomology. -/
lemma subsingleton_HPrime_iff_H {T : C} (hT : IsTerminal T)
    (F : Sheaf J AddCommGrpCat.{a}) (n : ℕ) :
    Subsingleton (F.H' n T) ↔ Subsingleton (F.H n) :=
  (HPrimeAddEquivH (J := J) hT F n).toEquiv.subsingleton_congr

variable [HasFiniteProducts C]

/-- A cover is Cech-acyclic for `F` when `F` has no positive cohomology on any nonempty finite
intersection occurring in its Cech nerve.

Coverage itself is intentionally separate: `U` is just the family used to form the Cech complex.
Use `IsCechAcyclicCover` for the complete Leray hypothesis. -/
def IsCechAcyclicFor (U : ι → C) (F : Sheaf J AddCommGrpCat.{a}) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (x : Fin (n + 1) → ι),
    Subsingleton (F.H' q (∏ᶜ fun k ↦ U (x k)))

/-- The standard Leray hypothesis for a Cech-to-derived comparison: `U` covers the terminal
object and `F` is acyclic on every nonempty finite intersection in the Cech nerve. -/
def IsCechAcyclicCover (U : ι → C) (F : Sheaf J AddCommGrpCat.{a}) : Prop :=
  J.CoversTop U ∧ IsCechAcyclicFor U F

/-- The conclusion of a degreewise Cech-to-derived comparison theorem.

This is a proposition so downstream vanishing results need not depend on a particular choice of
isomorphism.  It is not an assumption installed globally and it contains no unproved declaration. -/
def CechComputesDerivedCohomologyAt (U : ι → C) (F : Sheaf J AddCommGrpCat.{a})
    (n : ℕ) : Prop :=
  Nonempty ((cechCohomology U F.obj n : AddCommGrpCat.{a}) ≃+ F.H n)

/-- A cover computes derived sheaf cohomology when it does so in every degree. -/
def CechComputesDerivedCohomology (U : ι → C) (F : Sheaf J AddCommGrpCat.{a}) : Prop :=
  ∀ n, CechComputesDerivedCohomologyAt U F n

/-- The positive-degree comparison for the singleton cover by a terminal object.  Here the Cech
complex is contractible, while `IsCechAcyclicFor` says precisely that the derived group vanishes;
`HPrimeAddEquivH` identifies its terminal-object and global presentations. -/
theorem cechComputesDerivedCohomologyAt_singleton_terminal_of_pos
    {T : C} (hT : IsTerminal T) (F : Sheaf J AddCommGrpCat.{a})
    (n : ℕ) (hn : 0 < n)
    (hacyclic : IsCechAcyclicFor (fun _ : PUnit ↦ T) F) :
    CechComputesDerivedCohomologyAt (fun _ : PUnit ↦ T) F n := by
  let V : C := ∏ᶜ fun _ : Fin 1 ↦ T
  have hV : IsTerminal V := IsTerminal.ofUniqueHom
    (fun X ↦ Pi.lift fun _ ↦ hT.from X)
    (fun X f ↦ Pi.hom_ext f (Pi.lift fun _ ↦ hT.from X) fun k ↦ hT.hom_ext _ _)
  have hHPrime := hacyclic n hn 0 (fun _ ↦ PUnit.unit)
  change Subsingleton (F.H' n V) at hHPrime
  have hH : Subsingleton (F.H n) :=
    (subsingleton_HPrime_iff_H (J := J) hV F n).mp hHPrime
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (by omega : n ≠ 0)
  have hexact := cechComplex_exactAt_succ_of_isTerminal
    (i₀ := PUnit.unit) (fun _ : PUnit ↦ T) hT (𝟙 T) F.obj m
  have hzero : IsZero
      (cechCohomology (fun _ : PUnit ↦ T) F.obj (m + 1)) :=
    hexact.isZero_homology
  letI : Subsingleton
      (cechCohomology (fun _ : PUnit ↦ T) F.obj (m + 1) : AddCommGrpCat.{a}) :=
    AddCommGrpCat.subsingleton_of_isZero hzero
  letI : Subsingleton (F.H (m + 1)) := hH
  letI : Unique
      (cechCohomology (fun _ : PUnit ↦ T) F.obj (m + 1) : AddCommGrpCat.{a}) :=
    { default := 0
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  letI : Unique (F.H (m + 1)) :=
    { default := 0
      uniq := fun _ ↦ Subsingleton.elim _ _ }
  exact ⟨AddEquiv.ofUnique⟩

/-- If Cech cohomology computes derived sheaf cohomology in degree `n`, exactness of the explicit
Cech complex at `n` implies vanishing of derived sheaf cohomology there. -/
lemma subsingleton_H_of_cech_exactAt (U : ι → C) (F : Sheaf J AddCommGrpCat.{a})
    (n : ℕ) (hcomparison : CechComputesDerivedCohomologyAt U F n)
    (hexact : ((cechComplexFunctor U).obj F.obj).ExactAt n) :
    Subsingleton (F.H n) := by
  let e := hcomparison.some
  have hzero : IsZero (cechCohomology U F.obj n) :=
    cechCohomology_isZero_of_exactAt U F.obj n hexact
  letI : Subsingleton (cechCohomology U F.obj n : AddCommGrpCat.{a}) :=
    AddCommGrpCat.subsingleton_of_isZero hzero
  exact ⟨fun x y ↦ e.symm.injective (Subsingleton.elim _ _)⟩

end Sheaf

end CategoryTheory
