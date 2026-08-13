/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation.Deformation.SkewedStability
import BridgelandStabLean.Foundation.Slicing.IntervalStrictness
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Strict maximal destabilizing quotients in owner thin intervals

This module introduces the strict finite-length hypothesis and the witness
structure used by the owner Harder--Narasimhan recursion. It remains on the
Mathlib-only side of the ownership boundary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u'

namespace BridgelandStabLean.Foundation.Deformation

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ] {κ : K₀ C →+ Λ}

/-- Every object of an owner thin interval is strict Artinian and strict
Noetherian. This is the chain-condition hypothesis used by strict MDQ
selection and the finite-length HN recursion. -/
def ThinStrictFiniteLength (σ : StabilityCondition.WithClassMap C κ)
    (a b : ℝ) [Fact (a < b)] [Fact (b - a ≤ 1)] : Prop :=
  ∀ Y : σ.slicing.IntervalCat C a b,
    IsStrictArtinianObject Y ∧ IsStrictNoetherianObject Y

/-- Ordinary finite length of every thin-interval object implies owner strict
finite length. -/
theorem ThinStrictFiniteLength.of_finiteLength
    (σ : StabilityCondition.WithClassMap C κ) {a b : ℝ}
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    (h : ∀ Y : σ.slicing.IntervalCat C a b,
      IsArtinianObject Y ∧ IsNoetherianObject Y) :
    ThinStrictFiniteLength C σ a b := by
  intro Y
  letI : IsArtinianObject Y := (h Y).1
  letI : IsNoetherianObject Y := (h Y).2
  exact ⟨isStrictArtinianObject_of_isArtinianObject,
    isStrictNoetherianObject_of_isNoetherianObject⟩

/-- A strict maximal destabilizing quotient in an owner thin interval. Its
phase is minimal among nonzero semistable strict quotients, and equality
forces the competing quotient to factor through it. -/
structure IsStrictMDQ
    (σ : StabilityCondition.WithClassMap C κ) {a b : ℝ}
    (F : SkewedStabilityFunction C κ σ.slicing a b)
    [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X B : σ.slicing.IntervalCat C a b} (q : X ⟶ B) : Prop where
  /-- The quotient map is a strict epimorphism. -/
  strictEpi : IsStrictEpi q
  /-- The quotient is nonzero as an ambient object. -/
  nonzero : ¬IsZero B.obj
  /-- The quotient is semistable at its skewed phase. -/
  semistable : F.IsSemistable B.obj (F.phase B.obj)
  /-- The quotient has minimal phase, with the expected rigidity at equal
  phase. -/
  minimal :
    ∀ {B' : σ.slicing.IntervalCat C a b} (q' : X ⟶ B'), IsStrictEpi q' →
      ¬IsZero B'.obj → F.IsSemistable B'.obj (F.phase B'.obj) →
      F.phase B.obj ≤ F.phase B'.obj ∧
        (F.phase B'.obj = F.phase B.obj → ∃ t : B ⟶ B', q' = q ≫ t)

namespace IsStrictMDQ

variable {σ : StabilityCondition.WithClassMap C κ} {a b : ℝ}
variable {F : SkewedStabilityFunction C κ σ.slicing a b}
variable [Fact (a < b)] [Fact (b - a ≤ 1)]
variable {X B : σ.slicing.IntervalCat C a b} {q : X ⟶ B}

/-- A strict MDQ is epic. -/
theorem epi (hq : IsStrictMDQ C σ F q) : Epi q := hq.strictEpi.epi

/-- A strict MDQ is strict. -/
theorem strict (hq : IsStrictMDQ C σ F q) : IsStrict q := hq.strictEpi.strict

/-- The minimal-phase part of the strict MDQ universal property. -/
theorem phase_le (hq : IsStrictMDQ C σ F q)
    {B' : σ.slicing.IntervalCat C a b} (q' : X ⟶ B')
    (hq' : IsStrictEpi q') (hB' : ¬IsZero B'.obj)
    (hss : F.IsSemistable B'.obj (F.phase B'.obj)) :
    F.phase B.obj ≤ F.phase B'.obj :=
  (hq.minimal q' hq' hB' hss).1

/-- Equal phase forces a semistable strict quotient to factor through a
strict MDQ. -/
theorem factor_of_phase_eq (hq : IsStrictMDQ C σ F q)
    {B' : σ.slicing.IntervalCat C a b} (q' : X ⟶ B')
    (hq' : IsStrictEpi q') (hB' : ¬IsZero B'.obj)
    (hss : F.IsSemistable B'.obj (F.phase B'.obj))
    (hphase : F.phase B'.obj = F.phase B.obj) :
    ∃ t : B ⟶ B', q' = q ≫ t :=
  (hq.minimal q' hq' hB' hss).2 hphase

/-- A strict MDQ of a non-semistable source has a genuinely nonzero kernel
subobject. -/
theorem kernelSubobject_ne_bot_of_not_semistable
    (hq : IsStrictMDQ C σ F q)
    (hns : ¬F.IsSemistable X.obj (F.phase X.obj)) :
    kernelSubobject q ≠ ⊥ := by
  intro hK
  have hkerZero : IsZero (kernelSubobject q : σ.slicing.IntervalCat C a b) := by
    rw [hK]
    exact (isZero_zero (σ.slicing.IntervalCat C a b)).of_iso
      Subobject.botCoeIsoZero
  haveI : Mono q := Preadditive.mono_of_kernel_zero <|
    zero_of_source_iso_zero _ (hkerZero.of_iso (kernelSubobjectIso q).symm).isoZero
  haveI : IsIso q := IsStrictEpi.isIso hq.strictEpi
  let e : X.obj ≅ B.obj :=
    (Slicing.IntervalCat.ι (C := C) (s := σ.slicing) a b).mapIso (asIso q)
  have hphase : F.phase B.obj = F.phase X.obj := F.phase_iso e.symm
  exact hns (hphase ▸ hq.semistable.ofIso e.symm)

end IsStrictMDQ

end BridgelandStabLean.Foundation.Deformation
