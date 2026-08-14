/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.TStructure.Induced
import Mathlib.CategoryTheory.Triangulated.TStructure.Heart
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Bounded t-structures and t-exact functors

Both 2026 target papers state their central hypotheses in this vocabulary.
Polishchuk's inducing theorem (arXiv:2601.22994 Prop 3.4, arXiv:2607.28411
Thm A.17) asks for a *bounded* t-structure and for `Φ Φᴸ` to be *right t-exact*;
without those as definitions the hypothesis cannot be written down at all.

## Main definitions

* `TStructure.IsBounded`: every object is `t`-bounded.
* `TStructure.IsNondegenerate`: no nonzero object is `t`-coconnective in every
  degree, nor `t`-connective in every degree.
* `Functor.IsRightTExact` / `Functor.IsLeftTExact` / `Functor.IsTExact`:
  a functor's compatibility with a t-structure on its source and one on its
  target.

## Main results

* `Functor.isRightTExact_of_isLE_zero` / `Functor.isLeftTExact_of_isGE_zero`:
  for a shift-commuting functor, degree `0` suffices.
* `Functor.isTExact_of`: assemble `IsTExact` from its two halves.
* `Functor.isLeftTExact_rightAdjoint` / `Functor.isRightTExact_leftAdjoint`:
  right t-exactness of a left adjoint and left t-exactness of its right adjoint
  determine each other.
* `Functor.isRightTExact_comp` / `isLeftTExact_comp` / `isTExact_comp`, and the
  identity functor.

## Namespacing

Everything here lives under `BridgelandStabLean` so the exactness vocabulary
can evolve as a repository-owned interface without adding declarations to
Mathlib's `CategoryTheory` namespace. The slicing construction connects this
interface to the canonical t-structure through repository-owned bridge
theorems.

## Conventions

Mathlib writes the t-structure as `t.IsLE X n` (`X ∈ Dᵗ≤ⁿ`) and `t.IsGE X n`
(`X ∈ Dᵗ≥ⁿ`), and already supplies `t.plus`, `t.minus` and `t.bounded` as
`ObjectProperty C`. Boundedness of the t-structure itself is then just
`t.bounded = ⊤`, which is the definition taken here.

Right t-exactness preserves the *coconnective* half (`IsLE`), left t-exactness
the *connective* half (`IsGE`). This is the convention under which the derived
functor `Lf*` is right t-exact and `Rf_*` is left t-exact, and it is the one
both papers use.

## A correction to the issue that requested this file

Issue #146 asked for "the nondegenerate ⟺ bounded equivalence". Only one
direction is a theorem: **bounded implies nondegenerate** (`isNondegenerate_of_isBounded`).
The converse is false. A nondegenerate t-structure can have objects that are
bounded in neither direction — nondegeneracy only forbids an object from being
coconnective in *every* degree, which says nothing about an object that is
coconnective in no degree at all. The unbounded derived category of a nonzero
abelian category with its standard t-structure is nondegenerate and not bounded.
So the equivalence is not stated here, and #146's acceptance criterion should be
read as the implication.
-/

universe v v' u u'

namespace BridgelandStabLean

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated


namespace TStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

section Bounded

variable (t : TStructure C)

/-- A t-structure is **bounded** when every object of the ambient category is
`t`-bounded, i.e. lies in `Dᵗ≤ⁿ` for some `n` and in `Dᵗ≥ᵐ` for some `m`. -/
def IsBounded : Prop := ∀ X : C, t.bounded X

variable {t}

theorem isBounded_iff :
    TStructure.IsBounded t ↔ ∀ X : C, (∃ n : ℤ, t.IsGE X n) ∧ ∃ n : ℤ, t.IsLE X n :=
  Iff.rfl

/-- On a bounded t-structure every object admits a coconnective bound. -/
theorem exists_isLE (h : TStructure.IsBounded t) (X : C) : ∃ n : ℤ, t.IsLE X n := (h X).2

/-- On a bounded t-structure every object admits a connective bound. -/
theorem exists_isGE (h : TStructure.IsBounded t) (X : C) : ∃ n : ℤ, t.IsGE X n := (h X).1

end Bounded

section Nondegenerate

variable (t : TStructure C)

/-- A t-structure is **nondegenerate** when the only object lying in `Dᵗ≤ⁿ` for
every `n` is zero, and likewise for `Dᵗ≥ⁿ`. -/
structure IsNondegenerate : Prop where
  /-- An object coconnective in every degree is zero. -/
  isZero_of_forall_isLE : ∀ X : C, (∀ n : ℤ, t.IsLE X n) → IsZero X
  /-- An object connective in every degree is zero. -/
  isZero_of_forall_isGE : ∀ X : C, (∀ n : ℤ, t.IsGE X n) → IsZero X

variable {t}

/-- **Bounded implies nondegenerate.**

If `X` is coconnective in every degree then it is in particular coconnective in
degree `n - 1` for the `n` supplied by boundedness on the connective side, so
`X` lies in `Dᵗ≥ⁿ ∩ Dᵗ≤ⁿ⁻¹`, which is zero.

The converse is false; see the module docstring. -/
theorem isNondegenerate_of_isBounded (h : TStructure.IsBounded t) : TStructure.IsNondegenerate t where
  isZero_of_forall_isLE X hX := by
    obtain ⟨n, hn⟩ := exists_isGE h X
    haveI := hn
    haveI := hX (n - 1)
    exact t.isZero X (n - 1) n (by lia)
  isZero_of_forall_isGE X hX := by
    obtain ⟨n, hn⟩ := exists_isLE h X
    haveI := hn
    haveI := hX (n + 1)
    exact t.isZero X n (n + 1) (by lia)

end Nondegenerate

end TStructure

namespace Functor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- `F` is **right t-exact** for `t` on the source and `t'` on the target when it
carries `Dᵗ≤ⁿ` into `D'ᵗ'≤ⁿ` for every `n`. -/
class IsRightTExact (F : C ⥤ D) (t : TStructure C) (t' : TStructure D) : Prop where
  /-- Right t-exactness preserves the coconnective half. -/
  isLE_map : ∀ (X : C) (n : ℤ), t.IsLE X n → t'.IsLE (F.obj X) n

/-- `F` is **left t-exact** for `t` on the source and `t'` on the target when it
carries `Dᵗ≥ⁿ` into `D'ᵗ'≥ⁿ` for every `n`. -/
class IsLeftTExact (F : C ⥤ D) (t : TStructure C) (t' : TStructure D) : Prop where
  /-- Left t-exactness preserves the connective half. -/
  isGE_map : ∀ (X : C) (n : ℤ), t.IsGE X n → t'.IsGE (F.obj X) n

/-- `F` is **t-exact** when it is both left and right t-exact. -/
class IsTExact (F : C ⥤ D) (t : TStructure C) (t' : TStructure D) : Prop
    extends Functor.IsRightTExact F t t', Functor.IsLeftTExact F t t'

variable {F : C ⥤ D} {t : TStructure C} {t' : TStructure D}

theorem isLE_map_of_isRightTExact [Functor.IsRightTExact F t t'] (X : C) (n : ℤ)
    [t.IsLE X n] : t'.IsLE (F.obj X) n :=
  IsRightTExact.isLE_map X n ‹_›

theorem isGE_map_of_isLeftTExact [Functor.IsLeftTExact F t t'] (X : C) (n : ℤ)
    [t.IsGE X n] : t'.IsGE (F.obj X) n :=
  IsLeftTExact.isGE_map X n ‹_›

/-- Both halves assemble into `IsTExact`.

This is not an `instance`: `IsTExact`'s parents are already instances by
projection, so registering the converse would let instance search cycle between
them. `IsTExact.mk` has no explicit fields, so neither `⟨_, _⟩` nor
`inferInstance` reaches this — the lemma is the intended route. -/
theorem isTExact_of [Functor.IsRightTExact F t t'] [Functor.IsLeftTExact F t t'] :
    Functor.IsTExact F t t' := {}

section OfDegreeZero

/-- For a shift-commuting functor, right t-exactness at degree `0` gives it at
every degree.

The class is quantified over all `n` because a bare functor need not commute
with the shift, and then the degrees are genuinely independent. Every functor
one applies this to in practice does commute with the shift, so this is the
constructor to reach for. -/
theorem isRightTExact_of_isLE_zero [F.CommShift ℤ]
    (h : ∀ X : C, t.IsLE X 0 → t'.IsLE (F.obj X) 0) :
    Functor.IsRightTExact F t t' where
  isLE_map X n hX := by
    haveI := hX
    haveI : t.IsLE (X⟦n⟧) 0 := t.isLE_shift X n n 0 (by lia)
    haveI := h _ this
    have e : F.obj (X⟦n⟧) ≅ (F.obj X)⟦n⟧ := (F.commShiftIso n).app X
    haveI : t'.IsLE ((F.obj X)⟦n⟧) 0 := t'.isLE_of_iso e 0
    exact (t'.isLE_shift_iff (F.obj X) n n 0 (by lia)).1 this

/-- For a shift-commuting functor, left t-exactness at degree `0` gives it at
every degree. -/
theorem isLeftTExact_of_isGE_zero [F.CommShift ℤ]
    (h : ∀ X : C, t.IsGE X 0 → t'.IsGE (F.obj X) 0) :
    Functor.IsLeftTExact F t t' where
  isGE_map X n hX := by
    haveI := hX
    haveI : t.IsGE (X⟦n⟧) 0 := t.isGE_shift X n n 0 (by lia)
    haveI := h _ this
    have e : F.obj (X⟦n⟧) ≅ (F.obj X)⟦n⟧ := (F.commShiftIso n).app X
    haveI : t'.IsGE ((F.obj X)⟦n⟧) 0 := t'.isGE_of_iso e 0
    exact (t'.isGE_shift_iff (F.obj X) n n 0 (by lia)).1 this

end OfDegreeZero

section Adjunction

variable {G : D ⥤ C}

/-- **The right adjoint of a right t-exact functor is left t-exact.**

This is the closure lemma the inducing theorem actually consumes: its hypothesis
is right t-exactness of `Φ Φᴸ`, and what one has in hand is an adjunction.

The proof is the orthogonality characterization of `Dᵗ≥ⁿ`: a map `A ⟶ G Y` with
`A` in `Dᵗ≤ⁿ⁻¹` transposes to `F A ⟶ Y` with `F A` in `D'ᵗ'≤ⁿ⁻¹` and `Y` in
`D'ᵗ'≥ⁿ`, hence zero. -/
theorem isLeftTExact_rightAdjoint [G.Additive] (adj : F ⊣ G)
    [Functor.IsRightTExact F t t'] : Functor.IsLeftTExact G t' t where
  isGE_map Y n hY := by
    letI := adj.left_adjoint_additive
    haveI := hY
    rw [t.isGE_iff_orthogonal (n - 1) n (by lia)]
    intro A f hA
    haveI := hA
    haveI : t'.IsLE (F.obj A) (n - 1) := IsRightTExact.isLE_map A (n - 1) hA
    have hg : (adj.homEquiv A Y).symm f = 0 := t'.zero _ (n - 1) n (by lia)
    apply (adj.homEquiv A Y).symm.injective
    simpa only [Adjunction.homAddEquiv_symm_zero] using hg

/-- **The left adjoint of a left t-exact functor is right t-exact.**

Dual to `isLeftTExact_rightAdjoint`, through the orthogonality characterization
of `Dᵗ≤ⁿ`. -/
theorem isRightTExact_leftAdjoint [F.Additive] (adj : F ⊣ G)
    [Functor.IsLeftTExact G t' t] : Functor.IsRightTExact F t t' where
  isLE_map X n hX := by
    haveI := hX
    rw [t'.isLE_iff_orthogonal n (n + 1) (by lia)]
    intro Y g hY
    haveI := hY
    haveI : t.IsGE (G.obj Y) (n + 1) := IsLeftTExact.isGE_map Y (n + 1) hY
    have hf : adj.homEquiv X Y g = 0 := t.zero _ n (n + 1) (by lia)
    apply (adj.homEquiv X Y).injective
    simpa only [Adjunction.homAddEquiv_zero] using hf

end Adjunction

/-- A t-exact functor carries the heart into the heart. -/
theorem heart_map_of_isTExact [Functor.IsTExact F t t'] (X : C) (hX : t.heart X) :
    t'.heart (F.obj X) := by
  rw [t.mem_heart_iff] at hX
  obtain ⟨hLE, hGE⟩ := hX
  rw [t'.mem_heart_iff]
  exact ⟨IsRightTExact.isLE_map X 0 hLE, IsLeftTExact.isGE_map X 0 hGE⟩

section Comp

variable {E : Type*} [Category E] [Preadditive E] [HasZeroObject E]
  [HasShift E ℤ] [∀ n : ℤ, (shiftFunctor E n).Additive] [Pretriangulated E]
  {G : D ⥤ E} {t'' : TStructure E}


theorem isRightTExact_comp (t' : TStructure D)
    [Functor.IsRightTExact F t t'] [Functor.IsRightTExact G t' t''] :
    Functor.IsRightTExact (F ⋙ G) t t'' where
  isLE_map X n hX :=
    IsRightTExact.isLE_map (F := G) (t := t') (t' := t'') (F.obj X) n
      (IsRightTExact.isLE_map (F := F) (t := t) (t' := t') X n hX)

theorem isLeftTExact_comp (t' : TStructure D)
    [Functor.IsLeftTExact F t t'] [Functor.IsLeftTExact G t' t''] :
    Functor.IsLeftTExact (F ⋙ G) t t'' where
  isGE_map X n hX :=
    IsLeftTExact.isGE_map (F := G) (t := t') (t' := t'') (F.obj X) n
      (IsLeftTExact.isGE_map (F := F) (t := t) (t' := t') X n hX)

theorem isTExact_comp (t' : TStructure D)
    [Functor.IsTExact F t t'] [Functor.IsTExact G t' t''] :
    Functor.IsTExact (F ⋙ G) t t'' :=
  { toIsRightTExact := isRightTExact_comp (F := F) (G := G) t'
    toIsLeftTExact := isLeftTExact_comp (F := F) (G := G) t' }

end Comp

section Id

instance isRightTExact_id : Functor.IsRightTExact (𝟭 C) t t where
  isLE_map _ _ h := h

instance isLeftTExact_id : Functor.IsLeftTExact (𝟭 C) t t where
  isGE_map _ _ h := h

instance isTExact_id : Functor.IsTExact (𝟭 C) t t :=
  { toIsRightTExact := isRightTExact_id, toIsLeftTExact := isLeftTExact_id }

end Id

end Functor

end BridgelandStabLean
