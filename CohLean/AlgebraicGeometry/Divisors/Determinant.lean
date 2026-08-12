/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Coh.Abelian.Basic
import CohLean.AlgebraicGeometry.Divisors.PicardGroup
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Determinant lines and first Chern classes

Mathlib v4.32.1 has exterior powers of modules, but it has no exterior-power construction for
sheaves of modules.  This file therefore separates the algebraic local model from the global
descent datum:

* `Module.topExteriorPower R n` is the actual top exterior power of the free rank-`n`
  `R`-module, and has rank one;
* `Scheme.Modules.FiniteLocallyFreeData E n` records a fixed-rank locally free atlas for a
  module sheaf;
* `Scheme.Modules.DeterminantData E` records that atlas together with a chosen global
  invertible sheaf realizing the descended top exterior power and an explicit tensor inverse;
* direct-sum and short-exact compatibility are expressed by explicit comparison isomorphisms,
  from which additivity of the resulting first Chern class follows;
* the coherent-sheaf API only applies to coherent objects carrying this explicit finite locally
  free determinant data.  It deliberately does not claim that every coherent sheaf has a
  finite locally free resolution.

This is the same explicit-certificate design used for effective Cartier divisors: unsupported
global existence claims do not hide behind typeclass inference, while downstream work gets a
stable determinant/`c₁` interface whose hypotheses are visible in theorem types.
-/

open CategoryTheory Limits

universe u

namespace Module

variable (R : Type u) [CommRing R]

/-- The algebraic local model for the determinant of a free rank-`n` module. -/
abbrev topExteriorPower (n : ℕ) := ⋀[R]^n (Fin n → R)

/-- The top exterior power of a free rank-`n` module has rank one. -/
theorem finrank_topExteriorPower [Nontrivial R] (n : ℕ) :
    finrank R (topExteriorPower R n) = 1 := by
  rw [exteriorPower.finrank_eq]
  simp

end Module

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

/-- A fixed-rank locally free atlas for a module sheaf.

Unlike Mathlib's `SheafOfModules.IsLocallyFree`, this records one natural number `n` and requires
every local free basis in the chosen cover to be indexed by `Fin n`. -/
structure FiniteLocallyFreeData (E : X.Modules) (n : ℕ) where
  localGenerators :
    SheafOfModules.LocalGeneratorsData.{u}
      (show SheafOfModules X.ringCatSheaf from E)
  isLocallyFreeData : localGenerators.IsLocallyFreeData
  rankEquiv : ∀ i, Nonempty ((localGenerators.generators i).I ≃ Fin n)

namespace FiniteLocallyFreeData

/-- Fixed-rank locally free data in particular proves upstream local freeness. -/
theorem isLocallyFree {E : X.Modules} {n : ℕ}
    (D : FiniteLocallyFreeData E n) :
    SheafOfModules.IsLocallyFree.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from E) := by
  letI : D.localGenerators.IsLocallyFreeData := D.isLocallyFreeData
  exact D.localGenerators.isLocallyFree

/-- Transport a fixed-rank locally free atlas across an isomorphism. -/
noncomputable def ofIso {E F : X.Modules} {n : ℕ}
    (D : FiniteLocallyFreeData E n) (e : E ≅ F) :
    FiniteLocallyFreeData F n := by
  letI : D.localGenerators.IsLocallyFreeData := D.isLocallyFreeData
  exact
    { localGenerators := D.localGenerators.ofIso e
      isLocallyFreeData := inferInstance
      rankEquiv := D.rankEquiv }

end FiniteLocallyFreeData

/-- An invertible sheaf together with an explicit tensor inverse.

Keeping the inverse in the data gives a canonical element of the repository's scheme-level
Picard group, whose elements are units in the monoid of invertible-sheaf isomorphism classes. -/
structure LineBundleData (X : Scheme.{u}) where
  line : X.Modules
  inverse : X.Modules
  lineIsInvertible :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from line)
  inverseIsInvertible :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from inverse)
  tensorInverseIso :
    tensorObj line inverse ≅ SheafOfModules.unit X.ringCatSheaf

namespace LineBundleData

instance (L : LineBundleData X) :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L.line) :=
  L.lineIsInvertible

instance (L : LineBundleData X) :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L.inverse) :=
  L.inverseIsInvertible

/-- The underlying sheaf of a line bundle is coherent. -/
theorem isCoherent (L : LineBundleData X) : IsCoherent X L.line := by
  letI : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules.{u} X.ringCatSheaf from L.line) := L.lineIsInvertible
  exact SheafOfModules.IsInvertible.isFinitePresentation
    (M := (show SheafOfModules.{u} X.ringCatSheaf from L.line))

/-- The rank-one locally free atlas carried by an invertible sheaf. -/
noncomputable def finiteLocallyFree (L : LineBundleData X) :
    FiniteLocallyFreeData L.line 1 := by
  letI : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules.{u} X.ringCatSheaf from L.line) := L.lineIsInvertible
  let q := (SheafOfModules.IsInvertible.exists_rankOneData
    (M := (show SheafOfModules.{u} X.ringCatSheaf from L.line))).choose
  have hq := (SheafOfModules.IsInvertible.exists_rankOneData
    (M := (show SheafOfModules.{u} X.ringCatSheaf from L.line))).choose_spec.1
  have hrank := (SheafOfModules.IsInvertible.exists_rankOneData
    (M := (show SheafOfModules.{u} X.ringCatSheaf from L.line))).choose_spec.2
  exact
    { localGenerators := q
      isLocallyFreeData := hq
      rankEquiv := fun i => by
        letI : Unique (q.generators i).I :=
          { default := Classical.choice (hrank i).1
            uniq := fun a => (hrank i).2.elim a _ }
        exact ⟨Equiv.ofUnique _ _⟩ }

section Unit

local instance : Category X.Opens :=
  inferInstanceAs (Category (TopologicalSpace.Opens X))

private theorem unitIsInvertible (X : Scheme.{u}) :
    SheafOfModules.IsInvertible.{u, u, u}
      (SheafOfModules.unit X.ringCatSheaf) := by
  let q₀ := (SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf) PUnit.{u + 1}).localGeneratorsData
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅
      SheafOfModules.unit X.ringCatSheaf := SheafOfModules.freePUnitIsoUnit
  letI : q₀.IsLocallyFreeData := by
    dsimp [q₀]
    infer_instance
  exact
    { exists_rankOneData := ⟨q₀.ofIso e, inferInstance, by
        intro i
        change Nonempty PUnit ∧ Subsingleton PUnit
        exact ⟨inferInstance, inferInstance⟩⟩ }

/-- The structure sheaf with itself as tensor inverse. -/
noncomputable def unit (X : Scheme.{u}) : LineBundleData X where
  line := SheafOfModules.unit X.ringCatSheaf
  inverse := SheafOfModules.unit X.ringCatSheaf
  lineIsInvertible := unitIsInvertible X
  inverseIsInvertible := unitIsInvertible X
  tensorInverseIso := tensorUnitLeftIso _

end Unit

/-- The Picard-group element represented by a line bundle with its recorded inverse. -/
noncomputable def toPic (L : LineBundleData X) : Pic X :=
  Pic.mkOfTensorInverse L.line L.inverse L.tensorInverseIso

@[simp]
theorem coe_toPic (L : LineBundleData X) :
    (L.toPic : PicardClass X) = PicardClass.mk L.line :=
  rfl

/-- Isomorphic line representatives determine the same Picard-group element. -/
theorem toPic_eq_of_iso (L M : LineBundleData X) (e : L.line ≅ M.line) :
    L.toPic = M.toPic := by
  apply Units.ext
  change PicardClass.mk L.line = PicardClass.mk M.line
  exact (PicardClass.mk_eq_mk_iff _ _).2 ⟨e⟩

private noncomputable def tensorIso
    {L₁ L₂ M₁ M₂ : X.Modules} (e : L₁ ≅ L₂) (f : M₁ ≅ M₂) :
    tensorObj L₁ M₁ ≅ tensorObj L₂ M₂ where
  hom := tensorHom e.hom f.hom
  inv := tensorHom e.inv f.inv
  hom_inv_id := by
    rw [tensorHom_comp_tensorHom, e.hom_inv_id, f.hom_inv_id,
      tensorHom_id_id]
  inv_hom_id := by
    rw [tensorHom_comp_tensorHom, e.inv_hom_id, f.inv_hom_id,
      tensorHom_id_id]

/-- The inverse line bundle, with the two recorded representatives exchanged. -/
noncomputable def dual (L : LineBundleData X) : LineBundleData X where
  line := L.inverse
  inverse := L.line
  lineIsInvertible := L.inverseIsInvertible
  inverseIsInvertible := L.lineIsInvertible
  tensorInverseIso := tensorCommIso L.inverse L.line ≪≫ L.tensorInverseIso

/-- Tensor product of explicitly invertible line bundles. -/
noncomputable def tensor (L M : LineBundleData X) : LineBundleData X where
  line := tensorObj L.line M.line
  inverse := tensorObj M.inverse L.inverse
  lineIsInvertible := isInvertible_tensorObj L.line M.line
  inverseIsInvertible := isInvertible_tensorObj M.inverse L.inverse
  tensorInverseIso :=
    tensorAssocIso L.line M.line (tensorObj M.inverse L.inverse) ≪≫
      tensorIso (Iso.refl L.line)
        ((tensorAssocIso M.line M.inverse L.inverse).symm ≪≫
          tensorIso M.tensorInverseIso (Iso.refl L.inverse) ≪≫
          tensorUnitLeftIso L.inverse) ≪≫
      L.tensorInverseIso

@[simp]
theorem toPic_dual (L : LineBundleData X) :
    L.dual.toPic = L.toPic⁻¹ := by
  apply Units.ext
  rfl

@[simp]
theorem toPic_tensor (L M : LineBundleData X) :
    (L.tensor M).toPic = L.toPic * M.toPic := by
  apply Units.ext
  change PicardClass.mk (tensorObj L.line M.line) =
    PicardClass.mk L.line * PicardClass.mk M.line
  exact (PicardClass.mk_mul_mk L.line M.line).symm

end LineBundleData

/-- Determinant data for a finite locally free sheaf.

The `topExteriorPower` field is a chosen global descent of the algebraic local top exterior
powers supplied by `finiteLocallyFree`.  It is explicit because the current Mathlib sheaf API
does not construct exterior powers or their descent automatically. -/
structure DeterminantData (E : X.Modules) where
  rank : ℕ
  finiteLocallyFree : FiniteLocallyFreeData E rank
  topExteriorPower : LineBundleData X

namespace DeterminantData

variable {E F G : X.Modules}

/-- The determinant line. -/
abbrev line (D : DeterminantData E) : X.Modules :=
  D.topExteriorPower.line

/-- The recorded inverse determinant line. -/
abbrev inverse (D : DeterminantData E) : X.Modules :=
  D.topExteriorPower.inverse

/-- Determinant data proves that the underlying sheaf is locally free. -/
theorem isLocallyFree (D : DeterminantData E) :
    SheafOfModules.IsLocallyFree.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from E) :=
  D.finiteLocallyFree.isLocallyFree

/-- Transport determinant data across an isomorphism of finite locally free sheaves. -/
noncomputable def ofIso (D : DeterminantData E) (e : E ≅ F) :
    DeterminantData F where
  rank := D.rank
  finiteLocallyFree := D.finiteLocallyFree.ofIso e
  topExteriorPower := D.topExteriorPower

/-- The first Chern class of an explicitly determinant-equipped finite locally free sheaf. -/
noncomputable def firstChernClass (D : DeterminantData E) : Pic X :=
  D.topExteriorPower.toPic

/-- Additive notation for the first Chern class. -/
noncomputable def firstChernClassAdd (D : DeterminantData E) :
    Additive (Pic X) :=
  Additive.ofMul D.firstChernClass

@[simp]
theorem firstChernClass_ofIso (D : DeterminantData E) (e : E ≅ F) :
    (D.ofIso e).firstChernClass = D.firstChernClass :=
  rfl

@[simp]
theorem firstChernClassAdd_ofIso (D : DeterminantData E) (e : E ≅ F) :
    (D.ofIso e).firstChernClassAdd = D.firstChernClassAdd :=
  rfl

/-- Two determinant packages with isomorphic determinant lines have the same first Chern
class, independently of their chosen inverse representatives. -/
theorem firstChernClass_eq_of_lineIso (D : DeterminantData E)
    (D' : DeterminantData F) (e : D.line ≅ D'.line) :
    D.firstChernClass = D'.firstChernClass :=
  D.topExteriorPower.toPic_eq_of_iso D'.topExteriorPower e

end DeterminantData

/-- Determinant compatibility data for a direct sum.

The comparison is explicit: constructing it geometrically is precisely the top-exterior-power
descent statement, and is not inferred from unsupported sheaf exterior-power machinery. -/
structure DirectSumDeterminantData (E F : X.Modules) where
  left : DeterminantData E
  right : DeterminantData F
  sum : DeterminantData (E ⊞ F)
  lineIso : sum.line ≅ tensorObj left.line right.line

namespace DirectSumDeterminantData

variable {E F : X.Modules}

/-- Determinants turn direct sums into tensor products. -/
theorem firstChernClass_eq_mul (D : DirectSumDeterminantData E F) :
    D.sum.firstChernClass =
      D.left.firstChernClass * D.right.firstChernClass := by
  apply Units.ext
  change PicardClass.mk D.sum.line =
    PicardClass.mk D.left.line * PicardClass.mk D.right.line
  rw [PicardClass.mk_mul_mk]
  exact (PicardClass.mk_eq_mk_iff _ _).2 ⟨D.lineIso⟩

/-- Additive form of determinant compatibility with direct sums. -/
theorem firstChernClassAdd_eq_add (D : DirectSumDeterminantData E F) :
    D.sum.firstChernClassAdd =
      D.left.firstChernClassAdd + D.right.firstChernClassAdd := by
  apply Additive.toMul.injective
  exact D.firstChernClass_eq_mul

end DirectSumDeterminantData

/-- Determinant compatibility data for a short exact sequence. -/
structure ShortExactDeterminantData (S : ShortComplex X.Modules) where
  shortExact : S.ShortExact
  left : DeterminantData S.X₁
  middle : DeterminantData S.X₂
  right : DeterminantData S.X₃
  lineIso : middle.line ≅ tensorObj left.line right.line

namespace ShortExactDeterminantData

variable {S : ShortComplex X.Modules}

/-- The determinant line of the middle term of a short exact sequence is the tensor product of
the determinant lines of its ends. -/
theorem firstChernClass_eq_mul (D : ShortExactDeterminantData S) :
    D.middle.firstChernClass =
      D.left.firstChernClass * D.right.firstChernClass := by
  apply Units.ext
  change PicardClass.mk D.middle.line =
    PicardClass.mk D.left.line * PicardClass.mk D.right.line
  rw [PicardClass.mk_mul_mk]
  exact (PicardClass.mk_eq_mk_iff _ _).2 ⟨D.lineIso⟩

/-- First Chern classes are additive in determinant-equipped short exact sequences. -/
theorem firstChernClassAdd_eq_add (D : ShortExactDeterminantData S) :
    D.middle.firstChernClassAdd =
      D.left.firstChernClassAdd + D.right.firstChernClassAdd := by
  apply Additive.toMul.injective
  exact D.firstChernClass_eq_mul

end ShortExactDeterminantData

end

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Coh

variable {X : Scheme.{u}}

noncomputable section

/-- Determinant data for a coherent sheaf whose underlying module sheaf is explicitly finite
locally free of fixed rank.  No instance asserts this for arbitrary coherent sheaves. -/
abbrev DeterminantData (F : Coh X) :=
  Scheme.Modules.DeterminantData ((ι X).obj F)

/-- Determinant compatibility data for a short exact sequence of coherent sheaves. -/
structure ShortExactDeterminantData [IsLocallyNoetherian X]
    (S : ShortComplex (Coh X)) where
  shortExact : S.ShortExact
  left : DeterminantData S.X₁
  middle : DeterminantData S.X₂
  right : DeterminantData S.X₃
  lineIso : middle.line ≅
    Scheme.Modules.tensorObj left.line right.line

namespace ShortExactDeterminantData

/-- Forget a coherent determinant comparison to the ambient module-sheaf category. -/
noncomputable def toModules [IsLocallyNoetherian X]
    {S : ShortComplex (Coh X)} (D : ShortExactDeterminantData S) :
    Scheme.Modules.ShortExactDeterminantData (S.map (ι X)) where
  shortExact := shortExact_map_ι X D.shortExact
  left := D.left
  middle := D.middle
  right := D.right
  lineIso := D.lineIso

/-- First Chern classes are additive for coherent short exact sequences carrying explicit
finite-locally-free determinant comparison data. -/
theorem firstChernClassAdd_eq_add [IsLocallyNoetherian X]
    {S : ShortComplex (Coh X)} (D : ShortExactDeterminantData S) :
    D.middle.firstChernClassAdd =
      D.left.firstChernClassAdd + D.right.firstChernClassAdd :=
  D.toModules.firstChernClassAdd_eq_add

end ShortExactDeterminantData

/-- A coherent sheaf with an explicit two-term finite locally free resolution.

This is the available perfectness hypothesis in this file: no theorem manufactures such a
resolution for an arbitrary coherent sheaf. -/
structure TwoTermPerfectDeterminantData [IsLocallyNoetherian X] (F : Coh X) where
  resolution : ShortComplex (Coh X)
  shortExact : resolution.ShortExact
  targetIso : resolution.X₃ ≅ F
  left : DeterminantData resolution.X₁
  middle : DeterminantData resolution.X₂

namespace TwoTermPerfectDeterminantData

/-- The determinant line of a two-term resolution is
`det(P₀) ⊗ det(P₁)⁻¹`. -/
noncomputable def determinantLine [IsLocallyNoetherian X] {F : Coh X}
    (D : TwoTermPerfectDeterminantData F) :
    Scheme.Modules.LineBundleData X :=
  D.middle.topExteriorPower.tensor D.left.topExteriorPower.dual

/-- First Chern class of a coherent sheaf carrying a two-term finite locally free resolution. -/
noncomputable def firstChernClass [IsLocallyNoetherian X] {F : Coh X}
    (D : TwoTermPerfectDeterminantData F) : Scheme.Modules.Pic X :=
  D.determinantLine.toPic

/-- Additive notation for the first Chern class of a two-term perfect object. -/
noncomputable def firstChernClassAdd [IsLocallyNoetherian X] {F : Coh X}
    (D : TwoTermPerfectDeterminantData F) : Additive (Scheme.Modules.Pic X) :=
  Additive.ofMul D.firstChernClass

/-- The resolution formula `c₁(F) = c₁(P₀) - c₁(P₁)`. -/
theorem firstChernClass_eq [IsLocallyNoetherian X] {F : Coh X}
    (D : TwoTermPerfectDeterminantData F) :
    D.firstChernClass =
      D.middle.firstChernClass * D.left.firstChernClass⁻¹ := by
  simp [firstChernClass, determinantLine,
    Scheme.Modules.DeterminantData.firstChernClass]

/-- Transport a two-term determinant resolution across an isomorphism of its target. -/
noncomputable def ofIso [IsLocallyNoetherian X] {F G : Coh X}
    (D : TwoTermPerfectDeterminantData F) (e : F ≅ G) :
    TwoTermPerfectDeterminantData G where
  resolution := D.resolution
  shortExact := D.shortExact
  targetIso := D.targetIso ≪≫ e
  left := D.left
  middle := D.middle

@[simp]
theorem firstChernClass_ofIso [IsLocallyNoetherian X] {F G : Coh X}
    (D : TwoTermPerfectDeterminantData F) (e : F ≅ G) :
    (D.ofIso e).firstChernClass = D.firstChernClass :=
  rfl

end TwoTermPerfectDeterminantData

/-- Determinant comparison data for a coherent short exact sequence whose terms carry
two-term finite locally free resolutions. -/
structure PerfectShortExactDeterminantData [IsLocallyNoetherian X]
    (S : ShortComplex (Coh X)) where
  shortExact : S.ShortExact
  left : TwoTermPerfectDeterminantData S.X₁
  middle : TwoTermPerfectDeterminantData S.X₂
  right : TwoTermPerfectDeterminantData S.X₃
  lineIso : middle.determinantLine.line ≅
    Scheme.Modules.tensorObj left.determinantLine.line right.determinantLine.line

namespace PerfectShortExactDeterminantData

/-- First Chern classes are additive for a perfect short exact comparison. -/
theorem firstChernClassAdd_eq_add [IsLocallyNoetherian X]
    {S : ShortComplex (Coh X)} (D : PerfectShortExactDeterminantData S) :
    D.middle.firstChernClassAdd =
      D.left.firstChernClassAdd + D.right.firstChernClassAdd := by
  apply Additive.toMul.injective
  apply Units.ext
  change Scheme.Modules.PicardClass.mk D.middle.determinantLine.line =
    Scheme.Modules.PicardClass.mk D.left.determinantLine.line *
      Scheme.Modules.PicardClass.mk D.right.determinantLine.line
  rw [Scheme.Modules.PicardClass.mk_mul_mk]
  exact (Scheme.Modules.PicardClass.mk_eq_mk_iff _ _).2 ⟨D.lineIso⟩

end PerfectShortExactDeterminantData

end

end AlgebraicGeometry.Coh
