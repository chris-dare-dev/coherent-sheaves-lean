/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import CohLean.AlgebraicGeometry.Variety.Numerical
import CohLean.Cohomology.EulerCharacteristic.Additivity
import CohLean.Intersection.ChernCharacter.Basic
import CohLean.Numerical.GrothendieckGroup.Lattice
import CohLean.Numerical.Specializations.Surface
import CohLean.RiemannRoch.Grothendieck

/-!
# A geometric numerical variety for surfaces

This file is the assembly point from the geometric surface theory to Layer A.  It does two
things which should not be hidden behind instances:

* an invariant of coherent sheaves which respects isomorphisms and short exact sequences is
  descended through the explicit Grothendieck group `K₀(Coh X)`;
* reconstructed surface Chern characters, geometric Todd components, and geometric
  Hirzebruch--Riemann--Roch are packaged as a genuine `NumericalVariety`.

The construction uses `K₀(Coh X)` as its input group.  The numerical Grothendieck group is then
the Euler-radical quotient from `Numerical/GrothendieckGroup/Lattice.lean`; in particular the
quotient and sign conventions are shared with Layer A rather than reconstructed here.

`GeometricData.sheaf_hirzebruch_riemannRoch` is a theorem about every coherent sheaf, not a
Layer A axiom about arbitrary Grothendieck classes.  The latter is proved below by descending
both sides as additive invariants.  Thus `toNumericalVariety` is the point where the abstract
`NumericalVariety.hirzebruch_riemannRoch` field is discharged.
-/

universe u v w

open CategoryTheory

namespace CohLean.RiemannRoch.Surface

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Numerical
open CohLean.Intersection.ChernCharacter
open CohLean.Intersection.Number
open scoped BigOperators

variable {k : Type u} [Field k]
variable {X : Variety k}

noncomputable section

/-! ## Additive invariants and the coherent Grothendieck group -/

/- The dimension-independent implementation lives in `RiemannRoch/Grothendieck`.  These
aliases preserve the original surface API while new dimensions use the common owner. -/
abbrev CoherentAdditiveInvariant (X : Variety k) (M : Type v) [AddCommGroup M] :=
  CohLean.RiemannRoch.CoherentAdditiveInvariant X M

namespace CoherentAdditiveInvariant

variable {M : Type v} [AddCommGroup M]

noncomputable abbrev freeHom (I : CoherentAdditiveInvariant X M) :
    FreeAbelianGroup (Coh X.toScheme) →+ M :=
  CohLean.RiemannRoch.CoherentAdditiveInvariant.freeHom I

abbrev coherentGrothendieckRelations_le_ker (I : CoherentAdditiveInvariant X M) :
    coherentGrothendieckRelations X ≤ I.freeHom.ker :=
  CohLean.RiemannRoch.CoherentAdditiveInvariant.coherentGrothendieckRelations_le_ker I

noncomputable abbrev grothendieckHom (I : CoherentAdditiveInvariant X M) :
    CoherentGrothendieckGroup X →+ M :=
  CohLean.RiemannRoch.CoherentAdditiveInvariant.grothendieckHom I

abbrev grothendieckHom_class (I : CoherentAdditiveInvariant X M)
    (F : Coh X.toScheme) :
    I.grothendieckHom (coherentGrothendieckClass F) = I.obj F :=
  CohLean.RiemannRoch.CoherentAdditiveInvariant.grothendieckHom_class I F

end CoherentAdditiveInvariant

abbrev coherentGrothendieckGroup_hom_ext {M : Type v} [AddCommGroup M]
    {f g : CoherentGrothendieckGroup X →+ M}
    (h : ∀ F : Coh X.toScheme,
      f (coherentGrothendieckClass F) = g (coherentGrothendieckClass F)) :
    f = g :=
  CohLean.RiemannRoch.coherentGrothendieckGroup_hom_ext h

/-! ## Reconstructed Chern characters on `K₀` -/

variable {D : FiniteCohomology X}
variable {C : D.LinearConnectingSystem}
variable {A : Type v} [CommRing A] [Algebra ℚ A] [NumericalRing 2 A]
variable {P : PairingContext D C 2 A}
variable {O : Coh X.toScheme}
variable (RO : P.ReconstructionData O)

/-- A compatible choice of reconstruction data for every coherent sheaf.

The comparison fields are the exact hypotheses needed by the reconstruction theorems.  They
are separated from `GeometricData` because they already suffice to descend rank and Chern
character to the coherent Grothendieck group. -/
structure ReconstructionSystem where
  /-- Reconstruction data for every coherent sheaf. -/
  reconstruction : ∀ F : Coh X.toScheme, P.ReconstructionData F
  /-- Rank is invariant under coherent-sheaf isomorphism. -/
  rank_iso : ∀ {F G : Coh X.toScheme} (_e : F ≅ G),
    (reconstruction F).rank = (reconstruction G).rank
  /-- Twist Euler functions are invariant under coherent-sheaf isomorphism. -/
  eulerPic_iso : ∀ {F G : Coh X.toScheme} (_e : F ≅ G),
    (reconstruction F).twists.eulerPic = (reconstruction G).twists.eulerPic
  /-- Rank is additive in a short exact sequence. -/
  rank_shortExact : ∀ (S : ShortComplex (Coh X.toScheme)) (_hS : S.ShortExact),
    (reconstruction S.X₂).rank =
      (reconstruction S.X₁).rank + (reconstruction S.X₃).rank
  /-- Twist Euler functions are additive in a short exact sequence. -/
  eulerPic_shortExact : ∀ (S : ShortComplex (Coh X.toScheme)) (_hS : S.ShortExact),
    (reconstruction S.X₂).twists.eulerPic =
      (reconstruction S.X₁).twists.eulerPic +
        (reconstruction S.X₃).twists.eulerPic

namespace ReconstructionSystem

/-- Rank as an additive invariant of coherent sheaves. -/
def rankInvariant (R : ReconstructionSystem (P := P)) : CoherentAdditiveInvariant X ℤ where
  obj F := (R.reconstruction F).rank
  map_iso e := R.rank_iso e
  map_shortExact S hS := R.rank_shortExact S hS

/-- The reconstructed `i`-th Chern-character component, valued in its certified graded piece,
as an additive invariant of coherent sheaves. -/
noncomputable def chernCharacterInvariant (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O) (i : ℕ) :
    CoherentAdditiveInvariant X (NumericalRing.piece (n := 2) (A := A) i) where
  obj F := ⟨chernCharacterComponent RO (R.reconstruction F) i,
    chernCharacterComponent_mem RO (R.reconstruction F) i⟩
  map_iso := by
    intro F G e
    apply Subtype.ext
    exact chernCharacterComponent_iso RO (R.reconstruction F) (R.reconstruction G) e
      (R.rank_iso e) (R.eulerPic_iso e) i
  map_shortExact := by
    intro S hS
    apply Subtype.ext
    exact chernCharacterComponent_add RO (R.reconstruction S.X₁)
      (R.reconstruction S.X₃) (R.reconstruction S.X₂)
      (R.rank_shortExact S hS) (R.eulerPic_shortExact S hS) i

/-- Rank on `K₀(Coh X)`. -/
noncomputable def rankHom (R : ReconstructionSystem (P := P)) :
    CoherentGrothendieckGroup X →+ ℤ :=
  R.rankInvariant.grothendieckHom

/-- The reconstructed `i`-th Chern-character component on `K₀(Coh X)`. -/
noncomputable def chernCharacterHom (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O) (i : ℕ) :
    CoherentGrothendieckGroup X →+ A :=
  (NumericalRing.piece (n := 2) (A := A) i).subtype.toAddMonoidHom.comp
    (R.chernCharacterInvariant RO i).grothendieckHom

@[simp]
theorem rankHom_class (R : ReconstructionSystem (P := P)) (F : Coh X.toScheme) :
    R.rankHom (coherentGrothendieckClass F) = (R.reconstruction F).rank := by
  simp [rankHom, rankInvariant]

@[simp]
theorem chernCharacterHom_class (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O)
    (F : Coh X.toScheme) (i : ℕ) :
    R.chernCharacterHom RO i (coherentGrothendieckClass F) =
      chernCharacterComponent RO (R.reconstruction F) i := by
  simp [chernCharacterHom, chernCharacterInvariant]

/-- Every descended Chern-character component remains in the correct graded piece. -/
theorem chernCharacterHom_mem (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O)
    (E : CoherentGrothendieckGroup X) (i : ℕ) :
    R.chernCharacterHom RO i E ∈ NumericalRing.piece (n := 2) i :=
  ((R.chernCharacterInvariant RO i).grothendieckHom E).property

/-- The rational algebra map restricted to integral ranks. -/
noncomputable def intAlgebraMap : ℤ →+ A where
  toFun r := algebraMap ℚ A (r : ℚ)
  map_zero' := by simp
  map_add' r s := by simp

/-- The reconstructed zeroth Chern character is the algebra image of numerical rank on every
Grothendieck class, not only on sheaf generators. -/
theorem chernCharacterHom_zero (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O)
    (E : CoherentGrothendieckGroup X) :
    R.chernCharacterHom RO 0 E = algebraMap ℚ A (R.rankHom E : ℚ) := by
  have hhom : R.chernCharacterHom RO 0 =
      (intAlgebraMap (A := A)).comp R.rankHom := by
    apply coherentGrothendieckGroup_hom_ext
    intro F
    simp [intAlgebraMap]
  exact DFunLike.congr_fun hhom E

theorem chernCharacterHom_add (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O)
    (E F : CoherentGrothendieckGroup X) (i : ℕ) :
    R.chernCharacterHom RO i (E + F) =
      R.chernCharacterHom RO i E + R.chernCharacterHom RO i F :=
  map_add _ _ _

end ReconstructionSystem

/-! ## Surface assembly and Hirzebruch--Riemann--Roch -/

/-- Geometric input which assembles the coherent Grothendieck group into a Layer A numerical
surface.

The HRR field is deliberately stated only for genuine coherent sheaves.  The proof for every
virtual Grothendieck class is `GeometricData.hirzebruch_riemannRoch` below. -/
structure GeometricData (RO : P.ReconstructionData O)
    (R : ReconstructionSystem (P := P)) where
  /-- The geometrically constructed Todd components. -/
  toddComponent : ℕ → A
  /-- Todd components carry their geometric grading. -/
  toddComponent_mem : ∀ i,
    toddComponent i ∈ NumericalRing.piece (n := 2) i
  /-- The degree-zero Todd component is normalized to one. -/
  toddComponent_zero : toddComponent 0 = 1
  /-- Geometric surface HRR for coherent sheaves. -/
  sheaf_hirzebruch_riemannRoch : ∀ F : Coh X.toScheme,
    (D.eulerCharacteristic F : ℚ) = NumericalRing.degree (n := 2)
      ((∑ i ∈ Finset.range 3,
          chernCharacterComponent RO (R.reconstruction F) i) *
        (∑ j ∈ Finset.range 3, toddComponent j))

namespace GeometricData

variable {R : ReconstructionSystem (P := P)}

/-- The total reconstructed Chern character as an additive homomorphism on `K₀`. -/
noncomputable def totalChernCharacterHom (_G : GeometricData RO R) :
    CoherentGrothendieckGroup X →+ A :=
  ∑ i ∈ Finset.range 3, R.chernCharacterHom RO i

/-- The total geometric Todd class of the surface. -/
noncomputable def totalTodd (G : GeometricData RO R) : A :=
  ∑ j ∈ Finset.range 3, G.toddComponent j

/-- The right side of HRR, as an additive homomorphism on `K₀`. -/
noncomputable def riemannRochHom (G : GeometricData RO R) :
    CoherentGrothendieckGroup X →+ ℚ where
  toFun E := NumericalRing.degree (n := 2)
    (totalChernCharacterHom (RO := RO) G E * totalTodd (RO := RO) G)
  map_zero' := by simp [totalChernCharacterHom]
  map_add' E F := by
    rw [map_add, add_mul, map_add]

/-- Cast the cohomological Euler homomorphism from `ℤ` to `ℚ`. -/
noncomputable def rationalEulerHom (_G : GeometricData RO R) :
    CoherentGrothendieckGroup X →+ ℚ where
  toFun E := (D.grothendieckEulerHom C E : ℚ)
  map_zero' := by simp
  map_add' E F := by simp

@[simp]
theorem totalChernCharacterHom_class (G : GeometricData RO R)
    (F : Coh X.toScheme) :
    totalChernCharacterHom (RO := RO) G (coherentGrothendieckClass F) =
      ∑ i ∈ Finset.range 3,
        chernCharacterComponent RO (R.reconstruction F) i := by
  simp [totalChernCharacterHom]

@[simp]
theorem riemannRochHom_class (G : GeometricData RO R)
    (F : Coh X.toScheme) :
    riemannRochHom (RO := RO) G (coherentGrothendieckClass F) =
      NumericalRing.degree (n := 2)
        ((∑ i ∈ Finset.range 3,
            chernCharacterComponent RO (R.reconstruction F) i) *
          (∑ j ∈ Finset.range 3, G.toddComponent j)) := by
  simp [riemannRochHom, totalTodd]

@[simp]
theorem rationalEulerHom_class (G : GeometricData RO R)
    (F : Coh X.toScheme) :
    rationalEulerHom (RO := RO) G (coherentGrothendieckClass F) =
      (D.eulerCharacteristic F : ℚ) := by
  simp [rationalEulerHom]

/-- Geometric HRR descends from coherent sheaves to every virtual Grothendieck class. -/
theorem hirzebruch_riemannRoch (G : GeometricData RO R)
    (E : CoherentGrothendieckGroup X) :
    (D.grothendieckEulerHom C E : ℚ) = NumericalRing.degree (n := 2)
      ((∑ i ∈ Finset.range 3, R.chernCharacterHom RO i E) *
        (∑ j ∈ Finset.range 3, G.toddComponent j)) := by
  have hhom : rationalEulerHom (RO := RO) G = riemannRochHom (RO := RO) G := by
    apply coherentGrothendieckGroup_hom_ext
    intro F
    rw [rationalEulerHom_class (RO := RO) G,
      riemannRochHom_class (RO := RO) G]
    exact G.sheaf_hirzebruch_riemannRoch F
  change rationalEulerHom (RO := RO) G E = riemannRochHom (RO := RO) G E
  exact DFunLike.congr_fun hhom E

/-- The scheme-derived numerical surface.

Its HRR field is filled by `GeometricData.hirzebruch_riemannRoch`, which was proved from the
coherent-sheaf theorem by Grothendieck descent. -/
@[reducible]
noncomputable def toNumericalVariety (G : GeometricData RO R) :
    NumericalVariety 2 A (CoherentGrothendieckGroup X) where
  toNumericalRing := inferInstance
  rank := R.rankHom
  chComp E i := R.chernCharacterHom RO i E
  chComp_mem := R.chernCharacterHom_mem RO
  chComp_zero := R.chernCharacterHom_zero RO
  chComp_add := R.chernCharacterHom_add RO
  toddComp := G.toddComponent
  toddComp_mem := G.toddComponent_mem
  toddComp_zero := G.toddComponent_zero
  chi := D.grothendieckEulerHom C
  hirzebruch_riemannRoch := G.hirzebruch_riemannRoch

@[simp]
theorem toNumericalVariety_rank_class (G : GeometricData RO R)
    (F : Coh X.toScheme) :
    G.toNumericalVariety.rank (coherentGrothendieckClass F) =
      (R.reconstruction F).rank := by
  change R.rankHom (coherentGrothendieckClass F) = (R.reconstruction F).rank
  exact R.rankHom_class F

@[simp]
theorem toNumericalVariety_chComp_class (G : GeometricData RO R)
    (F : Coh X.toScheme) (i : ℕ) :
    G.toNumericalVariety.chComp (coherentGrothendieckClass F) i =
      chernCharacterComponent RO (R.reconstruction F) i := by
  change R.chernCharacterHom RO i (coherentGrothendieckClass F) =
    chernCharacterComponent RO (R.reconstruction F) i
  exact R.chernCharacterHom_class RO F i

@[simp]
theorem toNumericalVariety_toddComp (G : GeometricData RO R) (i : ℕ) :
    G.toNumericalVariety.toddComp i = G.toddComponent i :=
  rfl

@[simp]
theorem toNumericalVariety_chi_class (G : GeometricData RO R)
    (F : Coh X.toScheme) :
    G.toNumericalVariety.chi (coherentGrothendieckClass F) =
      D.eulerCharacteristic F := by
  change D.grothendieckEulerHom C (coherentGrothendieckClass F) =
    D.eulerCharacteristic F
  exact D.grothendieckEulerHom_class C F

/-- On a coherent-sheaf class, the Layer A surface expansion is exactly the geometric
rank/`ch₁`/`ch₂` expansion used to construct the instance. -/
theorem surface_chi_class_eq (G : GeometricData RO R)
    (F : Coh X.toScheme) :
    (D.eulerCharacteristic F : ℚ) =
      ((R.reconstruction F).rank : ℚ) *
          NumericalRing.degree (n := 2) (G.toddComponent 2) +
        NumericalRing.degree (n := 2)
          (chernCharacterComponent RO (R.reconstruction F) 1 *
            G.toddComponent 1) +
        NumericalRing.degree (n := 2)
          (chernCharacterComponent RO (R.reconstruction F) 2) := by
  have h := @AlgebraicGeometry.Numerical.Surface.chi_eq
    A (CoherentGrothendieckGroup X) _ _ _ G.toNumericalVariety
    (coherentGrothendieckClass F)
  rw [toNumericalVariety_chi_class (RO := RO) G F,
    toNumericalVariety_rank_class (RO := RO) G F,
    toNumericalVariety_toddComp (RO := RO) G 2,
    toNumericalVariety_chComp_class (RO := RO) G F 1,
    toNumericalVariety_toddComp (RO := RO) G 1,
    toNumericalVariety_chComp_class (RO := RO) G F 2] at h
  exact h

/-- The geometric K3 hypotheses give the existing Layer A K3 structure on the assembled
surface. -/
theorem toIsK3 (G : GeometricData RO R)
    (htoddOne : G.toddComponent 1 = 0)
    (htoddTwo : NumericalRing.degree (n := 2) (G.toddComponent 2) = 2) :
    letI := G.toNumericalVariety
    K3.IsK3 A (CoherentGrothendieckGroup X) := by
  letI := G.toNumericalVariety
  exact
    { toddComp_one := htoddOne
      degree_toddComp_two := htoddTwo }

/-- Under the geometric K3 hypotheses, the existing Layer A K3 Riemann--Roch theorem becomes
the corresponding statement for every coherent sheaf. -/
theorem k3_eulerCharacteristic_eq (G : GeometricData RO R)
    (htoddOne : G.toddComponent 1 = 0)
    (htoddTwo : NumericalRing.degree (n := 2) (G.toddComponent 2) = 2)
    (F : Coh X.toScheme) :
    (D.eulerCharacteristic F : ℚ) =
      2 * ((R.reconstruction F).rank : ℚ) +
        NumericalRing.degree (n := 2)
          (chernCharacterComponent RO (R.reconstruction F) 2) := by
  letI : NumericalVariety 2 A (CoherentGrothendieckGroup X) :=
    G.toNumericalVariety
  letI : K3.IsK3 A (CoherentGrothendieckGroup X) :=
    toIsK3 (RO := RO) G htoddOne htoddTwo
  simpa only [toNumericalVariety_chi_class, toNumericalVariety_rank_class,
    toNumericalVariety_chComp_class] using
      (K3.chi_eq (A := A) (coherentGrothendieckClass F))

/-- The numerical class of a coherent sheaf: first its coherent-Grothendieck class, then the
Euler-radical quotient fixed by Layer A. -/
noncomputable def numericalClass (G : GeometricData RO R) (F : Coh X.toScheme) :
    letI := G.toNumericalVariety
    NumericalVariety.NumericalQuotient 2 A (CoherentGrothendieckGroup X) := by
  letI := G.toNumericalVariety
  exact Submodule.Quotient.mk (coherentGrothendieckClass F)

end GeometricData

end

end CohLean.RiemannRoch.Surface
