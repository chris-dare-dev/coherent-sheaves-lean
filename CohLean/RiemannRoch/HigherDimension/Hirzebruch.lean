/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import CohLean.Intersection.ChernCharacter.Basic
import CohLean.Numerical.Specializations.Fourfold
import CohLean.Numerical.Specializations.Threefold
import CohLean.RiemannRoch.Grothendieck

/-!
# Reconstructed Hirzebruch--Riemann--Roch through dimension four

This file implements the higher-dimensional route selected in issue #45.  The route is
numerical rather than cycle-valued:

* Snapper polynomiality supplies the Picard Euler polynomial of every coherent sheaf;
* `PairingContext.ReconstructionData` represents its homogeneous coefficients as the
  Todd-weighted components `tau_i(F)` in a chosen numerical ring;
* the structure sheaf supplies the positive-degree Todd components;
* the triangular identities from `Intersection/ChernCharacter/Basic` recover `ch_i(F)`; and
* the top identity `degree (tau_d(F)) = chi(F)` proves HRR.

The construction is valid in every positive dimension at most four.  In particular it gives
scheme-derived `NumericalVariety` bridges in dimensions three and four and makes the existing
Layer A display formulas unconditional once the explicit reconstruction packages below are
supplied.

## Trust and scope boundary

`PairingContext` keeps representability and separation by divisor products explicit.  This is
necessary: products of divisors need not separate all middle-codimension classes on an arbitrary
higher-dimensional variety.  The Todd components constructed here are therefore
divisor-numerical representatives reconstructed from `chi`, not cycle-valued Chow classes.

No splitting principle, deformation to the normal cone, or Grothendieck--Riemann--Roch theorem
is required for this numerical HRR statement.  Such input would still be required to identify
these representatives with Chern-polynomial expressions in a geometrically constructed tangent
bundle.  The upper bound four is exactly the current bound of the triangular Chern-character
implementation; arbitrary dimension requires extending that universal recursion, not adding a
new HRR axiom.
-/

universe u v

open CategoryTheory

namespace CohLean.RiemannRoch.HigherDimension

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Numerical
open AlgebraicGeometry.Scheme.Modules
open CohLean.Intersection.ChernCharacter
open CohLean.Intersection.Number
open CohLean.Intersection.Snapper
open scoped BigOperators

variable {k : Type u} [Field k]
variable {X : Variety k}
variable {D : FiniteCohomology X}
variable {C : D.LinearConnectingSystem}
variable {d : ℕ}
variable {A : Type v} [CommRing A] [Algebra ℚ A] [NumericalRing d A]
variable {P : PairingContext D C d A}
variable {O : Coh X.toScheme}

noncomputable section

/-! ## The top reconstructed component -/

private theorem homogeneousPicardCoefficient_nil
    (d : ℕ) (f : Pic X.toScheme → ℤ) :
    homogeneousPicardCoefficient d [] f = (f 1 : ℚ) := by
  have hinj : Set.InjOn (fun j : ℕ ↦ (j : ℚ))
      (Finset.range (d + 1) : Set ℕ) := by
    intro a _ b _ hab
    exact Nat.cast_inj.mp hab
  have h := Lagrange.eval_interpolate_at_node
    (s := Finset.range (d + 1)) (v := fun j : ℕ ↦ (j : ℚ))
    (r := fun _j : ℕ ↦ (f 1 : ℚ)) hinj (i := 0) (by simp)
  have h0 : Polynomial.eval (0 : ℚ)
      (Lagrange.interpolate (Finset.range (d + 1)) (fun j : ℕ ↦ (j : ℚ))
        (fun _j : ℕ ↦ (f 1 : ℚ))) = (f 1 : ℚ) := by
    simpa using h
  rw [← Polynomial.coeff_zero_eq_eval_zero] at h0
  simpa [homogeneousPicardCoefficient, interpolatingPolynomial,
    scaledPicardCoefficient, picardCoefficient] using h0

/-- The Picard Euler function in any reconstruction package takes the trivial class to the
actual Euler characteristic of its coherent sheaf. -/
theorem reconstruction_eulerPic_one {F : Coh X.toScheme}
    (Q : P.ReconstructionData F) :
    Q.twists.eulerPic 1 = D.eulerCharacteristic F := by
  let L : Fin 0 → Pic X.toScheme := fun i ↦ Fin.elim0 i
  have h := Q.twists.realization 0 L (0 : Fin 0 → ℤ)
  rw [picardMonomial_zero] at h
  calc
    Q.twists.eulerPic 1 =
        D.eulerCharacteristic ((Q.twists.twistFamily 0 L).obj 0) := h
    _ = D.eulerCharacteristic F := by
      apply D.eulerCharacteristic_iso
      apply ObjectProperty.isoMk (Scheme.coherent X.toScheme)
      simpa [CoherentTwistFamily.obj, twistModules, twistModulesAlong] using
        (Iso.refl F.1)

/-- In every dimension, the degree of the top reconstructed Todd-weighted component is the
coherent Euler characteristic. -/
theorem degree_tauComponent_top_eq_eulerCharacteristic
    {F : Coh X.toScheme} (Q : P.ReconstructionData F) :
    NumericalRing.degree (n := d) (Q.tauComponent d) =
      (D.eulerCharacteristic F : ℚ) := by
  have h := Q.degree_tauComponent_mul_divisorProduct d (by omega) [] (by simp)
  rw [divisorProduct_nil, mul_one, PairingContext.twistPairing,
    homogeneousPicardCoefficient_nil] at h
  calc
    NumericalRing.degree (n := d) (Q.tauComponent d) =
        (Q.twists.eulerPic 1 : ℚ) := h
    _ = (D.eulerCharacteristic F : ℚ) := by
      exact_mod_cast reconstruction_eulerPic_one Q

/-! ## Dimension-general descent through `K₀(Coh X)` -/

/-- A compatible choice of reconstruction data for every coherent sheaf in dimension `d`. -/
structure ReconstructionSystem where
  reconstruction : ∀ F : Coh X.toScheme, P.ReconstructionData F
  rank_iso : ∀ {F G : Coh X.toScheme} (_e : F ≅ G),
    (reconstruction F).rank = (reconstruction G).rank
  eulerPic_iso : ∀ {F G : Coh X.toScheme} (_e : F ≅ G),
    (reconstruction F).twists.eulerPic = (reconstruction G).twists.eulerPic
  rank_shortExact : ∀ (S : ShortComplex (Coh X.toScheme)) (_hS : S.ShortExact),
    (reconstruction S.X₂).rank =
      (reconstruction S.X₁).rank + (reconstruction S.X₃).rank
  eulerPic_shortExact : ∀ (S : ShortComplex (Coh X.toScheme)) (_hS : S.ShortExact),
    (reconstruction S.X₂).twists.eulerPic =
      (reconstruction S.X₁).twists.eulerPic +
        (reconstruction S.X₃).twists.eulerPic

namespace ReconstructionSystem

/-- Reconstructed rank as an additive coherent-sheaf invariant. -/
def rankInvariant (R : ReconstructionSystem (P := P)) :
    CoherentAdditiveInvariant X ℤ where
  obj F := (R.reconstruction F).rank
  map_iso e := R.rank_iso e
  map_shortExact S hS := R.rank_shortExact S hS

/-- The reconstructed `i`-th Chern-character component as an additive coherent-sheaf
invariant valued in the certified graded piece. -/
noncomputable def chernCharacterInvariant (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O) (i : ℕ) :
    CoherentAdditiveInvariant X
      (NumericalRing.piece (n := d) (A := A) i) where
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

/-- Reconstructed rank on `K₀(Coh X)`. -/
noncomputable def rankHom (R : ReconstructionSystem (P := P)) :
    CoherentGrothendieckGroup X →+ ℤ :=
  R.rankInvariant.grothendieckHom

/-- The reconstructed `i`-th Chern-character component on `K₀(Coh X)`. -/
noncomputable def chernCharacterHom (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O) (i : ℕ) :
    CoherentGrothendieckGroup X →+ A :=
  (NumericalRing.piece (n := d) (A := A) i).subtype.toAddMonoidHom.comp
    (R.chernCharacterInvariant RO i).grothendieckHom

@[simp]
theorem rankHom_class (R : ReconstructionSystem (P := P)) (F : Coh X.toScheme) :
    R.rankHom (coherentGrothendieckClass F) = (R.reconstruction F).rank := by
  simp [rankHom, rankInvariant]

@[simp]
theorem chernCharacterHom_class (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O) (F : Coh X.toScheme) (i : ℕ) :
    R.chernCharacterHom RO i (coherentGrothendieckClass F) =
      chernCharacterComponent RO (R.reconstruction F) i := by
  simp [chernCharacterHom, chernCharacterInvariant]

/-- Every descended Chern-character component remains in its graded piece. -/
theorem chernCharacterHom_mem (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O)
    (E : CoherentGrothendieckGroup X) (i : ℕ) :
    R.chernCharacterHom RO i E ∈ NumericalRing.piece (n := d) i :=
  ((R.chernCharacterInvariant RO i).grothendieckHom E).property

/-- The rational algebra map restricted to integral ranks. -/
noncomputable def intAlgebraMap : ℤ →+ A where
  toFun r := algebraMap ℚ A (r : ℚ)
  map_zero' := by simp
  map_add' r s := by simp

/-- The descended zeroth Chern character is the algebra image of rank. -/
theorem chernCharacterHom_zero (R : ReconstructionSystem (P := P))
    (RO : P.ReconstructionData O) (E : CoherentGrothendieckGroup X) :
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

/-! ## Reconstructed Todd components and the top convolution -/

/-- The reconstructed Todd component, normalized to `td₀ = 1`.  Positive components are the
Todd-weighted representatives reconstructed from the structure sheaf. -/
noncomputable def reconstructedToddComponent (RO : P.ReconstructionData O) : ℕ → A
  | 0 => 1
  | i + 1 => toddComponent RO (i + 1)

@[simp]
theorem reconstructedToddComponent_zero (RO : P.ReconstructionData O) :
    reconstructedToddComponent RO 0 = (1 : A) := rfl

@[simp]
theorem reconstructedToddComponent_succ (RO : P.ReconstructionData O) (i : ℕ) :
    reconstructedToddComponent RO (i + 1) = toddComponent RO (i + 1) := rfl

theorem reconstructedToddComponent_mem (RO : P.ReconstructionData O) (i : ℕ) :
    reconstructedToddComponent RO i ∈ NumericalRing.piece (n := d) i := by
  cases i with
  | zero => exact NumericalRing.one_mem_piece_zero
  | succ i => exact PairingContext.ReconstructionData.tauComponent_mem RO (i + 1)

private theorem degree_sum_mul_sum_eq_antidiagonal
    (ch td : ℕ → A)
    (hch : ∀ i, ch i ∈ NumericalRing.piece (n := d) i)
    (htd : ∀ i, td i ∈ NumericalRing.piece (n := d) i) :
    NumericalRing.degree (n := d)
        ((∑ i ∈ Finset.range (d + 1), ch i) *
          (∑ j ∈ Finset.range (d + 1), td j)) =
      ∑ i ∈ Finset.range (d + 1),
        NumericalRing.degree (n := d) (ch i * td (d - i)) := by
  rw [Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [map_sum]
  refine Finset.sum_eq_single (d - i) (fun b _ hb ↦ ?_) (fun hmem ↦ ?_)
  · refine NumericalRing.degree_eq_zero_of_mem (fun hib ↦ hb ?_)
      (NumericalRing.mul_mem_piece (hch i) (htd b))
    omega
  · exact absurd (Finset.mem_range.mpr (by omega)) hmem

private theorem degree_antidiagonal_eq_tauComponent
    (RO : P.ReconstructionData O) {F : Coh X.toScheme}
    (Q : P.ReconstructionData F)
    (hdpos : 1 ≤ d) (hd4 : d ≤ 4) :
    (∑ i ∈ Finset.range (d + 1),
        NumericalRing.degree (n := d)
          (chernCharacterComponent RO Q i * reconstructedToddComponent RO (d - i))) =
      NumericalRing.degree (n := d) (Q.tauComponent d) := by
  interval_cases d <;>
    simp [Finset.sum_range_succ, reconstructedToddComponent] <;> ring

/-- Reconstructed HRR for every coherent sheaf in every positive dimension at most four. -/
theorem sheaf_hirzebruch_riemannRoch
    (RO : P.ReconstructionData O)
    (R : ReconstructionSystem (P := P))
    (hdpos : 1 ≤ d) (hd4 : d ≤ 4)
    (F : Coh X.toScheme) :
    (D.eulerCharacteristic F : ℚ) = NumericalRing.degree (n := d)
      ((∑ i ∈ Finset.range (d + 1),
          chernCharacterComponent RO (R.reconstruction F) i) *
        (∑ j ∈ Finset.range (d + 1), reconstructedToddComponent RO j)) := by
  rw [degree_sum_mul_sum_eq_antidiagonal _ _
    (chernCharacterComponent_mem RO (R.reconstruction F))
    (reconstructedToddComponent_mem RO)]
  rw [degree_antidiagonal_eq_tauComponent RO (R.reconstruction F) hdpos hd4]
  exact (degree_tauComponent_top_eq_eulerCharacteristic (R.reconstruction F)).symm

/-! ## The numerical variety and its low-dimensional bridges -/

/-- The total reconstructed Chern character as an additive homomorphism on `K₀(Coh X)`. -/
noncomputable def totalChernCharacterHom
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P)) :
    CoherentGrothendieckGroup X →+ A :=
  ∑ i ∈ Finset.range (d + 1), R.chernCharacterHom RO i

/-- The total reconstructed Todd representative through the geometric dimension. -/
noncomputable def totalTodd (RO : P.ReconstructionData O) : A :=
  ∑ j ∈ Finset.range (d + 1), reconstructedToddComponent RO j

/-- The reconstructed right side of HRR as an additive homomorphism on `K₀(Coh X)`. -/
noncomputable def riemannRochHom
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P)) :
    CoherentGrothendieckGroup X →+ ℚ where
  toFun E := NumericalRing.degree (n := d)
    (totalChernCharacterHom RO R E * totalTodd RO)
  map_zero' := by simp [totalChernCharacterHom]
  map_add' E F := by
    rw [map_add, add_mul, map_add]

/-- The cohomological Euler homomorphism cast from `ℤ` to `ℚ`. -/
noncomputable def rationalEulerHom : CoherentGrothendieckGroup X →+ ℚ where
  toFun E := (D.grothendieckEulerHom C E : ℚ)
  map_zero' := by simp
  map_add' E F := by simp

@[simp]
theorem totalChernCharacterHom_class
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P))
    (F : Coh X.toScheme) :
    totalChernCharacterHom RO R (coherentGrothendieckClass F) =
      ∑ i ∈ Finset.range (d + 1),
        chernCharacterComponent RO (R.reconstruction F) i := by
  simp [totalChernCharacterHom]

@[simp]
theorem riemannRochHom_class
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P))
    (F : Coh X.toScheme) :
    riemannRochHom RO R (coherentGrothendieckClass F) =
      NumericalRing.degree (n := d)
        ((∑ i ∈ Finset.range (d + 1),
            chernCharacterComponent RO (R.reconstruction F) i) *
          (∑ j ∈ Finset.range (d + 1), reconstructedToddComponent RO j)) := by
  simp [riemannRochHom, totalTodd]

@[simp]
theorem rationalEulerHom_class (F : Coh X.toScheme) :
    rationalEulerHom (D := D) (C := C) (coherentGrothendieckClass F) =
      (D.eulerCharacteristic F : ℚ) := by
  simp [rationalEulerHom]

/-- Reconstructed HRR descends from coherent sheaves to every virtual Grothendieck class. -/
theorem hirzebruch_riemannRoch
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P))
    (hdpos : 1 ≤ d) (hd4 : d ≤ 4)
    (E : CoherentGrothendieckGroup X) :
    (D.grothendieckEulerHom C E : ℚ) = NumericalRing.degree (n := d)
      ((∑ i ∈ Finset.range (d + 1), R.chernCharacterHom RO i E) *
        (∑ j ∈ Finset.range (d + 1), reconstructedToddComponent RO j)) := by
  have hhom : rationalEulerHom (D := D) (C := C) = riemannRochHom RO R := by
    apply coherentGrothendieckGroup_hom_ext
    intro F
    rw [rationalEulerHom_class, riemannRochHom_class]
    exact sheaf_hirzebruch_riemannRoch RO R hdpos hd4 F
  simpa [rationalEulerHom, riemannRochHom, totalChernCharacterHom, totalTodd] using
    DFunLike.congr_fun hhom E

/-- The scheme-derived numerical variety reconstructed from Picard Euler polynomials.

The two inequalities are proofs, not mathematical input fields: they record the current
positive-dimension and codimension-four implementation bounds. -/
@[reducible]
noncomputable def toNumericalVariety
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P))
    (hdpos : 1 ≤ d) (hd4 : d ≤ 4) :
    NumericalVariety d A (CoherentGrothendieckGroup X) where
  toNumericalRing := inferInstance
  rank := R.rankHom
  chComp E i := R.chernCharacterHom RO i E
  chComp_mem := R.chernCharacterHom_mem RO
  chComp_zero := R.chernCharacterHom_zero RO
  chComp_add := R.chernCharacterHom_add RO
  toddComp := reconstructedToddComponent RO
  toddComp_mem := reconstructedToddComponent_mem RO
  toddComp_zero := reconstructedToddComponent_zero RO
  chi := D.grothendieckEulerHom C
  hirzebruch_riemannRoch := hirzebruch_riemannRoch RO R hdpos hd4

@[simp]
theorem toNumericalVariety_rank_class
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P))
    (hdpos : 1 ≤ d) (hd4 : d ≤ 4) (F : Coh X.toScheme) :
    (toNumericalVariety RO R hdpos hd4).rank (coherentGrothendieckClass F) =
      (R.reconstruction F).rank := by
  change R.rankHom (coherentGrothendieckClass F) = (R.reconstruction F).rank
  exact R.rankHom_class F

@[simp]
theorem toNumericalVariety_chComp_class
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P))
    (hdpos : 1 ≤ d) (hd4 : d ≤ 4)
    (F : Coh X.toScheme) (i : ℕ) :
    (toNumericalVariety RO R hdpos hd4).chComp (coherentGrothendieckClass F) i =
      chernCharacterComponent RO (R.reconstruction F) i := by
  change R.chernCharacterHom RO i (coherentGrothendieckClass F) =
    chernCharacterComponent RO (R.reconstruction F) i
  exact R.chernCharacterHom_class RO F i

@[simp]
theorem toNumericalVariety_toddComp
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P))
    (hdpos : 1 ≤ d) (hd4 : d ≤ 4) (i : ℕ) :
    (toNumericalVariety RO R hdpos hd4).toddComp i =
      reconstructedToddComponent RO i := rfl

@[simp]
theorem toNumericalVariety_chi_class
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P))
    (hdpos : 1 ≤ d) (hd4 : d ≤ 4) (F : Coh X.toScheme) :
    (toNumericalVariety RO R hdpos hd4).chi (coherentGrothendieckClass F) =
      D.eulerCharacteristic F := by
  change D.grothendieckEulerHom C (coherentGrothendieckClass F) =
    D.eulerCharacteristic F
  exact D.grothendieckEulerHom_class C F

/-- The numerical class of a coherent sheaf in the Euler-radical quotient fixed by Layer A. -/
noncomputable def numericalClass
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P))
    (hdpos : 1 ≤ d) (hd4 : d ≤ 4) (F : Coh X.toScheme) :
    letI := toNumericalVariety RO R hdpos hd4
    NumericalVariety.NumericalQuotient d A (CoherentGrothendieckGroup X) := by
  letI := toNumericalVariety RO R hdpos hd4
  exact Submodule.Quotient.mk (coherentGrothendieckClass F)

/-! ### Explicit threefold and fourfold constructors -/

/-- The scheme-derived dimension-three bridge requested by issue #45. -/
@[reducible]
noncomputable def toThreefoldNumericalVariety
    {A : Type v} [CommRing A] [Algebra ℚ A] [NumericalRing 3 A]
    {P : PairingContext D C 3 A} {O : Coh X.toScheme}
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P)) :
    NumericalVariety 3 A (CoherentGrothendieckGroup X) :=
  toNumericalVariety RO R (by omega) (by omega)

/-- The scheme-derived dimension-four bridge requested by issue #45. -/
@[reducible]
noncomputable def toFourfoldNumericalVariety
    {A : Type v} [CommRing A] [Algebra ℚ A] [NumericalRing 4 A]
    {P : PairingContext D C 4 A} {O : Coh X.toScheme}
    (RO : P.ReconstructionData O) (R : ReconstructionSystem (P := P)) :
    NumericalVariety 4 A (CoherentGrothendieckGroup X) :=
  toNumericalVariety RO R (by omega) (by omega)

/-- The existing Layer A threefold display, evaluated on a genuine coherent sheaf through the
scheme-derived bridge. -/
theorem threefold_eulerCharacteristic_eq
    {B : Type v} [CommRing B] [Algebra ℚ B] [NumericalRing 3 B]
    {P3 : PairingContext D C 3 B} {O3 : Coh X.toScheme}
    (RO : P3.ReconstructionData O3) (R : ReconstructionSystem (P := P3))
    (F : Coh X.toScheme) :
    (D.eulerCharacteristic F : ℚ) =
      ((R.reconstruction F).rank : ℚ) *
          NumericalRing.degree (n := 3) (reconstructedToddComponent RO 3) +
        NumericalRing.degree (n := 3)
          (chernCharacterComponent RO (R.reconstruction F) 1 *
            reconstructedToddComponent RO 2) +
        NumericalRing.degree (n := 3)
          (chernCharacterComponent RO (R.reconstruction F) 2 *
            reconstructedToddComponent RO 1) +
        NumericalRing.degree (n := 3)
          (chernCharacterComponent RO (R.reconstruction F) 3) := by
  letI : NumericalVariety 3 B (CoherentGrothendieckGroup X) :=
    toThreefoldNumericalVariety RO R
  simpa [toThreefoldNumericalVariety, toNumericalVariety] using
    (Threefold.chi_eq (A := B) (coherentGrothendieckClass F))

/-- The existing Layer A fourfold display, evaluated on a genuine coherent sheaf through the
scheme-derived bridge. -/
theorem fourfold_eulerCharacteristic_eq
    {B : Type v} [CommRing B] [Algebra ℚ B] [NumericalRing 4 B]
    {P4 : PairingContext D C 4 B} {O4 : Coh X.toScheme}
    (RO : P4.ReconstructionData O4) (R : ReconstructionSystem (P := P4))
    (F : Coh X.toScheme) :
    (D.eulerCharacteristic F : ℚ) =
      ((R.reconstruction F).rank : ℚ) *
          NumericalRing.degree (n := 4) (reconstructedToddComponent RO 4) +
        NumericalRing.degree (n := 4)
          (chernCharacterComponent RO (R.reconstruction F) 1 *
            reconstructedToddComponent RO 3) +
        NumericalRing.degree (n := 4)
          (chernCharacterComponent RO (R.reconstruction F) 2 *
            reconstructedToddComponent RO 2) +
        NumericalRing.degree (n := 4)
          (chernCharacterComponent RO (R.reconstruction F) 3 *
            reconstructedToddComponent RO 1) +
        NumericalRing.degree (n := 4)
          (chernCharacterComponent RO (R.reconstruction F) 4) := by
  letI : NumericalVariety 4 B (CoherentGrothendieckGroup X) :=
    toFourfoldNumericalVariety RO R
  simpa [toFourfoldNumericalVariety, toNumericalVariety] using
    (Fourfold.chi_eq (A := B) (coherentGrothendieckClass F))

end

end CohLean.RiemannRoch.HigherDimension
