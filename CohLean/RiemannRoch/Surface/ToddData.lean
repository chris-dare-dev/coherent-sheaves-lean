/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.RiemannRoch.Surface.Divisor
import CohLean.Intersection.ChernCharacter.Basic
import CohLean.Duality.Canonical.Basic
import CohLean.Numerical.RiemannRoch.K3

/-!
# Numerical Todd data for smooth proper surfaces

This file constructs the three Todd components needed by surface Riemann--Roch.  The
codimension-zero and codimension-one terms are the expected explicit classes

`td₀ = 1`,  `td₁ = -K_X / 2`.

The top component is not postulated.  It is the representative reconstructed from the
structure-sheaf twist polynomial, and its degree is proved to be the geometric Euler
characteristic `χ(O_X)`.  Representability of the twist functional remains explicit through
`PairingContext.ReconstructionData`; no global Chow group or hidden existence instance is used.

The resulting component family carries the grading and normalization statements expected by
`NumericalVariety`.  A final comparison theorem turns geometric K3 hypotheses into the existing
Layer A `K3.IsK3` class whenever a proposed `NumericalVariety` uses these components.
-/

universe u v w

open CategoryTheory

namespace CohLean.RiemannRoch.Surface.ToddData

open AlgebraicGeometry
open AlgebraicGeometry.Cohomology
open AlgebraicGeometry.Numerical
open AlgebraicGeometry.Scheme.Modules
open CohLean.Duality
open CohLean.Intersection.ChernCharacter
open CohLean.Intersection.ChernCharacterSurface
open CohLean.Intersection.Number

variable {k : Type u} [Field k]
variable {X : SmoothProperVariety k}
variable {D : FiniteCohomology X.toVariety}
variable {C : D.LinearConnectingSystem}
variable {A : Type v} [CommRing A] [Algebra ℚ A] [NumericalRing 2 A]

noncomputable section

private theorem homogeneousPicardCoefficient_nil
    (d : ℕ) (f : Pic X.toVariety.toScheme → ℤ) :
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

/-- The explicit geometric data used to construct the surface Todd components.

The structure-sheaf representative is required to realize the same Picard Euler function as
the intersection context.  Serre symmetry is included because it is what identifies the
linear Todd term with `-K_X/2`. -/
structure Data
    (P : PairingContext D C 2 A)
    (K : SmoothProperVariety.CanonicalSheafData X 2) where
  structureData : P.ReconstructionData
    (structureSheafObject P.intersection.structureSheafCoherent)
  structure_rank : structureData.rank = 1
  structure_twists : structureData.twists.eulerPic = P.intersection.eulerPic
  serre : Serre.Data.SurfacePicardSymmetry P.intersection K.canonicalClass

variable {P : PairingContext D C 2 A}
variable {K : SmoothProperVariety.CanonicalSheafData X 2}

/-- The canonical divisor class inside the chosen numerical intersection ring. -/
noncomputable def numericalCanonicalClass : A :=
  P.divisorClass K.canonicalClassAdd

/-- The codimension-zero Todd component. -/
def toddZero : A := 1

/-- The codimension-one Todd component `-K_X/2`. -/
noncomputable def toddOne : A :=
  -(algebraMap ℚ A (1 / 2) * numericalCanonicalClass (P := P) (K := K))

/-- The top Todd component reconstructed from the structure-sheaf twist polynomial. -/
noncomputable def toddTwo (T : Data P K) : A :=
  T.structureData.tauComponent 2

/-- The surface Todd components, extended by zero above the dimension. -/
noncomputable def toddComponent (T : Data P K) : ℕ → A
  | 0 => toddZero
  | 1 => toddOne (P := P) (K := K)
  | 2 => toddTwo T
  | _ => 0

theorem numericalCanonicalClass_mem :
    numericalCanonicalClass (P := P) (K := K) ∈ NumericalRing.piece (n := 2) 1 :=
  P.divisorClass_mem K.canonicalClassAdd

theorem toddZero_mem :
    toddZero (A := A) ∈ NumericalRing.piece (n := 2) 0 :=
  NumericalRing.one_mem_piece_zero

theorem toddOne_mem :
    toddOne (P := P) (K := K) ∈ NumericalRing.piece (n := 2) 1 := by
  unfold toddOne
  exact Submodule.neg_mem _ <| by
    simpa using NumericalRing.mul_mem_piece
      (NumericalRing.algebraMap_mem_piece_zero (n := 2) (A := A) (1 / 2))
      (numericalCanonicalClass_mem (P := P) (K := K))

theorem toddTwo_mem (T : Data P K) :
    toddTwo T ∈ NumericalRing.piece (n := 2) 2 :=
  T.structureData.tauComponent_mem 2

theorem toddComponent_mem (T : Data P K) (i : ℕ) :
    toddComponent T i ∈ NumericalRing.piece (n := 2) i := by
  rcases i with _ | _ | _ | i
  · exact toddZero_mem
  · exact toddOne_mem
  · exact toddTwo_mem T
  · exact Submodule.zero_mem _

@[simp] theorem toddComponent_zero (T : Data P K) :
    toddComponent T 0 = 1 :=
  rfl

@[simp] theorem toddComponent_one (T : Data P K) :
    toddComponent T 1 = toddOne (P := P) (K := K) :=
  rfl

@[simp] theorem toddComponent_two (T : Data P K) :
    toddComponent T 2 = toddTwo T :=
  rfl

theorem toddComponent_eq_zero_of_two_lt (T : Data P K)
    {i : ℕ} (hi : 2 < i) : toddComponent T i = 0 := by
  rcases i with _ | _ | _ | i <;> simp [toddComponent] at hi ⊢

/-- The reconstructed top Todd component has degree `χ(O_X)`, derived from the
structure-sheaf twist polynomial rather than supplied as a Todd axiom. -/
theorem degree_toddTwo_eq_eulerPic_one (T : Data P K) :
    NumericalRing.degree (n := 2) (toddTwo T) =
      (P.intersection.eulerPic 1 : ℚ) := by
  have h := T.structureData.degree_tauComponent_mul_divisorProduct
    2 (by omega) [] (by simp)
  rw [PairingContext.twistPairing, homogeneousPicardCoefficient_nil] at h
  simpa [toddTwo, divisorProduct, T.structure_twists] using h

/-- Geometric form of the top normalization: `∫td₂ = χ(O_X)`. -/
theorem degree_toddTwo_eq_structureSheafEulerCharacteristic (T : Data P K) :
    NumericalRing.degree (n := 2) (toddTwo T) =
      (D.eulerCharacteristic
        (structureSheafObject P.intersection.structureSheafCoherent) : ℚ) := by
  rw [degree_toddTwo_eq_eulerPic_one T,
    eulerPic_one_eq_eulerCharacteristic_structureSheaf P.intersection]

/-- Realization of the intersection of the numerical canonical class with a divisor class. -/
theorem degree_numericalCanonicalClass_mul_divisorClass
    (L : Additive (Pic X.toVariety.toScheme)) :
    NumericalRing.degree (n := 2)
        (numericalCanonicalClass (P := P) (K := K) * P.divisorClass L) =
      (P.intersection.surfaceIntersectionPairing K.canonicalClassAdd L : ℤ) := by
  have h := P.degree_divisorProduct ![K.canonicalClass, L.toMul]
  rw [P.intersection.picardIntersectionNumber_fin2] at h
  change NumericalRing.degree (n := 2)
      (P.divisorClass (Additive.ofMul K.canonicalClass) * P.divisorClass L) =
    (P.intersection.surfaceIntersectionNumber K.canonicalClass L.toMul : ℚ)
  simpa [divisorProduct, numericalCanonicalClass] using h

/-- Serre symmetry identifies the degree-one Todd functional with `-K_X/2`. -/
theorem toddOnePairing_eq_neg_half_canonical (T : Data P K)
    (L : Additive (Pic X.toVariety.toScheme)) :
    toddOnePairing P.intersection L =
      -(P.intersection.surfaceIntersectionPairing K.canonicalClassAdd L : ℚ) / 2 := by
  have hrr := Surface.eulerPic_eq P.intersection T.serre L.toMul
  have hsymm := P.intersection.surfaceIntersectionPairing_symm
    K.canonicalClass L.toMul
  have hself : P.intersection.surfaceIntersectionPairing L L =
      P.intersection.surfaceIntersectionNumber L.toMul L.toMul := by
    simpa using P.intersection.surfaceIntersectionPairing_apply L.toMul L.toMul
  rw [toddOnePairing_apply]
  push_cast
  rw [hrr]
  unfold Surface.correctionNumerator
  change _ = -(P.intersection.surfaceIntersectionNumber K.canonicalClass L.toMul : ℚ) / 2
  change P.intersection.surfaceIntersectionNumber K.canonicalClass L.toMul =
    P.intersection.surfaceIntersectionNumber L.toMul K.canonicalClass at hsymm
  rw [hsymm, hself]
  push_cast
  ring

/-- Ring-valued form of `td₁ = -K_X/2`, tested against every divisor class. -/
theorem degree_toddOne_mul_divisorClass (T : Data P K)
    (L : Additive (Pic X.toVariety.toScheme)) :
    NumericalRing.degree (n := 2)
        (toddOne (P := P) (K := K) * P.divisorClass L) =
      toddOnePairing P.intersection L := by
  rw [toddOne, neg_mul, map_neg]
  rw [mul_assoc, NumericalRing.degree_algebraMap_mul,
    degree_numericalCanonicalClass_mul_divisorClass (P := P) (K := K) L,
    toddOnePairing_eq_neg_half_canonical T L]
  ring

/-- Trivial canonical class forces the geometric first Todd component to vanish. -/
theorem toddOne_eq_zero (hK : K.canonicalClass = 1) :
    toddOne (P := P) (K := K) = 0 := by
  simp [toddOne, numericalCanonicalClass, SmoothProperVariety.CanonicalSheafData.canonicalClassAdd,
    hK]

/-- K3 top normalization: `χ(O_X)=2` gives `∫td₂=2`. -/
theorem degree_toddTwo_eq_two (T : Data P K)
    (hchi : P.intersection.eulerPic 1 = 2) :
    NumericalRing.degree (n := 2) (toddTwo T) = 2 := by
  rw [degree_toddTwo_eq_eulerPic_one T, hchi]
  norm_num

/-- A proposed Layer A numerical variety uses the geometrically constructed Todd components. -/
structure NumericalVarietyComparison
    {B : Type v} [CommRing B] [Algebra ℚ B]
    {N : Type w} [AddCommGroup N] [NumericalVariety 2 B N]
    {PB : PairingContext D C 2 B}
    {KB : SmoothProperVariety.CanonicalSheafData X 2}
    (T : Data PB KB) : Prop where
  toddComp_eq : ∀ i,
    NumericalVariety.toddComp (A := B) (N := N) i = toddComponent T i

namespace NumericalVarietyComparison

variable {B : Type v} [CommRing B] [Algebra ℚ B]
variable {N : Type w} [AddCommGroup N] [NumericalVariety 2 B N]
variable {PB : PairingContext D C 2 B}
variable {KB : SmoothProperVariety.CanonicalSheafData X 2}

theorem toddComp_zero_eq (T : Data PB KB)
    (Q : NumericalVarietyComparison (N := N) T) :
    NumericalVariety.toddComp (A := B) (N := N) 0 = 1 := by
  rw [Q.toddComp_eq, toddComponent_zero]

theorem toddComp_one_eq (T : Data PB KB)
    (Q : NumericalVarietyComparison (N := N) T) :
    NumericalVariety.toddComp (A := B) (N := N) 1 =
      toddOne (P := PB) (K := KB) := by
  rw [Q.toddComp_eq, toddComponent_one]

theorem degree_toddComp_two_eq (T : Data PB KB)
    (Q : NumericalVarietyComparison (N := N) T) :
    NumericalRing.degree (n := 2)
        (NumericalVariety.toddComp (A := B) (N := N) 2) =
      (PB.intersection.eulerPic 1 : ℚ) := by
  rw [Q.toddComp_eq, toddComponent_two, degree_toddTwo_eq_eulerPic_one]

/-- The geometric Todd construction supplies the existing Layer A K3 hypotheses whenever the
Layer A variety is explicitly compared with it. -/
theorem toIsK3
    (T : Data PB KB) (Q : NumericalVarietyComparison (N := N) T)
    (hK : KB.canonicalClass = 1)
    (hchi : PB.intersection.eulerPic 1 = 2) :
    AlgebraicGeometry.Numerical.K3.IsK3 B N where
  toddComp_one := by
    rw [Q.toddComp_eq, toddComponent_one, toddOne_eq_zero hK]
  degree_toddComp_two := by
    rw [Q.toddComp_eq, toddComponent_two, degree_toddTwo_eq_two T hchi]

end NumericalVarietyComparison

end

end CohLean.RiemannRoch.Surface.ToddData
