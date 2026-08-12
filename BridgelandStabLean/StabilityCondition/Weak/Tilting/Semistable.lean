/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Weak.Tilting.Cohomology.Sequence
import BridgelandStabLean.StabilityCondition.Weak.HarderNarasimhan.Heart
import BridgelandStabLean.StabilityCondition.Weak.Tilting.Property

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Semistable objects after tilting a weak stability condition

This file develops the phase-language counterpart of Lemma 14.17 of
arXiv:1902.08184v4.  The slope cutoff in the paper is represented by a phase
cutoff `beta` in `[0, 1)`, as in `SlopeTorsionPair.lean`.  The converse uses
`0 < beta`, since a finite slope cutoff corresponds to a phase cut strictly
inside `(0, 1)`.  The numerical reparameterisation between the two cutoffs is
deliberately not asserted.

The first construction is the weak stability function on the HRS-tilted
heart.  Its charge is the original charge rotated clockwise through
`pi * beta`.  Every object of the tilted heart has all old slicing phases in
`(beta, beta + 1]`; decomposing it into its old HN factors therefore proves
the weak upper-half-plane condition directly, including zero-charge factors.

The two source-shaped classes are defined and proved semistable.  Conversely,
the canonical original-cohomology sequence and strict old-HN phase separation
force every nonzero-charge tilted-semistable object into one of those classes.
The final `moreover` clause is proved by factoring maps through their image in
the abelian tilted heart: positive imaginary charge gives the semistable case,
and the strict `IsStable` predicate gives the boundary case.
-/

namespace BridgelandStabLean.WeakStability

open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated Complex
open BridgelandStabLean.Tilting
open scoped BigOperators ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]

variable {Lambda : Type*} [AddCommGroup Lambda]
variable {v : K₀ C →+ Lambda}

namespace WeakPreStabilityCondition

/-- Clockwise rotation through `pi * beta`, as an additive endomorphism of
the complex plane. -/
noncomputable def phaseTiltRotation (beta : ℝ) : ℂ →+ ℂ where
  toFun z := z * Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)
  map_zero' := by simp
  map_add' z w := by rw [add_mul]

@[simp]
theorem phaseTiltRotation_apply (beta : ℝ) (z : ℂ) :
    phaseTiltRotation beta z =
      z * Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := rfl

/-- The central charge rotated clockwise through the phase cutoff. -/
noncomputable def phaseTiltCharge
    (sigma : WeakPreStabilityCondition v) (beta : ℝ) : K₀ C →+ ℂ :=
  (phaseTiltRotation beta).comp (sigma.Z.comp v)

omit [IsTriangulated C] in
@[simp]
theorem phaseTiltCharge_apply
    (sigma : WeakPreStabilityCondition v) (beta : ℝ) (E : C) :
    sigma.phaseTiltCharge beta (K₀.of C E) =
      sigma.Z (v (K₀.of C E)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := rfl

private def WeakUpperClosed (z : ℂ) : Prop :=
  0 ≤ z.im ∧ (z.im = 0 → z.re ≤ 0)

private theorem weakUpperClosed_zero : WeakUpperClosed 0 := by
  constructor <;> simp

private theorem weakUpperClosed_add {z w : ℂ}
    (hz : WeakUpperClosed z) (hw : WeakUpperClosed w) :
    WeakUpperClosed (z + w) := by
  constructor
  · simpa using add_nonneg hz.1 hw.1
  · intro him
    have hz_nonneg := hz.1
    have hw_nonneg := hw.1
    have hz0 : z.im = 0 := by
      simp only [Complex.add_im] at him
      linarith
    have hw0 : w.im = 0 := by
      simp only [Complex.add_im] at him
      linarith
    simp only [Complex.add_re]
    exact add_nonpos (hz.2 hz0) (hw.2 hw0)

private theorem weakUpperClosed_sum {I : Type*} [Fintype I] (f : I → ℂ)
    (hf : ∀ i, WeakUpperClosed (f i)) :
    WeakUpperClosed (∑ i, f i) := by
  classical
  exact Finset.sum_induction f WeakUpperClosed
    (fun _ _ => weakUpperClosed_add) weakUpperClosed_zero
    (by intro i _; exact hf i)

private theorem weakUpperClosed_eq_zero_of_sum_eq_zero
    {I : Type*} [Fintype I] (f : I → ℂ)
    (hf : ∀ i, WeakUpperClosed (f i)) (hsum : ∑ i, f i = 0) (i : I) :
    f i = 0 := by
  classical
  have himsum : ∑ j, (f j).im = 0 := by
    have := congrArg Complex.im hsum
    simpa using this
  have him : (f i).im = 0 :=
    congrFun ((Fintype.sum_eq_zero_iff_of_nonneg fun j => (hf j).1).mp himsum) i
  have hre_nonpos : ∀ j, (f j).re ≤ 0 := fun j =>
    (hf j).2 (congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg fun k => (hf k).1).mp himsum) j)
  have hresum : ∑ j, -(f j).re = 0 := by
    have hre := congrArg Complex.re hsum
    have : ∑ j, (f j).re = 0 := by simpa using hre
    simpa using congrArg Neg.neg this
  have hre : -(f i).re = 0 :=
    congrFun
      ((Fintype.sum_eq_zero_iff_of_nonneg fun j => neg_nonneg.mpr (hre_nonpos j)).mp
        hresum) i
  apply Complex.ext <;> simp_all

private theorem rotatedRay_weakUpperClosed {beta phi m : ℝ}
    (hm : 0 ≤ m) (hphi : phi ∈ Set.Ioc beta (beta + 1)) :
    WeakUpperClosed
      ((m : ℂ) * Complex.exp (((Real.pi * phi : ℝ) : ℂ) * Complex.I) *
        Complex.exp (-((Real.pi : ℂ) * (beta : ℂ)) * Complex.I)) := by
  have hdelta_pos : 0 < phi - beta := by linarith [hphi.1]
  have hdelta_le : phi - beta ≤ 1 := by linarith [hphi.2]
  have hrewrite :
      (m : ℂ) * Complex.exp (((Real.pi * phi : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-((Real.pi : ℂ) * (beta : ℂ)) * Complex.I) =
        (m : ℂ) *
          Complex.exp (((Real.pi * (phi - beta) : ℝ) : ℂ) * Complex.I) := by
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hrewrite, Complex.exp_ofReal_mul_I]
  unfold WeakUpperClosed
  simp only [Complex.mul_im, Complex.add_im, Complex.add_re, Complex.ofReal_re,
    Complex.ofReal_im,
    Complex.I_im, Complex.I_re, zero_mul, mul_zero, mul_one, add_zero,
    zero_add, Complex.mul_re, sub_zero]
  change
    0 ≤ m * Real.sin (Real.pi * (phi - beta)) ∧
      (m * Real.sin (Real.pi * (phi - beta)) = 0 →
        m * Real.cos (Real.pi * (phi - beta)) ≤ 0)
  constructor
  · exact mul_nonneg hm
      (Real.sin_nonneg_of_nonneg_of_le_pi
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))
  · intro him
    rcases mul_eq_zero.mp him with hm0 | hsin0
    · simp [hm0]
    have hdelta : phi - beta = 1 := by
      by_contra hne
      have hdelta_lt : phi - beta < 1 := lt_of_le_of_ne hdelta_le hne
      have hsin_pos : 0 < Real.sin (Real.pi * (phi - beta)) :=
        Real.sin_pos_of_pos_of_lt_pi
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      exact (ne_of_gt hsin_pos) hsin0
    rw [hdelta]
    simpa using neg_nonpos.mpr hm

private def cross (z w : ℂ) : ℝ :=
  z.re * w.im - z.im * w.re

private theorem cross_phaseTiltRotation (beta : ℝ) (z w : ℂ) :
    cross (phaseTiltRotation beta z) (phaseTiltRotation beta w) = cross z w := by
  rw [phaseTiltRotation_apply, phaseTiltRotation_apply]
  let c := Real.cos (Real.pi * beta)
  let s := Real.sin (Real.pi * beta)
  have hexp :
      Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) = (c : ℂ) - (s : ℂ) * Complex.I := by
    rw [show -(Real.pi * beta : ℂ) * Complex.I =
        ((-(Real.pi * beta) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I]
    simp [c, s]
    ring
  rw [hexp]
  unfold cross
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, zero_sub]
  have htrig : c ^ 2 + s ^ 2 = 1 := by
    dsimp [c, s]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * beta)]
  rw [show
      (z.re * c - z.im * -(s + 0)) * (w.re * -(s + 0) + w.im * c) -
          (z.re * -(s + 0) + z.im * c) * (w.re * c - w.im * -(s + 0)) =
        (c ^ 2 + s ^ 2) * (z.re * w.im - z.im * w.re) by ring,
    htrig, one_mul]

private theorem cross_phaseTiltRotation_neg_left (beta : ℝ) (z w : ℂ) :
    cross (phaseTiltRotation beta (-z)) (phaseTiltRotation beta w) = -cross z w := by
  rw [cross_phaseTiltRotation]
  simp [cross]
  ring

private theorem cross_phaseTiltRotation_neg_right (beta : ℝ) (z w : ℂ) :
    cross (phaseTiltRotation beta z) (phaseTiltRotation beta (-w)) = -cross z w := by
  rw [cross_phaseTiltRotation]
  simp [cross]
  ring

omit [IsTriangulated C] in
/-- A positive oriented area between two nonzero weak upper-half-plane
charges is the strict slope inequality. -/
private theorem slope_lt_of_cross_pos {t : TStructure C}
    (W : WeakStabilityFunction t) {A B : C}
    (hA : t.heart A) (hB : t.heart B) (hA0 : ¬IsZero A) (hB0 : ¬IsZero B)
    (hcross : 0 < cross (W.charge A) (W.charge B)) :
    W.slope A < W.slope B := by
  have hAim : 0 < (W.charge A).im := by
    rcases W.upper A hA hA0 with him | ⟨him, hre⟩
    · exact him
    · have hBim : 0 ≤ (W.charge B).im := by
        rcases W.upper B hB hB0 with himB | ⟨himB, -⟩
        · exact himB.le
        · exact himB.ge
      unfold cross at hcross
      rw [him] at hcross
      simp only [zero_mul, sub_zero] at hcross
      nlinarith
  by_cases hBim : 0 < (W.charge B).im
  · rw [W.slope_of_im_pos hAim, W.slope_of_im_pos hBim]
    exact_mod_cast (div_lt_div_iff₀ hAim hBim).2 (by
      unfold cross at hcross
      nlinarith)
  · rw [W.slope_of_im_pos hAim, W.slope_of_im_nonpos hBim]
    exact WithTop.coe_lt_top _

/-- The lower HN phase bounds the argument of every nonzero total charge in
the original heart.  This extends the positive-imaginary lemma to the
negative-real boundary ray. -/
private theorem pi_mul_phiMinus_le_charge_arg_of_charge_ne_zero
    (sigma : WeakPreStabilityCondition v) (E : C)
    (hheart : sigma.slicing.toTStructure.heart E)
    (hcharge : sigma.weakStabilityFunctionOnHeart.charge E ≠ 0) :
    Real.pi * sigma.slicing.phiMinus C E
        (fun hE => hcharge (sigma.weakStabilityFunctionOnHeart.charge_isZero hE)) ≤
      Complex.arg (sigma.weakStabilityFunctionOnHeart.charge E) := by
  let W := sigma.weakStabilityFunctionOnHeart
  have hE : ¬IsZero E := fun hE => hcharge (W.charge_isZero hE)
  by_cases him : 0 < (W.charge E).im
  · exact sigma.pi_mul_phiMinus_le_charge_arg_of_im_pos E hheart hE him
  · have him0 : (W.charge E).im = 0 := by
      rcases W.upper E hheart hE with him' | ⟨him', -⟩
      · exact absurd him' him
      · exact him'
    have hrele : (W.charge E).re ≤ 0 := by
      rcases W.upper E hheart hE with him' | ⟨-, hre⟩
      · exact absurd him' him
      · exact hre
    have hrelt : (W.charge E).re < 0 := lt_of_le_of_ne hrele fun hre0 => by
      apply hcharge
      exact Complex.ext hre0 him0
    have harg : Complex.arg (W.charge E) = Real.pi := by
      rw [show W.charge E = ((W.charge E).re : ℂ) from Complex.ext rfl him0,
        Complex.arg_ofReal_of_neg hrelt]
    rw [harg]
    have hle : sigma.slicing.phiMinus C E hE ≤ 1 :=
      (sigma.slicing.phiMinus_le_phiPlus C E hE).trans
        (sigma.slicing.phiPlus_le_of_leProp C hE
          ((sigma.slicing.toTStructure_heart_iff C E).mp hheart).2)
    nlinarith [Real.pi_pos]

/-- A nonzero charged torsion-class object lies in the open upper half-plane
after a nontrivial phase rotation. -/
theorem phaseTiltCharge_im_pos_of_phaseTors
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    (hbeta0 : 0 < beta) {E : C}
    (hE : phaseTors sigma.slicing beta E)
    (hcharge :
      phaseTiltRotation beta
        (sigma.weakStabilityFunctionOnHeart.charge E) ≠ 0) :
    0 < (phaseTiltRotation beta
      (sigma.weakStabilityFunctionOnHeart.charge E)).im := by
  let W0 := sigma.weakStabilityFunctionOnHeart
  have hheart : sigma.slicing.toTStructure.heart E :=
    mem_heart_of_bounds sigma.slicing
      (sigma.slicing.gtProp_anti C hbeta0.le E hE.1) hE.2
  have hZ0 : W0.charge E ≠ 0 := by
    intro hz
    apply hcharge
    rw [show W0.charge E = 0 from hz]
    exact map_zero (phaseTiltRotation beta)
  have hE0 : ¬IsZero E := fun hzero => hZ0 (W0.charge_isZero hzero)
  have hlower :=
    pi_mul_phiMinus_le_charge_arg_of_charge_ne_zero sigma E hheart hZ0
  have hphase : beta < sigma.slicing.phiMinus C E hE0 :=
    sigma.slicing.phiMinus_gt_of_gtProp C hE0 hE.1
  have harg_lower : Real.pi * beta < Complex.arg (W0.charge E) := by
    nlinarith [Real.pi_pos]
  have hangle_pos : 0 < Complex.arg (W0.charge E) - Real.pi * beta := by
    linarith
  have hangle_lt : Complex.arg (W0.charge E) - Real.pi * beta < Real.pi := by
    nlinarith [Complex.arg_le_pi (W0.charge E), Real.pi_pos]
  have him : (phaseTiltRotation beta (W0.charge E)).im =
      ‖W0.charge E‖ * Real.sin (Complex.arg (W0.charge E) - Real.pi * beta) := by
    change (W0.charge E *
      Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)).im = _
    have polar := Complex.norm_mul_exp_arg_mul_I (W0.charge E)
    conv_lhs => rw [← polar]
    rw [mul_assoc, ← Complex.exp_add]
    have hexp :
        (Complex.arg (W0.charge E) : ℂ) * Complex.I +
            -(Real.pi * beta : ℂ) * Complex.I =
          ((Complex.arg (W0.charge E) - Real.pi * beta : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hexp]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.exp_ofReal_mul_I_im]
  rw [him]
  exact mul_pos (norm_pos_iff.mpr hZ0)
    (Real.sin_pos_of_pos_of_lt_pi hangle_pos hangle_lt)

/-- Strict phase separation below phase `1` gives strict slope separation
after rotation. -/
theorem phaseTilt_slope_lt_of_phase_separated
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    {tTilt : TStructure C} (W : WeakStabilityFunction tTilt) {A B : C}
    (hAheart : sigma.slicing.toTStructure.heart A)
    (hBheart : sigma.slicing.toTStructure.heart B)
    (hAtilt : tTilt.heart A) (hBtilt : tTilt.heart B)
    (hWA : W.charge A = phaseTiltRotation beta
      (sigma.weakStabilityFunctionOnHeart.charge A))
    (hWB : W.charge B = phaseTiltRotation beta
      (sigma.weakStabilityFunctionOnHeart.charge B))
    (hA0 : ¬IsZero A) (hB0 : ¬IsZero B)
    (hsep : sigma.slicing.phiPlus C A hA0 < sigma.slicing.phiMinus C B hB0)
    (hAplus : sigma.slicing.phiPlus C A hA0 < 1)
    (hBcharge : sigma.weakStabilityFunctionOnHeart.charge B ≠ 0) :
    W.slope A < W.slope B := by
  let W0 := sigma.weakStabilityFunctionOnHeart
  obtain ⟨hAupper, hAarg⟩ :=
    sigma.charge_mem_upperHalfPlane_and_arg_le_phiPlus A hAheart hA0 hAplus
  have hBarg :=
    pi_mul_phiMinus_le_charge_arg_of_charge_ne_zero sigma B hBheart hBcharge
  have harglt : Complex.arg (W0.charge A) < Complex.arg (W0.charge B) := by
    calc
      Complex.arg (W0.charge A) ≤
          Real.pi * sigma.slicing.phiPlus C A hA0 := hAarg
      _ < Real.pi * sigma.slicing.phiMinus C B hB0 :=
        mul_lt_mul_of_pos_left hsep Real.pi_pos
      _ ≤ Complex.arg (W0.charge B) := hBarg
  have hAcrossB : 0 < cross (W0.charge A) (W0.charge B) :=
    cross_pos_of_arg_lt (arg_pos_of_mem_upperHalfPlaneUnion hAupper)
      (upperHalfPlaneUnion_ne_zero hAupper) hBcharge harglt
  have hcross : 0 < cross (W.charge A) (W.charge B) := by
    rw [hWA, hWB]
    rw [cross_phaseTiltRotation]
    exact hAcrossB
  exact slope_lt_of_cross_pos W hAtilt hBtilt hA0 hB0 hcross

/-- The shifted version of strict phase/slope separation.  This public form
is used by the `H⁻¹` quotient induction for the weak upper tilt. -/
theorem phaseTilt_slope_shift_lt_shift_of_phase_separated
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    {tTilt : TStructure C} (W : WeakStabilityFunction tTilt) {A B : C}
    (hAheart : sigma.slicing.toTStructure.heart A)
    (hBheart : sigma.slicing.toTStructure.heart B)
    (hAtilt : tTilt.heart (A⟦(1 : ℤ)⟧))
    (hBtilt : tTilt.heart (B⟦(1 : ℤ)⟧))
    (hWA : W.charge (A⟦(1 : ℤ)⟧) = phaseTiltRotation beta
      (-(sigma.weakStabilityFunctionOnHeart.charge A)))
    (hWB : W.charge (B⟦(1 : ℤ)⟧) = phaseTiltRotation beta
      (-(sigma.weakStabilityFunctionOnHeart.charge B)))
    (hA0 : ¬IsZero A) (hB0 : ¬IsZero B)
    (hsep : sigma.slicing.phiPlus C A hA0 < sigma.slicing.phiMinus C B hB0)
    (hAplus : sigma.slicing.phiPlus C A hA0 < 1)
    (hBcharge : sigma.weakStabilityFunctionOnHeart.charge B ≠ 0) :
    W.slope (A⟦(1 : ℤ)⟧) < W.slope (B⟦(1 : ℤ)⟧) := by
  let W0 := sigma.weakStabilityFunctionOnHeart
  obtain ⟨hAupper, hAarg⟩ :=
    sigma.charge_mem_upperHalfPlane_and_arg_le_phiPlus A hAheart hA0 hAplus
  have hBarg :=
    pi_mul_phiMinus_le_charge_arg_of_charge_ne_zero sigma B hBheart hBcharge
  have harglt : Complex.arg (W0.charge A) < Complex.arg (W0.charge B) := by
    calc
      Complex.arg (W0.charge A) ≤
          Real.pi * sigma.slicing.phiPlus C A hA0 := hAarg
      _ < Real.pi * sigma.slicing.phiMinus C B hB0 :=
        mul_lt_mul_of_pos_left hsep Real.pi_pos
      _ ≤ Complex.arg (W0.charge B) := hBarg
  have hAcrossB : 0 < cross (W0.charge A) (W0.charge B) :=
    cross_pos_of_arg_lt (arg_pos_of_mem_upperHalfPlaneUnion hAupper)
      (upperHalfPlaneUnion_ne_zero hAupper) hBcharge harglt
  have hcross : 0 < cross (W.charge (A⟦(1 : ℤ)⟧)) (W.charge (B⟦(1 : ℤ)⟧)) := by
    rw [hWA, hWB]
    rw [cross_phaseTiltRotation]
    simpa [cross, W0, WeakStabilityFunction.charge] using hAcrossB
  have hAshift0 : ¬IsZero (A⟦(1 : ℤ)⟧) := fun hzero =>
    hA0 (by
      rw [IsZero.iff_id_eq_zero] at hzero ⊢
      exact (Functor.map_eq_zero_iff (shiftFunctor C (1 : ℤ))).mp (by simpa using hzero))
  have hBshift0 : ¬IsZero (B⟦(1 : ℤ)⟧) := fun hzero =>
    hB0 (by
      rw [IsZero.iff_id_eq_zero] at hzero ⊢
      exact (Functor.map_eq_zero_iff (shiftFunctor C (1 : ℤ))).mp (by simpa using hzero))
  exact slope_lt_of_cross_pos W hAtilt hBtilt hAshift0 hBshift0 hcross

/-- A higher-phase unshifted factor has smaller tilted slope than the shift
of a lower-phase factor. -/
theorem phaseTilt_slope_unshifted_lt_shifted_of_phase_separated
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    {tTilt : TStructure C} (W : WeakStabilityFunction tTilt) {U V : C}
    (hUheart : sigma.slicing.toTStructure.heart U)
    (hVheart : sigma.slicing.toTStructure.heart V)
    (hUshiftTilt : tTilt.heart (U⟦(1 : ℤ)⟧))
    (hVtilt : tTilt.heart V)
    (hWU : W.charge (U⟦(1 : ℤ)⟧) = phaseTiltRotation beta
      (-(sigma.weakStabilityFunctionOnHeart.charge U)))
    (hWV : W.charge V = phaseTiltRotation beta
      (sigma.weakStabilityFunctionOnHeart.charge V))
    (hU0 : ¬IsZero U) (hV0 : ¬IsZero V)
    (hsep : sigma.slicing.phiPlus C U hU0 < sigma.slicing.phiMinus C V hV0)
    (hUplus : sigma.slicing.phiPlus C U hU0 < 1)
    (hVcharge : sigma.weakStabilityFunctionOnHeart.charge V ≠ 0) :
    W.slope V < W.slope (U⟦(1 : ℤ)⟧) := by
  let W0 := sigma.weakStabilityFunctionOnHeart
  obtain ⟨hUupper, hUarg⟩ :=
    sigma.charge_mem_upperHalfPlane_and_arg_le_phiPlus U hUheart hU0 hUplus
  have hVarg :=
    pi_mul_phiMinus_le_charge_arg_of_charge_ne_zero sigma V hVheart hVcharge
  have harglt : Complex.arg (W0.charge U) < Complex.arg (W0.charge V) := by
    calc
      Complex.arg (W0.charge U) ≤
          Real.pi * sigma.slicing.phiPlus C U hU0 := hUarg
      _ < Real.pi * sigma.slicing.phiMinus C V hV0 :=
        mul_lt_mul_of_pos_left hsep Real.pi_pos
      _ ≤ Complex.arg (W0.charge V) := hVarg
  have hUcrossV : 0 < cross (W0.charge U) (W0.charge V) :=
    cross_pos_of_arg_lt (arg_pos_of_mem_upperHalfPlaneUnion hUupper)
      (upperHalfPlaneUnion_ne_zero hUupper) hVcharge harglt
  have hcross : 0 < cross (W.charge V) (W.charge (U⟦(1 : ℤ)⟧)) := by
    rw [hWV, hWU]
    rw [cross_phaseTiltRotation_neg_right]
    unfold cross at hUcrossV ⊢
    linarith
  have hUshift0 : ¬IsZero (U⟦(1 : ℤ)⟧) := fun hzero =>
    hU0 (by
      rw [IsZero.iff_id_eq_zero] at hzero ⊢
      exact (Functor.map_eq_zero_iff (shiftFunctor C (1 : ℤ))).mp (by simpa using hzero))
  exact slope_lt_of_cross_pos W hVtilt hUshiftTilt hV0 hUshift0 hcross

private theorem ray_cross_nonneg {psi theta m n : ℝ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hpsi : 0 < psi)
    (horder : psi ≤ theta) (htheta : theta ≤ 1) :
    0 ≤ cross
      ((m : ℂ) * Complex.exp (((Real.pi * psi : ℝ) : ℂ) * Complex.I))
      ((n : ℂ) * Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I)) := by
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  unfold cross
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, mul_one, add_zero, zero_add]
  rw [show
      m * Real.cos (Real.pi * psi) * (n * Real.sin (Real.pi * theta)) -
          m * Real.sin (Real.pi * psi) * (n * Real.cos (Real.pi * theta)) =
        (m * n) * Real.sin (Real.pi * (theta - psi)) by
      rw [show Real.pi * (theta - psi) = Real.pi * theta - Real.pi * psi by ring,
        Real.sin_sub]
      ring]
  exact mul_nonneg (mul_nonneg hm hn)
    (Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))

omit [IsTriangulated C] in
private theorem rotatedCharge_weakUpperClosed_of_interval
    (sigma : WeakPreStabilityCondition v) {beta : ℝ} {E : C}
    (hgt : sigma.slicing.gtProp C beta E)
    (hle : sigma.slicing.leProp C (beta + 1) E) :
    WeakUpperClosed
      (sigma.Z (v (K₀.of C E)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)) := by
  classical
  by_cases hE : IsZero E
  · simpa [K₀.of_isZero C hE] using weakUpperClosed_zero
  obtain ⟨F, hn, hfirst, hlast⟩ :=
    HNFiltration.exists_both_nonzero C sigma.slicing hE
  let P := F.toPostnikovTower
  have hphase : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc beta (beta + 1) := by
    intro i
    constructor
    · calc
        beta < sigma.slicing.phiMinus C E hE :=
          sigma.slicing.phiMinus_gt_of_gtProp C hE hgt
        _ = F.φ ⟨F.n - 1, by lia⟩ := by
          rw [sigma.slicing.phiMinus_eq C E hE F hn hlast]
        _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
    · calc
        F.φ i ≤ F.φ ⟨0, hn⟩ :=
          F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
        _ = sigma.slicing.phiPlus C E hE := by
          rw [sigma.slicing.phiPlus_eq C E hE F hn hfirst]
        _ ≤ beta + 1 := sigma.slicing.phiPlus_le_of_leProp C hE hle
  have hsum :
      sigma.Z (v (K₀.of C E)) *
          Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) =
        ∑ i : Fin F.n,
          sigma.Z (v (K₀.of C (P.factor i))) *
            Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum, map_sum, Finset.sum_mul]
  rw [hsum]
  apply weakUpperClosed_sum
  intro i
  by_cases hi : IsZero (P.factor i)
  · simpa [K₀.of_isZero C hi] using weakUpperClosed_zero
  obtain ⟨m, hm, -, hmZ⟩ :=
    sigma.compat' (F.φ i) (P.factor i) (F.semistable i) hi
  rw [hmZ]
  exact rotatedRay_weakUpperClosed hm (hphase i)

omit [IsTriangulated C] in
private theorem rotatedCharge_cross_ray_nonneg_of_bounds
    (sigma : WeakPreStabilityCondition v) {beta theta n : ℝ} {A : C}
    (hn : 0 ≤ n) (htheta : theta ≤ 1)
    (hgt : sigma.slicing.gtProp C beta A)
    (hle : sigma.slicing.leProp C (beta + theta) A) :
    0 ≤ cross
      (sigma.Z (v (K₀.of C A)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I))
      ((n : ℂ) *
        Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I)) := by
  classical
  by_cases hA : IsZero A
  · simp [K₀.of_isZero C hA, cross]
  obtain ⟨F, hFn, hfirst, hlast⟩ :=
    HNFiltration.exists_both_nonzero C sigma.slicing hA
  let P := F.toPostnikovTower
  let z : ℂ := (n : ℂ) *
    Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I)
  let f : Fin F.n → ℂ := fun i =>
    sigma.Z (v (K₀.of C (P.factor i))) *
      Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)
  have hphase : ∀ i : Fin F.n,
      0 < F.φ i - beta ∧ F.φ i - beta ≤ theta := by
    intro i
    constructor
    · calc
        0 < sigma.slicing.phiMinus C A hA - beta := by
          linarith [sigma.slicing.phiMinus_gt_of_gtProp C hA hgt]
        _ = F.φ ⟨F.n - 1, by lia⟩ - beta := by
          rw [sigma.slicing.phiMinus_eq C A hA F hFn hlast]
        _ ≤ F.φ i - beta := by
          have hi : i ≤ (⟨F.n - 1, by lia⟩ : Fin F.n) :=
            Fin.mk_le_mk.mpr (by lia)
          linarith [F.hφ.antitone hi]
    · calc
        F.φ i - beta ≤ F.φ ⟨0, hFn⟩ - beta := by
          have hi : (⟨0, hFn⟩ : Fin F.n) ≤ i :=
            Fin.mk_le_mk.mpr (Nat.zero_le _)
          linarith [F.hφ.antitone hi]
        _ = sigma.slicing.phiPlus C A hA - beta := by
          rw [sigma.slicing.phiPlus_eq C A hA F hFn hfirst]
        _ ≤ theta := by
          linarith [sigma.slicing.phiPlus_le_of_leProp C hA hle]
  have hsum :
      sigma.Z (v (K₀.of C A)) *
          Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) =
        ∑ i, f i := by
    rw [K₀.of_postnikovTower_eq_sum C P, map_sum, map_sum, Finset.sum_mul]
  rw [hsum]
  change 0 ≤ cross (∑ i, f i) z
  rw [show cross (∑ i, f i) z = ∑ i, cross (f i) z by
    simp [cross, Finset.sum_mul, ← Finset.sum_sub_distrib]]
  apply Finset.sum_nonneg
  intro i _
  by_cases hi : IsZero (P.factor i)
  · simp [f, K₀.of_isZero C hi, cross]
  obtain ⟨m, hm, -, hmZ⟩ :=
    sigma.compat' (F.φ i) (P.factor i) (F.semistable i) hi
  have hrot : f i =
      (m : ℂ) *
        Complex.exp (((Real.pi * (F.φ i - beta) : ℝ) : ℂ) * Complex.I) := by
    dsimp [f]
    rw [hmZ, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [hrot]
  exact ray_cross_nonneg hm hn (hphase i).1 (hphase i).2 htheta

/-- A tilted-heart object has all old slicing phases in `(beta, beta + 1]`.
This is the sector form of the HRS heart description. -/
theorem phaseTiltHeart_interval
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E : C}
    (hE : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E) :
    sigma.slicing.gtProp C beta E ∧
      sigma.slicing.leProp C (beta + 1) E := by
  obtain ⟨F, T, hF, hT, f, g, d, hdist⟩ :=
    (slicingTilt_heart_iff sigma.slicing hbeta0 hbeta1.le E).mp hE
  have hFgt : sigma.slicing.gtProp C beta (F⟦(1 : ℤ)⟧) := by
    have hshift := sigma.slicing.gtProp_shift C 0 F 1 hF.1
    have hshift' : sigma.slicing.gtProp C 1 (F⟦(1 : ℤ)⟧) := by
      simpa using hshift
    exact sigma.slicing.gtProp_anti C hbeta1.le _ hshift'
  have hFle : sigma.slicing.leProp C (beta + 1) (F⟦(1 : ℤ)⟧) := by
    simpa only [Int.cast_one] using
      sigma.slicing.leProp_shift C beta F 1 hF.2
  have hTgt : sigma.slicing.gtProp C beta T := hT.1
  have hTle : sigma.slicing.leProp C (beta + 1) T :=
    sigma.slicing.leProp_mono C (by linarith) T hT.2
  exact ⟨sigma.slicing.gtProp_of_triangle C beta hFgt hTgt hdist,
    sigma.slicing.leProp_of_triangle C (beta + 1) hFle hTle hdist⟩

/-- The HRS tilt at the phase cut is exactly the heart of the phase-shifted
slicing.  This identifies both descriptions with the interval
`P((beta, beta + 1])`. -/
theorem phaseTiltHeart_iff_phaseShiftHeart
    (sigma : WeakPreStabilityCondition v) {beta : ℝ}
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (E : C) :
    ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E ↔
      ((sigma.slicing.phaseShift C beta).toTStructure).heart E := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  constructor
  · intro hE
    obtain ⟨hgt, hle⟩ := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hE
    rw [(sigma.slicing.phaseShift C beta).toTStructure_heart_iff]
    exact ⟨(sigma.slicing.phaseShift_gtProp_zero C beta E).mpr hgt,
      (sigma.slicing.phaseShift_leProp C beta 1 E).mpr (by simpa [add_comm] using hle)⟩
  · intro hE
    have hbounds :=
      (sigma.slicing.phaseShift C beta).toTStructure_heart_iff C E |>.mp hE
    have hgt : sigma.slicing.gtProp C beta E :=
      (sigma.slicing.phaseShift_gtProp_zero C beta E).mp hbounds.1
    have hle : sigma.slicing.leProp C (beta + 1) E :=
      (sigma.slicing.phaseShift_leProp C beta 1 E).mp hbounds.2 |>
        (by simpa [add_comm] using ·)
    by_cases hzero : IsZero E
    · exact ObjectProperty.prop_of_iso (P.tilt).heart hzero.isoZero.symm
        (P.tors_mem_tilt_heart P.tors_zero)
    obtain ⟨F, hn, hfirst, hlast⟩ :=
      HNFiltration.exists_both_nonzero C sigma.slicing hzero
    have hphase : ∀ i : Fin F.n,
        beta < F.φ i ∧ F.φ i < beta + 2 := by
      intro i
      constructor
      · calc
          beta < sigma.slicing.phiMinus C E hzero :=
            sigma.slicing.phiMinus_gt_of_gtProp C hzero hgt
          _ = F.φ ⟨F.n - 1, by lia⟩ := by
            rw [sigma.slicing.phiMinus_eq C E hzero F hn hlast]
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc
          F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = sigma.slicing.phiPlus C E hzero := by
            rw [sigma.slicing.phiPlus_eq C E hzero F hn hfirst]
          _ ≤ beta + 1 := sigma.slicing.phiPlus_le_of_leProp C hzero hle
          _ < beta + 2 := by linarith
    obtain ⟨X, Y, f, g, d, hdist, hXgt, hYle, -⟩ :=
      sigma.slicing.exists_split_at_cutoff C F hphase hn (t := 1)
    have hXle : sigma.slicing.leProp C (beta + 1) X := by
      have hYshift : sigma.slicing.leProp C (beta + 1) (Y⟦(-1 : ℤ)⟧) := by
        have hshift := sigma.slicing.leProp_shift C 1 Y (-1) hYle
        exact sigma.slicing.leProp_mono C (by push_cast; linarith) _ hshift
      exact sigma.slicing.leProp_of_triangle C (beta + 1) hYshift hle
        (inv_rot_of_distTriang _ hdist)
    have hYgt : sigma.slicing.gtProp C beta Y := by
      have hXshift : sigma.slicing.gtProp C beta (X⟦(1 : ℤ)⟧) := by
        have hshift := sigma.slicing.gtProp_shift C 1 X 1 hXgt
        exact sigma.slicing.gtProp_anti C (by push_cast; linarith) _ hshift
      exact sigma.slicing.gtProp_of_triangle C beta hgt hXshift
        (rot_of_distTriang _ hdist)
    have hfree : phaseFree sigma.slicing beta (X⟦(-1 : ℤ)⟧) := by
      constructor
      · have hshift := sigma.slicing.gtProp_shift C 1 X (-1) hXgt
        convert hshift using 1
        all_goals push_cast
        all_goals ring
      · have hshift := sigma.slicing.leProp_shift C (beta + 1) X (-1) hXle
        convert hshift using 1
        all_goals push_cast
        all_goals ring
    have htors : phaseTors sigma.slicing beta Y := ⟨hYgt, hYle⟩
    let e : (X⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧ ≅ X :=
      (shiftFunctorCompIsoId C (-1 : ℤ) (1 : ℤ) (by lia)).app X
    have hdist' :
        Triangle.mk (e.hom ≫ f) g (d ≫ e.inv⟦(1 : ℤ)⟧') ∈ distTriang C := by
      refine isomorphic_distinguished _ hdist _ ?_
      exact Triangle.isoMk _ _ e (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp [← Functor.map_comp])
    exact P.tilt_heart_of_triangle hfree htors hdist'

/-- The phase-language tilted weak stability function.  Its heart is the HRS
tilt at the cutoff `beta`, and its charge is the original charge rotated
clockwise through `pi * beta`. -/
noncomputable def phaseTiltWeakStabilityFunction
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    WeakStabilityFunction
      (slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt where
  Z := sigma.phaseTiltCharge beta
  upper E hE _ := by
    obtain ⟨hgt, hle⟩ := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hE
    have hclosed :=
      rotatedCharge_weakUpperClosed_of_interval sigma hgt hle
    rcases lt_or_eq_of_le hclosed.1 with him | him
    · exact Or.inl him
    · exact Or.inr ⟨him.symm, hclosed.2 him.symm⟩

@[simp]
theorem phaseTiltWeakStabilityFunction_Z
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).Z =
      sigma.phaseTiltCharge beta := rfl

@[simp]
theorem phaseTiltWeakStabilityFunction_charge
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (E : C) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E =
      sigma.Z (v (K₀.of C E)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) := rfl

/-- A zero-charge object of the original slicing heart belongs to the
boundary slice `P(1)`. -/
theorem zeroCharge_mem_P_one
    (sigma : WeakPreStabilityCondition v) {E : C}
    (hEheart : sigma.slicing.toTStructure.heart E)
    (hZ : sigma.Z (v (K₀.of C E)) = 0) :
    sigma.slicing.P 1 E := by
  by_cases hzero : IsZero E
  · exact ObjectProperty.prop_of_iso (sigma.slicing.P 1) hzero.isoZero.symm
      (sigma.slicing.zero_mem 1)
  let W := sigma.weakStabilityFunctionOnHeart
  have hss : W.IsSemistable E := by
    refine ⟨hEheart, ?_⟩
    intro A B hA hB hA0 hB0 f g d hdist
    have hEzero : W.zeroCharge E := ⟨hEheart, hZ⟩
    have hAzero := W.zeroCharge_left hA hB hEzero hdist
    have hBzero := W.zeroCharge_right hA hB hEzero hdist
    rw [W.slope_of_im_nonpos (by simp [hAzero.2]),
      W.slope_of_im_nonpos (by simp [hBzero.2])]
  have hPplus := sigma.mem_P_phiPlus_of_weakStabilityFunctionOnHeart_isSemistable
    E hzero hss
  obtain ⟨m, hm, hm_strict, hmZ⟩ :=
    sigma.compat' (sigma.slicing.phiPlus C E hzero) E hPplus hzero
  have hm0c : (m : ℂ) = 0 := by
    rw [hZ, eq_comm, mul_eq_zero] at hmZ
    exact hmZ.resolve_right (Complex.exp_ne_zero _)
  have hm0 : m = 0 := by exact_mod_cast hm0c
  have hinter : ∃ n : ℤ, sigma.slicing.phiPlus C E hzero = (n : ℝ) := by
    by_contra h
    push Not at h
    have := hm_strict h
    linarith
  obtain ⟨n, hncast⟩ := hinter
  have hbounds := (sigma.slicing.toTStructure_heart_iff C E).mp hEheart
  have hpos : 0 < sigma.slicing.phiPlus C E hzero :=
    lt_of_lt_of_le (sigma.slicing.phiMinus_gt_of_gtProp C hzero hbounds.1)
      (sigma.slicing.phiMinus_le_phiPlus C E hzero)
  have hle : sigma.slicing.phiPlus C E hzero ≤ 1 :=
    sigma.slicing.phiPlus_le_of_leProp C hzero hbounds.2
  have hnpos : 0 < n := by exact_mod_cast (hncast ▸ hpos)
  have hnle : n ≤ 1 := by exact_mod_cast (hncast ▸ hle)
  have hn : n = 1 := by omega
  have hphi : sigma.slicing.phiPlus C E hzero = 1 := by simpa [hn] using hncast
  rw [← hphi]
  exact hPplus

/-- Rotation and HRS tilting do not change the zero-charge subcategory:
the zero-charge objects of the tilted heart are precisely the original-heart
objects of zero original charge. -/
theorem phaseTiltWeakStabilityFunction_zeroCharge_iff
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (E : C) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge E ↔
      sigma.zeroCharge E := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  constructor
  · rintro ⟨hEtilt, hcharge⟩
    have hZ : sigma.Z (v (K₀.of C E)) = 0 := by
      have hmul : sigma.Z (v (K₀.of C E)) *
          Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) = 0 := by
        simpa [W] using hcharge
      exact (mul_eq_zero.mp hmul).resolve_right (Complex.exp_ne_zero _)
    by_cases hzero : IsZero E
    · exact ⟨ObjectProperty.prop_of_iso sigma.slicing.toTStructure.heart
          hzero.isoZero.symm
          (mem_heart_of_bounds sigma.slicing
            (sigma.slicing.gtProp_zero C 0) (sigma.slicing.leProp_zero C 1)),
        hZ⟩
    obtain ⟨F, hn, hfirst, hlast⟩ :=
      HNFiltration.exists_both_nonzero C sigma.slicing hzero
    let P := F.toPostnikovTower
    let f : Fin F.n → ℂ := fun i =>
      sigma.Z (v (K₀.of C (P.factor i))) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I)
    have hbounds := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hEtilt
    have hphase : ∀ i : Fin F.n, F.φ i ∈ Set.Ioc beta (beta + 1) := by
      intro i
      constructor
      · calc
          beta < sigma.slicing.phiMinus C E hzero :=
            sigma.slicing.phiMinus_gt_of_gtProp C hzero hbounds.1
          _ = F.φ ⟨F.n - 1, by lia⟩ := by
            rw [sigma.slicing.phiMinus_eq C E hzero F hn hlast]
          _ ≤ F.φ i := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc
          F.φ i ≤ F.φ ⟨0, hn⟩ :=
            F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = sigma.slicing.phiPlus C E hzero := by
            rw [sigma.slicing.phiPlus_eq C E hzero F hn hfirst]
          _ ≤ beta + 1 :=
            sigma.slicing.phiPlus_le_of_leProp C hzero hbounds.2
    have hsum : ∑ i, f i = 0 := by
      have hdecomp :
          sigma.Z (v (K₀.of C E)) *
              Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) =
            ∑ i, f i := by
        rw [K₀.of_postnikovTower_eq_sum C P, map_sum, map_sum, Finset.sum_mul]
      rw [hZ, zero_mul] at hdecomp
      exact hdecomp.symm
    have hfclosed : ∀ i, WeakUpperClosed (f i) := by
      intro i
      by_cases hi : IsZero (P.factor i)
      · simpa [f, K₀.of_isZero C hi] using weakUpperClosed_zero
      obtain ⟨m, hm, -, hmZ⟩ :=
        sigma.compat' (F.φ i) (P.factor i) (F.semistable i) hi
      dsimp [f]
      rw [hmZ]
      exact rotatedRay_weakUpperClosed hm (hphase i)
    have hfactorZ : ∀ i, sigma.Z (v (K₀.of C (P.factor i))) = 0 := by
      intro i
      have hfi := weakUpperClosed_eq_zero_of_sum_eq_zero f hfclosed hsum i
      dsimp [f] at hfi
      exact (mul_eq_zero.mp hfi).resolve_right (Complex.exp_ne_zero _)
    have hphase_one_of_nonzero : ∀ i : Fin F.n, ¬IsZero (P.factor i) → F.φ i = 1 := by
      intro i hi
      obtain ⟨m, hm, hm_strict, hmZ⟩ :=
        sigma.compat' (F.φ i) (P.factor i) (F.semistable i) hi
      have hm0 : m = 0 := by
        rw [hfactorZ i, eq_comm, mul_eq_zero] at hmZ
        exact_mod_cast hmZ.resolve_right (Complex.exp_ne_zero _)
      have hinter : ∃ n : ℤ, F.φ i = (n : ℝ) := by
        by_contra h
        push Not at h
        have := hm_strict h
        linarith
      obtain ⟨n, hncast⟩ := hinter
      have hnpos : 0 < n := by
        exact_mod_cast lt_of_le_of_lt hbeta0 (hncast ▸ (hphase i).1)
      have hnlt : n < 2 := by
        have hnlt_real : (n : ℝ) < 2 := by
          rw [← hncast]
          linarith [(hphase i).2]
        exact_mod_cast hnlt_real
      have : n = 1 := by omega
      simpa [this] using hncast
    have hfirst_phase : F.φ ⟨0, hn⟩ = 1 :=
      hphase_one_of_nonzero ⟨0, hn⟩ hfirst
    have hlast_phase : F.φ ⟨F.n - 1, by lia⟩ = 1 :=
      hphase_one_of_nonzero ⟨F.n - 1, by lia⟩ hlast
    have hP : sigma.slicing.P 1 E := by
      have heq : sigma.slicing.phiPlus C E hzero =
          sigma.slicing.phiMinus C E hzero := by
        rw [sigma.slicing.phiPlus_eq C E hzero F hn hfirst,
          sigma.slicing.phiMinus_eq C E hzero F hn hlast,
          hfirst_phase, hlast_phase]
      have hPplus := sigma.slicing.semistable_of_phiPlus_eq_phiMinus C hzero heq
      rw [sigma.slicing.phiPlus_eq C E hzero F hn hfirst, hfirst_phase] at hPplus
      exact hPplus
    exact ⟨mem_heart_of_bounds sigma.slicing
        (sigma.slicing.gtProp_of_semistable C 1 0 E hP (by norm_num))
        (sigma.slicing.leProp_of_semistable C 1 1 E hP le_rfl), hZ⟩
  · rintro ⟨hEheart, hZ⟩
    have hP := sigma.zeroCharge_mem_P_one hEheart hZ
    have hgt : sigma.slicing.gtProp C beta E :=
      sigma.slicing.gtProp_of_semistable C 1 beta E hP hbeta1
    have hle : sigma.slicing.leProp C (beta + 1) E :=
      sigma.slicing.leProp_of_semistable C 1 (beta + 1) E hP (by linarith)
    have hshiftHeart :
        ((sigma.slicing.phaseShift C beta).toTStructure).heart E := by
      rw [(sigma.slicing.phaseShift C beta).toTStructure_heart_iff]
      exact ⟨(sigma.slicing.phaseShift_gtProp_zero C beta E).mpr hgt,
        (sigma.slicing.phaseShift_leProp C beta 1 E).mpr (by simpa [add_comm] using hle)⟩
    exact ⟨(sigma.phaseTiltHeart_iff_phaseShiftHeart hbeta0 hbeta1 E).mpr hshiftHeart,
      by simp [hZ]⟩

/-- The `moreover` mechanism in Lemma 14.17.  A map from an original
zero-charge object to a nonzero-charge tilted-semistable object vanishes
away from the boundary ray; strict stability gives the same conclusion on
the boundary. -/
theorem hom_eq_zero_of_zeroCharge_to_phaseTiltSemistable
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E A0 : C}
    (hE :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E ≠ 0)
    (hA0 : sigma.zeroCharge A0)
    (hrefine :
      0 < ((sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E).im ∨
        (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsStable E)
    (f : A0 ⟶ E) : f = 0 := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  let H := P.tilt.heart.FullSubcategory
  letI : Abelian H := P.tilt.heartFullSubcategoryAbelian
  have hA0tilt : P.tilt.heart A0 :=
    ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0 hbeta1 A0).mpr
      hA0).1
  let A0' : H := ⟨A0, hA0tilt⟩
  let E' : H := ⟨E, hE.1⟩
  let f' : A0' ⟶ E' := ObjectProperty.homMk f
  let I : H := Abelian.image f'
  let p : A0' ⟶ I := Abelian.factorThruImage f'
  let i : I ⟶ E' := Abelian.image.ι f'
  haveI : Epi p := by dsimp [p]; infer_instance
  haveI : Mono i := by dsimp [i]; infer_instance
  by_contra hf
  have hI0 : ¬IsZero I := by
    intro hIz
    apply hf
    have hf' : f' = 0 := by
      rw [← Abelian.image.fac f']
      change p ≫ i = 0
      rw [hIz.eq_of_tgt p 0, zero_comp]
    exact congrArg (fun k : A0' ⟶ E' => k.hom) hf'
  let K : H := kernel p
  let S0 : ShortComplex H := ShortComplex.mk (kernel.ι p) p (kernel.condition p)
  have hS0 : S0.ShortExact := ShortComplex.ShortExact.mk'
    (by simpa [S0, K] using ShortComplex.exact_kernel p)
    (by dsimp [S0]; infer_instance)
    (by dsimp [S0]; infer_instance)
  let T0 := P.triangleOfShortExact S0 hS0
  have hT0 : T0 ∈ distTriang C := P.triangleOfShortExact_distinguished S0 hS0
  have hIzero : W.zeroCharge I.obj := by
    apply W.zeroCharge_right K.property I.property
      ((sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0 hbeta1 A0).mpr
        hA0)
    exact hT0
  let Q : H := cokernel i
  let S : ShortComplex H := ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (by simpa [S, Q] using ShortComplex.exact_cokernel i)
    (by dsimp [S]; infer_instance)
    (by dsimp [S]; infer_instance)
  let T := P.triangleOfShortExact S hS
  have hT : T ∈ distTriang C := P.triangleOfShortExact_distinguished S hS
  have hsum : W.charge E = W.charge I.obj + W.charge Q.obj := by
    simpa [T, S, I, Q, E'] using W.charge_triangle' hT
  have hQcharge : W.charge Q.obj = W.charge E := by
    rw [hIzero.2, zero_add] at hsum
    exact hsum.symm
  have hQ0 : ¬IsZero Q.obj := fun hQz =>
    hcharge (by rw [← hQcharge]; exact W.charge_isZero hQz)
  have hIambient0 : ¬IsZero I.obj := fun h => hI0
    (ObjectProperty.FullSubcategory.isZero_of_obj_isZero h)
  have hslope := hE.2 I.property Q.property hIambient0 hQ0
    T.mor₁ T.mor₂ T.mor₃ hT
  rcases hrefine with him | hstable
  · have hQim : 0 < (W.charge Q.obj).im := by rwa [hQcharge]
    rw [W.slope_of_im_nonpos (by rw [hIzero.2]; simp),
      W.slope_of_im_pos hQim] at hslope
    exact WithTop.not_top_le_coe _ hslope
  · have hslope' := hstable.2 I.property Q.property hIambient0 hQ0
      T.mor₁ T.mor₂ T.mor₃ hT
    rw [W.slope_of_im_nonpos (by rw [hIzero.2]; simp)] at hslope'
    exact (not_lt_of_ge le_top) hslope'

/-- A semistable object's subobject with zero-charge quotient is itself
semistable.  The proof forms the composite subobject in the abelian tilted
heart and compares its cokernel charge with the original quotient charge. -/
theorem phaseTilt_isSemistable_left_of_zeroCharge_right
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {A E V : C}
    (hA : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart A)
    (hV : ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart V)
    (hE :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E)
    (hVzero :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).zeroCharge V)
    {f : A ⟶ E} {g : E ⟶ V} {d : V ⟶ A⟦(1 : ℤ)⟧}
    (hdist : Triangle.mk f g d ∈ distTriang C) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable A := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  let H := P.tilt.heart.FullSubcategory
  letI : Abelian H := P.tilt.heartFullSubcategoryAbelian
  refine ⟨hA, ?_⟩
  intro X Y hX hY hX0 hY0 a b e hXY
  let X' : H := ⟨X, hX⟩
  let Y' : H := ⟨Y, hY⟩
  let A' : H := ⟨A, hA⟩
  let E' : H := ⟨E, hE.1⟩
  let V' : H := ⟨V, hV⟩
  let a' : X' ⟶ A' := ObjectProperty.homMk a
  let f' : A' ⟶ E' := ObjectProperty.homMk f
  let Sinner : ShortComplex H := ShortComplex.mk a'
    (ObjectProperty.homMk b : A' ⟶ Y') (by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hXY)
  let Souter : ShortComplex H := ShortComplex.mk f'
    (ObjectProperty.homMk g : E' ⟶ V') (by
      ext
      exact comp_distTriang_mor_zero₁₂ _ hdist)
  have hSinner : Sinner.ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt hXY
  have hSouter : Souter.ShortExact :=
    TStructure.heartFullSubcategory_shortExact_of_distTriang
      (C := C) P.tilt hdist
  letI : Mono a' := hSinner.mono_f
  letI : Mono f' := hSouter.mono_f
  let c : X' ⟶ E' := a' ≫ f'
  let Q : H := cokernel c
  let S : ShortComplex H := ShortComplex.mk c (cokernel.π c) (cokernel.condition c)
  have hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (by simpa [S, Q] using ShortComplex.exact_cokernel c)
    (by dsimp [S, c]; infer_instance)
    (by dsimp [S]; infer_instance)
  let T := P.triangleOfShortExact S hS
  have hT : T ∈ distTriang C := P.triangleOfShortExact_distinguished S hS
  have hQ0 : ¬IsZero Q.obj := by
    intro hQ
    have hQ' : IsZero Q := ObjectProperty.FullSubcategory.isZero_of_obj_isZero hQ
    haveI : Epi c := Preadditive.epi_of_isZero_cokernel c hQ'
    haveI : Epi f' := epi_of_epi a' f'
    haveI : IsIso f' := isIso_of_mono_of_epi f'
    haveI : IsIso c := isIso_of_mono_of_epi c
    haveI : IsIso a' := IsIso.of_isIso_comp_right a' f'
    have ha' : IsIso a'.hom := by
      change IsIso (P.tilt.heart.ι.map a')
      infer_instance
    haveI : IsIso a := by simpa [a'] using ha'
    have haTriangle : IsIso (Triangle.mk a b e).mor₁ := by
      change IsIso a
      infer_instance
    exact hY0 ((Triangle.isZero₃_iff_isIso₁ (Triangle.mk a b e) hXY).2 haTriangle)
  have hsumOuter : W.charge E = W.charge A + W.charge V := W.charge_triangle' hdist
  have hsumInner : W.charge A = W.charge X + W.charge Y := W.charge_triangle' hXY
  have hsumComp : W.charge E = W.charge X + W.charge Q.obj := by
    simpa [T, S, Q, E', X'] using W.charge_triangle' hT
  have hQcharge : W.charge Q.obj = W.charge Y := by
    apply add_left_cancel (a := W.charge X)
    calc
      W.charge X + W.charge Q.obj = W.charge E := hsumComp.symm
      _ = W.charge A := by rw [hsumOuter, hVzero.2, add_zero]
      _ = W.charge X + W.charge Y := hsumInner
  have hslope := hE.2 hX Q.property hX0 hQ0 T.mor₁ T.mor₂ T.mor₃ hT
  have hslopeQ : W.slope Q.obj = W.slope Y := by
    unfold WeakStabilityFunction.slope
    rw [hQcharge]
  rwa [hslopeQ] at hslope

/-- A charged torsion-class object which is semistable after the phase tilt
was already semistable in the original heart. -/
theorem weakStabilityFunctionOnHeart_isSemistable_of_phaseTors_phaseTiltSemistable
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) {E : C}
    (hEtors : phaseTors sigma.slicing beta E)
    (hEss :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).IsSemistable E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).charge E ≠ 0) :
    sigma.weakStabilityFunctionOnHeart.IsSemistable E := by
  let P := slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le
  let W0 := sigma.weakStabilityFunctionOnHeart
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1
  have hheart : sigma.slicing.toTStructure.heart E :=
    mem_heart_of_bounds sigma.slicing
      (sigma.slicing.gtProp_anti C hbeta0.le E hEtors.1) hEtors.2
  have hE0 : ¬IsZero E := fun hzero => hcharge (W.charge_isZero hzero)
  have him : 0 < (W.charge E).im := by
    have := phaseTiltCharge_im_pos_of_phaseTors sigma hbeta0 hEtors (by
      change phaseTiltRotation beta (W0.charge E) ≠ 0
      simpa [W, W0] using hcharge)
    simpa [W, W0] using this
  have hHom : ∀ A0 : C, sigma.zeroCharge A0 → ∀ f : A0 ⟶ E, f = 0 := by
    intro A0 hA0 f
    exact sigma.hom_eq_zero_of_zeroCharge_to_phaseTiltSemistable beta hbeta0.le hbeta1
      hEss hcharge hA0 (Or.inl him) f
  apply (sigma.weakStabilityFunctionOnHeart_isSemistable_iff E hheart hE0).mpr
  apply sigma.slicing.semistable_of_phiPlus_eq_phiMinus C hE0
  apply le_antisymm
  · by_contra hnot
    have hgap : sigma.slicing.phiMinus C E hE0 < sigma.slicing.phiPlus C E hE0 :=
      lt_of_not_ge hnot
    let cut :=
      (sigma.slicing.phiMinus C E hE0 + sigma.slicing.phiPlus C E hE0) / 2
    have hminus_cut : sigma.slicing.phiMinus C E hE0 < cut := by
      dsimp [cut]
      linarith
    have hcut_plus : cut < sigma.slicing.phiPlus C E hE0 := by
      dsimp [cut]
      linarith
    have hbeta_cut : beta < cut :=
      (sigma.slicing.phiMinus_gt_of_gtProp C hE0 hEtors.1).trans hminus_cut
    have hplus_one : sigma.slicing.phiPlus C E hE0 ≤ 1 :=
      sigma.slicing.phiPlus_le_of_leProp C hE0 hEtors.2
    have hcut_one : cut < 1 := hcut_plus.trans_le hplus_one
    obtain ⟨F, hn, hfirst, hlast⟩ :=
      HNFiltration.exists_both_nonzero C sigma.slicing hE0
    have hphase : ∀ j : Fin F.n, beta < F.φ j ∧ F.φ j < 2 := by
      intro j
      constructor
      · calc
          beta < sigma.slicing.phiMinus C E hE0 :=
            sigma.slicing.phiMinus_gt_of_gtProp C hE0 hEtors.1
          _ = F.φ ⟨F.n - 1, by lia⟩ := by
            rw [sigma.slicing.phiMinus_eq C E hE0 F hn hlast]
          _ ≤ F.φ j := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc
          F.φ j ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = sigma.slicing.phiPlus C E hE0 := by
            rw [sigma.slicing.phiPlus_eq C E hE0 F hn hfirst]
          _ ≤ 1 := hplus_one
          _ < 2 := by norm_num
    obtain ⟨X, Y, f, g, d, hdist, hXgt, hYle, -⟩ :=
      sigma.slicing.exists_split_at_cutoff C F hphase hn (t := cut)
    have hXle : sigma.slicing.leProp C 1 X := by
      have hYshift : sigma.slicing.leProp C 1 (Y⟦(-1 : ℤ)⟧) := by
        have hs := sigma.slicing.leProp_shift C cut Y (-1) hYle
        exact sigma.slicing.leProp_mono C (by push_cast; linarith) _ hs
      exact sigma.slicing.leProp_of_triangle C 1 hYshift hEtors.2
        (inv_rot_of_distTriang _ hdist)
    have hYgt : sigma.slicing.gtProp C beta Y := by
      have hXshift : sigma.slicing.gtProp C beta (X⟦(1 : ℤ)⟧) := by
        have hs := sigma.slicing.gtProp_shift C cut X 1 hXgt
        exact sigma.slicing.gtProp_anti C (by push_cast; linarith) _ hs
      exact sigma.slicing.gtProp_of_triangle C beta hEtors.1 hXshift
        (rot_of_distTriang _ hdist)
    have hXtors : phaseTors sigma.slicing beta X :=
      ⟨sigma.slicing.gtProp_anti C hbeta_cut.le X hXgt, hXle⟩
    have hYtors : phaseTors sigma.slicing beta Y :=
      ⟨hYgt, sigma.slicing.leProp_mono C hcut_one.le Y hYle⟩
    have hX0 : ¬IsZero X := by
      intro hzero
      haveI : IsIso g :=
        (Triangle.isZero₁_iff_isIso₂ (Triangle.mk f g d) hdist).mp hzero
      have hEle : sigma.slicing.leProp C cut E :=
        ObjectProperty.prop_of_iso (sigma.slicing.leProp C cut) (asIso g).symm hYle
      linarith [sigma.slicing.phiPlus_le_of_leProp C hE0 hEle]
    have hY0 : ¬IsZero Y := by
      intro hzero
      haveI : IsIso f :=
        (Triangle.isZero₃_iff_isIso₁ (Triangle.mk f g d) hdist).mp hzero
      have hEgt : sigma.slicing.gtProp C cut E :=
        ObjectProperty.prop_of_iso (sigma.slicing.gtProp C cut) (asIso f) hXgt
      linarith [sigma.slicing.phiMinus_gt_of_gtProp C hE0 hEgt]
    have hXheart : sigma.slicing.toTStructure.heart X :=
      mem_heart_of_bounds sigma.slicing
        (sigma.slicing.gtProp_anti C hbeta0.le X hXtors.1) hXtors.2
    have hYheart : sigma.slicing.toTStructure.heart Y :=
      mem_heart_of_bounds sigma.slicing
        (sigma.slicing.gtProp_anti C hbeta0.le Y hYtors.1) hYtors.2
    have hXtilt : P.tilt.heart X := P.tors_mem_tilt_heart hXtors
    have hYtilt : P.tilt.heart Y := P.tors_mem_tilt_heart hYtors
    have hXcharge : W0.charge X ≠ 0 := by
      intro hXZ
      have hfzero := hHom X ⟨hXheart, hXZ⟩ f
      let X' : P.tilt.heart.FullSubcategory := ⟨X, hXtilt⟩
      let E' : P.tilt.heart.FullSubcategory := ⟨E, hEss.1⟩
      let Y' : P.tilt.heart.FullSubcategory := ⟨Y, hYtilt⟩
      let f' : X' ⟶ E' := ObjectProperty.homMk f
      let g' : E' ⟶ Y' := ObjectProperty.homMk g
      have hshort := TStructure.heartFullSubcategory_shortExact_of_distTriang
        (C := C) P.tilt (A := X') (B := E') (Q := Y')
          (f := f') (g := g') (δ := d) hdist
      letI : Mono f' := hshort.mono_f
      have hfzero' : f' = 0 := by ext; exact hfzero
      have hXzero' : IsZero X' := IsZero.of_mono_eq_zero f' hfzero'
      exact hX0 (P.tilt.heart.ι.map_isZero hXzero')
    have hYplus : sigma.slicing.phiPlus C Y hY0 ≤ cut :=
      sigma.slicing.phiPlus_le_of_leProp C hY0 hYle
    have hXminus : cut < sigma.slicing.phiMinus C X hX0 :=
      sigma.slicing.phiMinus_gt_of_gtProp C hX0 hXgt
    have hslopeYX : W.slope Y < W.slope X :=
      phaseTilt_slope_lt_of_phase_separated sigma W hYheart hXheart hYtilt hXtilt
        (by rfl) (by rfl) hY0 hX0 (hYplus.trans_lt hXminus)
        (hYplus.trans_lt hcut_one) hXcharge
    have hslopeXY : W.slope X ≤ W.slope Y :=
      hEss.2 hXtilt hYtilt hX0 hY0 f g d hdist
    exact (not_lt_of_ge hslopeXY) hslopeYX
  · exact sigma.slicing.phiMinus_le_phiPlus C E hE0

/-- If the shift of a charged torsion-free object is semistable in the
tilted heart, the unshifted object is semistable in the original heart. -/
theorem weakStabilityFunctionOnHeart_isSemistable_of_phaseFree_shiftSemistable
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {U : C}
    (hUfree : phaseFree sigma.slicing beta U)
    (hUss :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable
        (U⟦(1 : ℤ)⟧))
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge
        (U⟦(1 : ℤ)⟧) ≠ 0) :
    sigma.weakStabilityFunctionOnHeart.IsSemistable U := by
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  let W0 := sigma.weakStabilityFunctionOnHeart
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  have hheart : sigma.slicing.toTStructure.heart U :=
    mem_heart_of_bounds sigma.slicing hUfree.1
      (sigma.slicing.leProp_mono C hbeta1.le U hUfree.2)
  have hU0 : ¬IsZero U := by
    intro hzero
    apply hcharge
    exact W.charge_isZero ((shiftFunctor C (1 : ℤ)).map_isZero hzero)
  apply (sigma.weakStabilityFunctionOnHeart_isSemistable_iff U hheart hU0).mpr
  apply sigma.slicing.semistable_of_phiPlus_eq_phiMinus C hU0
  apply le_antisymm
  · by_contra hnot
    have hgap : sigma.slicing.phiMinus C U hU0 < sigma.slicing.phiPlus C U hU0 :=
      lt_of_not_ge hnot
    let cut :=
      (sigma.slicing.phiMinus C U hU0 + sigma.slicing.phiPlus C U hU0) / 2
    have hminus_cut : sigma.slicing.phiMinus C U hU0 < cut := by
      dsimp [cut]
      linarith
    have hcut_plus : cut < sigma.slicing.phiPlus C U hU0 := by
      dsimp [cut]
      linarith
    have hzero_cut : 0 < cut :=
      (sigma.slicing.phiMinus_gt_of_gtProp C hU0 hUfree.1).trans hminus_cut
    have hplus_beta : sigma.slicing.phiPlus C U hU0 ≤ beta :=
      sigma.slicing.phiPlus_le_of_leProp C hU0 hUfree.2
    have hcut_beta : cut < beta := hcut_plus.trans_le hplus_beta
    have hcut_one : cut < 1 := hcut_beta.trans hbeta1
    obtain ⟨F, hn, hfirst, hlast⟩ :=
      HNFiltration.exists_both_nonzero C sigma.slicing hU0
    have hphase : ∀ j : Fin F.n, (0 : ℝ) < F.φ j ∧ F.φ j < 2 := by
      intro j
      constructor
      · calc
          0 < sigma.slicing.phiMinus C U hU0 :=
            sigma.slicing.phiMinus_gt_of_gtProp C hU0 hUfree.1
          _ = F.φ ⟨F.n - 1, by lia⟩ := by
            rw [sigma.slicing.phiMinus_eq C U hU0 F hn hlast]
          _ ≤ F.φ j := F.hφ.antitone (Fin.mk_le_mk.mpr (by lia))
      · calc
          F.φ j ≤ F.φ ⟨0, hn⟩ := F.hφ.antitone (Fin.mk_le_mk.mpr (Nat.zero_le _))
          _ = sigma.slicing.phiPlus C U hU0 := by
            rw [sigma.slicing.phiPlus_eq C U hU0 F hn hfirst]
          _ ≤ beta := hplus_beta
          _ < 1 := hbeta1
          _ < 2 := by norm_num
    obtain ⟨X, Y, f, g, d, hdist, hXgt, hYle, -⟩ :=
      sigma.slicing.exists_split_at_cutoff C F hphase hn (t := cut)
    have hXle : sigma.slicing.leProp C beta X := by
      have hYshift : sigma.slicing.leProp C beta (Y⟦(-1 : ℤ)⟧) := by
        have hs := sigma.slicing.leProp_shift C cut Y (-1) hYle
        exact sigma.slicing.leProp_mono C (by push_cast; linarith) _ hs
      exact sigma.slicing.leProp_of_triangle C beta hYshift hUfree.2
        (inv_rot_of_distTriang _ hdist)
    have hYgt : sigma.slicing.gtProp C 0 Y := by
      have hXshift : sigma.slicing.gtProp C 0 (X⟦(1 : ℤ)⟧) := by
        have hs := sigma.slicing.gtProp_shift C cut X 1 hXgt
        exact sigma.slicing.gtProp_anti C (by push_cast; linarith) _ hs
      exact sigma.slicing.gtProp_of_triangle C 0 hUfree.1 hXshift
        (rot_of_distTriang _ hdist)
    have hXfree : phaseFree sigma.slicing beta X :=
      ⟨sigma.slicing.gtProp_anti C hzero_cut.le X hXgt, hXle⟩
    have hYfree : phaseFree sigma.slicing beta Y :=
      ⟨hYgt, sigma.slicing.leProp_mono C hcut_beta.le Y hYle⟩
    have hX0 : ¬IsZero X := by
      intro hzero
      haveI : IsIso g :=
        (Triangle.isZero₁_iff_isIso₂ (Triangle.mk f g d) hdist).mp hzero
      have hUle : sigma.slicing.leProp C cut U :=
        ObjectProperty.prop_of_iso (sigma.slicing.leProp C cut) (asIso g).symm hYle
      linarith [sigma.slicing.phiPlus_le_of_leProp C hU0 hUle]
    have hY0 : ¬IsZero Y := by
      intro hzero
      haveI : IsIso f :=
        (Triangle.isZero₃_iff_isIso₁ (Triangle.mk f g d) hdist).mp hzero
      have hUgt : sigma.slicing.gtProp C cut U :=
        ObjectProperty.prop_of_iso (sigma.slicing.gtProp C cut) (asIso f) hXgt
      linarith [sigma.slicing.phiMinus_gt_of_gtProp C hU0 hUgt]
    have hXheart : sigma.slicing.toTStructure.heart X :=
      mem_heart_of_bounds sigma.slicing hXfree.1
        (sigma.slicing.leProp_mono C hbeta1.le X hXfree.2)
    have hYheart : sigma.slicing.toTStructure.heart Y :=
      mem_heart_of_bounds sigma.slicing hYfree.1
        (sigma.slicing.leProp_mono C hbeta1.le Y hYfree.2)
    have hXtilt : P.tilt.heart (X⟦(1 : ℤ)⟧) := P.free_shift_mem_tilt_heart hXfree
    have hYtilt : P.tilt.heart (Y⟦(1 : ℤ)⟧) := P.free_shift_mem_tilt_heart hYfree
    have hXplus : sigma.slicing.phiPlus C X hX0 ≤ beta :=
      sigma.slicing.phiPlus_le_of_leProp C hX0 hXfree.2
    obtain ⟨hXupper, -⟩ := sigma.charge_mem_upperHalfPlane_and_arg_le_phiPlus
      X hXheart hX0 (hXplus.trans_lt hbeta1)
    have hXcharge : W0.charge X ≠ 0 := upperHalfPlaneUnion_ne_zero hXupper
    have hYplus : sigma.slicing.phiPlus C Y hY0 ≤ cut :=
      sigma.slicing.phiPlus_le_of_leProp C hY0 hYle
    have hXminus : cut < sigma.slicing.phiMinus C X hX0 :=
      sigma.slicing.phiMinus_gt_of_gtProp C hX0 hXgt
    have hWX : W.charge (X⟦(1 : ℤ)⟧) = phaseTiltRotation beta (-(W0.charge X)) := by
      simp [W, W0, WeakStabilityFunction.charge, phaseTiltRotation, K₀.of_shift_one]
    have hWY : W.charge (Y⟦(1 : ℤ)⟧) = phaseTiltRotation beta (-(W0.charge Y)) := by
      simp [W, W0, WeakStabilityFunction.charge, phaseTiltRotation, K₀.of_shift_one]
    have hslopeYX : W.slope (Y⟦(1 : ℤ)⟧) < W.slope (X⟦(1 : ℤ)⟧) :=
      phaseTilt_slope_shift_lt_shift_of_phase_separated sigma W hYheart hXheart
        hYtilt hXtilt hWY hWX hY0 hX0 (hYplus.trans_lt hXminus)
        (hYplus.trans_lt hcut_one) hXcharge
    let Tshift := (shiftFunctor (Triangle C) (1 : ℤ)).obj (Triangle.mk f g d)
    have hTshift : Tshift ∈ distTriang C := Triangle.shift_distinguished _ hdist 1
    have hslopeXY : W.slope (X⟦(1 : ℤ)⟧) ≤ W.slope (Y⟦(1 : ℤ)⟧) :=
      hUss.2 hXtilt hYtilt
        (fun h => hX0 (by
          rw [IsZero.iff_id_eq_zero] at h ⊢
          exact (Functor.map_eq_zero_iff (shiftFunctor C (1 : ℤ))).mp (by simpa using h)))
        (fun h => hY0 (by
          rw [IsZero.iff_id_eq_zero] at h ⊢
          exact (Functor.map_eq_zero_iff (shiftFunctor C (1 : ℤ))).mp (by simpa using h)))
        Tshift.mor₁ Tshift.mor₂ Tshift.mor₃ hTshift
    exact (not_lt_of_ge hslopeXY) hslopeYX
  · exact sigma.slicing.phiMinus_le_phiPlus C U hU0

/-- A ray criterion for semistability in the tilted heart.  The object has a
single nonzero-charge phase `theta`; the Hom condition excludes zero-charge
subobjects when that ray lies in the open upper half-plane. -/
theorem phaseTiltWeakStabilityFunction_isSemistable_of_ray
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1)
    {E : C} (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    {theta m : ℝ} (htheta : theta ∈ Set.Ioc (0 : ℝ) 1) (hm : 0 < m)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E =
        (m : ℂ) *
          Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I))
    (hle : sigma.slicing.leProp C (beta + theta) E)
    (hHom : 0 <
        ((sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E).im →
      ∀ A0 : C, sigma.zeroCharge A0 → ∀ f : A0 ⟶ E, f = 0) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  let P := slicingTorsionPair sigma.slicing hbeta0 hbeta1.le
  refine ⟨hEtilt, ?_⟩
  intro A B hAtilt hBtilt hA0 hB0 f g d hdist
  have hAint := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hAtilt
  have hBint := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hBtilt
  have hBshift : sigma.slicing.leProp C beta (B⟦(-1 : ℤ)⟧) := by
    have hshift := sigma.slicing.leProp_shift C (beta + 1) B (-1) hBint.2
    convert hshift using 1
    all_goals push_cast
    all_goals ring
  have hAle : sigma.slicing.leProp C (beta + theta) A :=
    sigma.slicing.leProp_of_triangle C (beta + theta)
      (sigma.slicing.leProp_mono C (by linarith [htheta.1]) _ hBshift) hle
      (inv_rot_of_distTriang _ hdist)
  have hsum : W.charge E = W.charge A + W.charge B :=
    W.charge_triangle' hdist
  by_cases htheta_one : theta = 1
  · have hEim : (W.charge E).im = 0 := by
      rw [hcharge, htheta_one, Complex.exp_ofReal_mul_I]
      simp
    have hAim_nonneg : 0 ≤ (W.charge A).im := by
      rcases W.upper A hAtilt hA0 with him | ⟨him, -⟩
      · exact him.le
      · exact him.ge
    have hBim_nonneg : 0 ≤ (W.charge B).im := by
      rcases W.upper B hBtilt hB0 with him | ⟨him, -⟩
      · exact him.le
      · exact him.ge
    have him_sum : (W.charge A).im + (W.charge B).im = 0 := by
      have := congrArg Complex.im hsum
      simpa [hEim] using this.symm
    have hAim : (W.charge A).im = 0 := by linarith
    have hBim : (W.charge B).im = 0 := by linarith
    rw [W.slope_of_im_nonpos (by rw [hAim]; exact lt_irrefl 0),
      W.slope_of_im_nonpos (by rw [hBim]; exact lt_irrefl 0)]
  · have htheta_lt : theta < 1 := lt_of_le_of_ne htheta.2 htheta_one
    have hEim : 0 < (W.charge E).im := by
      rw [hcharge, Complex.exp_ofReal_mul_I]
      simp only [Complex.mul_im, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_im, zero_mul, mul_one, add_zero,
        zero_add]
      exact mul_pos hm (Real.sin_pos_of_pos_of_lt_pi
        (mul_pos Real.pi_pos htheta.1)
        (by nlinarith [mul_lt_mul_of_pos_left htheta_lt Real.pi_pos]))
    have hAcross : 0 ≤ cross (W.charge A) (W.charge E) := by
      have hcross := rotatedCharge_cross_ray_nonneg_of_bounds sigma hm.le htheta.2
        hAint.1 hAle
      rw [← hcharge] at hcross
      exact hcross
    have hAcharge : W.charge A ≠ 0 := by
      intro hAzero
      have hsigmaZero : sigma.zeroCharge A :=
        (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0 hbeta1 A).mp
          ⟨hAtilt, hAzero⟩
      have hfzero : f = 0 := hHom hEim A hsigmaZero f
      let A' : P.tilt.heart.FullSubcategory := ⟨A, hAtilt⟩
      let E' : P.tilt.heart.FullSubcategory := ⟨E, hEtilt⟩
      let B' : P.tilt.heart.FullSubcategory := ⟨B, hBtilt⟩
      let f' : A' ⟶ E' := ObjectProperty.homMk f
      let g' : E' ⟶ B' := ObjectProperty.homMk g
      have hshort := TStructure.heartFullSubcategory_shortExact_of_distTriang
        (C := C) P.tilt (A := A') (B := E') (Q := B')
          (f := f') (g := g') (δ := d) hdist
      letI : Mono f' := hshort.mono_f
      have hfzero' : f' = 0 := by ext; exact hfzero
      have hAzero' : IsZero A' := IsZero.of_mono_eq_zero f' hfzero'
      exact hA0 ((P.tilt).heart.ι.map_isZero hAzero')
    have hAim : 0 < (W.charge A).im := by
      rcases W.upper A hAtilt hA0 with him | ⟨him, hre⟩
      · exact him
      · exfalso
        have hre0 : (W.charge A).re = 0 := by
          unfold cross at hAcross
          rw [him] at hAcross
          simp only [zero_mul, sub_zero] at hAcross
          nlinarith
        apply hAcharge
        exact Complex.ext hre0 him
    by_cases hBim : 0 < (W.charge B).im
    · have hcrossAB : 0 ≤ cross (W.charge A) (W.charge B) := by
        have heq : cross (W.charge A) (W.charge B) =
            cross (W.charge A) (W.charge E) := by
          rw [hsum]
          simp [cross]
          ring
        rw [heq]
        exact hAcross
      rw [W.slope_of_im_pos hAim, W.slope_of_im_pos hBim]
      exact_mod_cast (div_le_div_iff₀ hAim hBim).2 (by
        unfold cross at hcrossAB
        nlinarith)
    · rw [W.slope_of_im_nonpos hBim]
      exact le_top

/-! ## The two classes in Lemma 14.17 -/

/-- The first class in the phase-language form of Lemma 14.17: an original
heart semistable object with no maps from original zero-charge objects. -/
def IsPhaseTiltTypeOne
    (sigma : WeakPreStabilityCondition v) (E : C) : Prop :=
  sigma.weakStabilityFunctionOnHeart.IsSemistable E ∧
    ∀ A0 : C, sigma.zeroCharge A0 → ∀ f : A0 ⟶ E, f = 0

/-- The second class in the phase-language form of Lemma 14.17: an extension
of a zero-charge object by the shift of a semistable torsion-free object.
The final implication is the positive-imaginary part of the lemma's
`moreover` clause; it is exactly what excludes zero-charge subobjects away
from the boundary ray. -/
def IsPhaseTiltTypeTwo
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) (E : C) : Prop :=
  ∃ (U V : C), phaseFree sigma.slicing beta U ∧
    sigma.weakStabilityFunctionOnHeart.IsSemistable U ∧
    sigma.zeroCharge V ∧
    ∃ (f : U⟦(1 : ℤ)⟧ ⟶ E) (g : E ⟶ V)
      (d : V ⟶ U⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧),
      Triangle.mk f g d ∈ distTriang C ∧
        (0 <
            ((sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E).im →
          ∀ V0 : C, sigma.zeroCharge V0 → ∀ a : V0 ⟶ E, a = 0)

/-- Objects of the first class are semistable for the phase-tilted weak
stability function. -/
theorem isSemistable_of_isPhaseTiltTypeOne
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E : C}
    (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E ≠ 0)
    (hE : sigma.IsPhaseTiltTypeOne E) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  have hEnz : ¬IsZero E := fun hzero =>
    hcharge ((W.charge_isZero hzero))
  have hheart := hE.1.1
  have hP :=
    (sigma.weakStabilityFunctionOnHeart_isSemistable_iff E hheart hEnz).mp hE.1
  let phi := sigma.slicing.phiPlus C E hEnz
  have hphi_eq := sigma.slicing.phiPlus_eq_phiMinus_of_semistable C hP hEnz
  have hinterval := sigma.phaseTiltHeart_interval hbeta0 hbeta1 hEtilt
  have hphi_beta : beta < phi := by
    dsimp [phi]
    rw [← hphi_eq.2]
    exact sigma.slicing.phiMinus_gt_of_gtProp C hEnz hinterval.1
  have hphi_one : phi ≤ 1 := by
    exact sigma.slicing.phiPlus_le_of_leProp C hEnz
      ((sigma.slicing.toTStructure_heart_iff C E).mp hheart).2
  obtain ⟨m, hm, -, hmZ⟩ := sigma.compat' phi E hP hEnz
  have hZne : sigma.Z (v (K₀.of C E)) ≠ 0 := by
    intro hZ
    apply hcharge
    simp [hZ]
  have hmpos : 0 < m := by
    apply lt_of_le_of_ne hm
    intro hm0
    apply hZne
    rw [hmZ]
    simp [hm0]
  let theta := phi - beta
  have htheta : theta ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · dsimp [theta]; linarith
    · dsimp [theta]; linarith
  have hrot : W.charge E =
      (m : ℂ) *
        Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I) := by
    rw [show W.charge E = sigma.Z (v (K₀.of C E)) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) from rfl, hmZ,
      mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp [theta]
    push_cast
    ring
  have hle : sigma.slicing.leProp C (beta + theta) E := by
    have : sigma.slicing.leProp C phi E :=
      sigma.slicing.leProp_of_semistable C phi phi E hP le_rfl
    convert this using 1
    all_goals dsimp [theta]
    all_goals ring
  exact sigma.phaseTiltWeakStabilityFunction_isSemistable_of_ray beta hbeta0 hbeta1
    hEtilt htheta hmpos hrot hle (fun _ => hE.2)

/-- Objects of the second class are semistable for the phase-tilted weak
stability function. -/
theorem isSemistable_of_isPhaseTiltTypeTwo
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E : C}
    (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E ≠ 0)
    (hE : sigma.IsPhaseTiltTypeTwo beta hbeta0 hbeta1 E) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E := by
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1
  obtain ⟨U, V, hUfree, hUss, hVzero, f, g, d, hdist, hHom⟩ := hE
  have hVtiltZero : W.zeroCharge V :=
    (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0 hbeta1 V).mpr
      hVzero
  have hsum : W.charge E = W.charge (U⟦(1 : ℤ)⟧) + W.charge V :=
    W.charge_triangle' hdist
  have hUshiftCharge : W.charge (U⟦(1 : ℤ)⟧) = W.charge E := by
    rw [hsum, hVtiltZero.2, add_zero]
  have hUne : ¬IsZero U := by
    intro hzero
    apply hcharge
    rw [← hUshiftCharge]
    exact W.charge_isZero ((shiftFunctor C (1 : ℤ)).map_isZero hzero)
  have hUheart := hUss.1
  have hUP :=
    (sigma.weakStabilityFunctionOnHeart_isSemistable_iff U hUheart hUne).mp hUss
  let phi := sigma.slicing.phiPlus C U hUne
  have hphi_eq := sigma.slicing.phiPlus_eq_phiMinus_of_semistable C hUP hUne
  have hphi_pos : 0 < phi := by
    dsimp [phi]
    rw [← hphi_eq.2]
    exact sigma.slicing.phiMinus_gt_of_gtProp C hUne hUfree.1
  have hphi_beta : phi ≤ beta := by
    exact sigma.slicing.phiPlus_le_of_leProp C hUne hUfree.2
  obtain ⟨m, hm, -, hmZ⟩ := sigma.compat' phi U hUP hUne
  have hZU_ne : sigma.Z (v (K₀.of C U)) ≠ 0 := by
    intro hZU
    apply hcharge
    rw [← hUshiftCharge]
    simp [W, WeakStabilityFunction.charge, K₀.of_shift_one, hZU]
  have hmpos : 0 < m := by
    apply lt_of_le_of_ne hm
    intro hm0
    apply hZU_ne
    rw [hmZ]
    simp [hm0]
  let theta := phi + 1 - beta
  have htheta : theta ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · dsimp [theta]; linarith
    · dsimp [theta]; linarith
  have hrot : W.charge E =
      (m : ℂ) *
        Complex.exp (((Real.pi * theta : ℝ) : ℂ) * Complex.I) := by
    rw [← hUshiftCharge]
    change sigma.Z (v (K₀.of C (U⟦(1 : ℤ)⟧))) *
        Complex.exp (-(Real.pi * beta : ℂ) * Complex.I) = _
    rw [K₀.of_shift_one, map_neg, map_neg, hmZ]
    rw [show -((m : ℂ) * Complex.exp (((Real.pi * phi : ℝ) : ℂ) * Complex.I)) =
        (m : ℂ) *
          Complex.exp (((Real.pi * (phi + 1) : ℝ) : ℂ) * Complex.I) by
      rw [show Real.pi * (phi + 1) = Real.pi * phi + Real.pi by ring,
        ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
      ring]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp [theta]
    push_cast
    ring
  have hUshiftLe : sigma.slicing.leProp C (phi + 1) (U⟦(1 : ℤ)⟧) := by
    simpa only [Int.cast_one] using
      sigma.slicing.leProp_shift C phi U 1
        (sigma.slicing.leProp_of_semistable C phi phi U hUP le_rfl)
  have hVP := sigma.zeroCharge_mem_P_one hVzero.1 hVzero.2
  have hVle : sigma.slicing.leProp C (phi + 1) V :=
    sigma.slicing.leProp_of_semistable C 1 (phi + 1) V hVP (by linarith)
  have hle : sigma.slicing.leProp C (beta + theta) E := by
    have := sigma.slicing.leProp_of_triangle C (phi + 1) hUshiftLe hVle hdist
    convert this using 1
    all_goals dsimp [theta]
    all_goals ring
  exact sigma.phaseTiltWeakStabilityFunction_isSemistable_of_ray beta hbeta0 hbeta1
    hEtilt htheta hmpos hrot hle hHom

/-- The reverse direction of the phase-language form of Lemma 14.17.  The
canonical original-cohomology sequence splits a tilted-semistable object
into `H⁻¹(E)[1]` and `H⁰(E)`; strict phase separation forces one of those
two terms to have zero charge. -/
theorem phaseTiltClassification_of_isSemistable
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) {E : C}
    (hE :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).IsSemistable E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).charge E ≠ 0) :
    sigma.IsPhaseTiltTypeOne E ∨
      sigma.IsPhaseTiltTypeTwo beta hbeta0.le hbeta1 E := by
  let t := sigma.slicing.toTStructure
  let P := slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le
  let W0 := sigma.weakStabilityFunctionOnHeart
  let W := sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1
  let U : C := (P.originalHMinusOne hE.1).obj
  let V : C := (P.originalHZero hE.1).obj
  let T := originalCohomologyTriangle t E
  have hT : T ∈ distTriang C := originalCohomologyTriangle_distinguished t E
  have hUfree : phaseFree sigma.slicing beta U := P.originalHMinusOne_free hE.1
  have hVtors : phaseTors sigma.slicing beta V := P.originalHZero_tors hE.1
  have hUheart : sigma.slicing.toTStructure.heart U :=
    mem_heart_of_bounds sigma.slicing hUfree.1
      (sigma.slicing.leProp_mono C hbeta1.le U hUfree.2)
  have hVheart : sigma.slicing.toTStructure.heart V :=
    mem_heart_of_bounds sigma.slicing
      (sigma.slicing.gtProp_anti C hbeta0.le V hVtors.1) hVtors.2
  have hUshiftTilt : P.tilt.heart (U⟦(1 : ℤ)⟧) :=
    P.free_shift_mem_tilt_heart hUfree
  have hVtilt : P.tilt.heart V := P.tors_mem_tilt_heart hVtors
  by_cases hUcharge : W.charge (U⟦(1 : ℤ)⟧) = 0
  · have hUshiftZeroCharge : W.zeroCharge (U⟦(1 : ℤ)⟧) :=
      ⟨hUshiftTilt, hUcharge⟩
    have hUshiftOriginalZero :=
      (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0.le hbeta1
        (U⟦(1 : ℤ)⟧)).mp hUshiftZeroCharge
    have hUshiftGt : sigma.slicing.gtProp C 1 (U⟦(1 : ℤ)⟧) := by
      simpa only [Int.cast_one, zero_add] using
        sigma.slicing.gtProp_shift C 0 U 1 hUfree.1
    have hUshiftLe : sigma.slicing.leProp C 1 (U⟦(1 : ℤ)⟧) :=
      ((sigma.slicing.toTStructure_heart_iff C (U⟦(1 : ℤ)⟧)).mp
        hUshiftOriginalZero.1).2
    have hUshiftZero : IsZero (U⟦(1 : ℤ)⟧) := by
      rw [IsZero.iff_id_eq_zero]
      exact sigma.slicing.zero_of_gtProp_leProp_general C 1 hUshiftGt hUshiftLe (𝟙 _)
    haveI : IsIso T.mor₂ :=
      (Triangle.isZero₁_iff_isIso₂ T hT).mp (by
        simpa [T, t, U, P, originalCohomologyTriangle,
          HeartTorsionPair.originalHMinusOne] using hUshiftZero)
    let eEV : E ≅ V := by
      simpa [T, t, V, P, originalCohomologyTriangle,
        HeartTorsionPair.originalHZero] using (asIso T.mor₂)
    have hEtors : phaseTors sigma.slicing beta E := by
      exact ⟨gtProp_of_iso sigma.slicing eEV.symm hVtors.1,
        leProp_of_iso sigma.slicing eEV.symm hVtors.2⟩
    have hEold :=
      sigma.weakStabilityFunctionOnHeart_isSemistable_of_phaseTors_phaseTiltSemistable
        beta hbeta0 hbeta1 hEtors hE hcharge
    have him : 0 < (W.charge E).im := by
      have him' := phaseTiltCharge_im_pos_of_phaseTors sigma hbeta0 hEtors (by
        change phaseTiltRotation beta (W0.charge E) ≠ 0
        simpa [W, W0] using hcharge)
      simpa [W, W0] using him'
    refine Or.inl ⟨hEold, ?_⟩
    intro A0 hA0 f
    exact sigma.hom_eq_zero_of_zeroCharge_to_phaseTiltSemistable beta hbeta0.le hbeta1
      hE hcharge hA0 (Or.inl him) f
  · have hVcharge : W.charge V = 0 := by
      by_contra hVcharge
      have hU0 : ¬IsZero U := by
        intro hzero
        apply hUcharge
        exact W.charge_isZero ((shiftFunctor C (1 : ℤ)).map_isZero hzero)
      have hV0 : ¬IsZero V := fun hzero => hVcharge (W.charge_isZero hzero)
      have hVoldCharge : W0.charge V ≠ 0 := by
        intro hz
        apply hVcharge
        change phaseTiltRotation beta (W0.charge V) = 0
        rw [hz]
        exact map_zero (phaseTiltRotation beta)
      have hUplus : sigma.slicing.phiPlus C U hU0 ≤ beta :=
        sigma.slicing.phiPlus_le_of_leProp C hU0 hUfree.2
      have hVminus : beta < sigma.slicing.phiMinus C V hV0 :=
        sigma.slicing.phiMinus_gt_of_gtProp C hV0 hVtors.1
      have hWU : W.charge (U⟦(1 : ℤ)⟧) =
          phaseTiltRotation beta (-(W0.charge U)) := by
        simp [W, W0, WeakStabilityFunction.charge, phaseTiltRotation, K₀.of_shift_one]
      have hWV : W.charge V = phaseTiltRotation beta (W0.charge V) := by rfl
      have hslopeVU : W.slope V < W.slope (U⟦(1 : ℤ)⟧) :=
        phaseTilt_slope_unshifted_lt_shifted_of_phase_separated sigma W
          hUheart hVheart hUshiftTilt hVtilt hWU hWV hU0 hV0
          (hUplus.trans_lt hVminus) (hUplus.trans_lt hbeta1) hVoldCharge
      have hslopeUV : W.slope (U⟦(1 : ℤ)⟧) ≤ W.slope V := by
        simpa [T, t, U, V, P] using
          hE.2 hUshiftTilt hVtilt
            (fun hzero => hUcharge (W.charge_isZero hzero)) hV0
            T.mor₁ T.mor₂ T.mor₃ hT
      exact (not_lt_of_ge hslopeUV) hslopeVU
    have hVzeroTilt : W.zeroCharge V := ⟨hVtilt, hVcharge⟩
    have hVzero : sigma.zeroCharge V :=
      (sigma.phaseTiltWeakStabilityFunction_zeroCharge_iff beta hbeta0.le hbeta1 V).mp
        hVzeroTilt
    have hUshiftSemistable : W.IsSemistable (U⟦(1 : ℤ)⟧) := by
      apply sigma.phaseTilt_isSemistable_left_of_zeroCharge_right beta hbeta0.le hbeta1
        hUshiftTilt hVtilt hE hVzeroTilt
      simpa [T, t, U, V, P, originalCohomologyTriangle,
        HeartTorsionPair.originalHMinusOne,
        HeartTorsionPair.originalHZero] using hT
    have hUold : W0.IsSemistable U :=
      sigma.weakStabilityFunctionOnHeart_isSemistable_of_phaseFree_shiftSemistable
        beta hbeta0.le hbeta1 hUfree hUshiftSemistable hUcharge
    refine Or.inr ⟨U, V, hUfree, hUold, hVzero, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [T, t, U, P, originalCohomologyTriangle,
        HeartTorsionPair.originalHMinusOne] using T.mor₁
    · simpa [T, t, V, P, originalCohomologyTriangle,
        HeartTorsionPair.originalHZero] using T.mor₂
    · simpa [T, t, U, V, P, originalCohomologyTriangle,
        HeartTorsionPair.originalHMinusOne,
        HeartTorsionPair.originalHZero] using T.mor₃
    · simpa [T, t, U, V, P, originalCohomologyTriangle,
        HeartTorsionPair.originalHMinusOne,
        HeartTorsionPair.originalHZero] using hT
    · intro him V0 hV0 a
      exact sigma.hom_eq_zero_of_zeroCharge_to_phaseTiltSemistable beta hbeta0.le hbeta1
        hE hcharge hV0 (Or.inl him) a

/-- The constructive direction of the phase-language classification: either
class described in Lemma 14.17 gives a semistable object in the tilted
heart. -/
theorem isSemistable_of_phaseTiltClassification
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 ≤ beta) (hbeta1 : beta < 1) {E : C}
    (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0 hbeta1.le).tilt).heart E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).charge E ≠ 0)
    (hE : sigma.IsPhaseTiltTypeOne E ∨
      sigma.IsPhaseTiltTypeTwo beta hbeta0 hbeta1 E) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0 hbeta1).IsSemistable E := by
  rcases hE with hE | hE
  · exact sigma.isSemistable_of_isPhaseTiltTypeOne beta hbeta0 hbeta1
      hEtilt hcharge hE
  · exact sigma.isSemistable_of_isPhaseTiltTypeTwo beta hbeta0 hbeta1
      hEtilt hcharge hE

/-- Full phase-language classification of nonzero-charge semistable objects
after tilting, combining both directions of Lemma 14.17.  The strict lower
bound on `beta` records that a finite slope cutoff corresponds to a phase
cut strictly inside `(0, 1)`. -/
theorem phaseTiltWeakStabilityFunction_isSemistable_iff_classification
    (sigma : WeakPreStabilityCondition v) (beta : ℝ)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) {E : C}
    (hEtilt :
      ((slicingTorsionPair sigma.slicing hbeta0.le hbeta1.le).tilt).heart E)
    (hcharge :
      (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).charge E ≠ 0) :
    (sigma.phaseTiltWeakStabilityFunction beta hbeta0.le hbeta1).IsSemistable E ↔
      sigma.IsPhaseTiltTypeOne E ∨
        sigma.IsPhaseTiltTypeTwo beta hbeta0.le hbeta1 E := by
  constructor
  · intro hE
    exact sigma.phaseTiltClassification_of_isSemistable beta hbeta0 hbeta1 hE hcharge
  · intro hE
    exact sigma.isSemistable_of_phaseTiltClassification beta hbeta0.le hbeta1
      hEtilt hcharge hE

end WeakPreStabilityCondition

end BridgelandStabLean.WeakStability
