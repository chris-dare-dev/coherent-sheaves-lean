/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.Shift

/-!
# Trivializing a twist on a degree-one Proj chart

If `f` is homogeneous of degree one, multiplication by `f ^ d` trivializes the natural shift
`A(d)` after localizing away from `f`.  This file constructs that statement at the exact
degree-zero-localization level used by the associated-sheaf construction.

The sign convention is DerivedAlgGeo's convention `A(d)ₙ = Aₙ₊d`: a fraction in the shifted
degree-zero localization has ordinary graded degree `d`.  Multiplying it by `f⁻ᵈ` produces a
degree-zero fraction, and multiplication by `fᵈ` is the inverse operation.
-/

noncomputable section

open DirectSum SetLike
open scoped Pointwise

namespace AlgebraicGeometry.Proj

universe u

variable {A σ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace DegreeZeroLocalization

variable {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)

private def twistPower : Submonoid.powers f := ⟨f ^ d, ⟨d, rfl⟩⟩

private def twistInverse : Localization (.powers f) :=
  Localization.mk 1 (twistPower d)

private def twistForward : Localization (.powers f) :=
  Localization.mk (f ^ d) 1

/-- Divide an `A(d)` fraction by `f ^ d`, obtaining an ordinary degree-zero fraction. -/
noncomputable def natShiftToSelfLinearMap :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) (.powers f) →ₗ[
      HomogeneousLocalization 𝒜 (.powers f)]
        DegreeZeroLocalization 𝒜 𝒜 (.powers f) where
  toFun z := by
    refine ⟨twistInverse (f := f) d • (z : LocalizedModule (.powers f) A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + d
        num := c.num
        den := ⟨(c.den : A) * f ^ d, ?_⟩
        den_mem := (Submonoid.powers f).mul_mem c.den_mem ⟨d, rfl⟩ }, ?_⟩
    · simpa using SetLike.mul_mem_graded c.den.2 (SetLike.pow_mem_graded d hf)
    · rw [← hc]
      change LocalizedModule.mk (c.num : A)
        (⟨(c.den : A) * f ^ d, ?_⟩ : Submonoid.powers f) =
          Localization.mk 1 (twistPower (f := f) d) •
            LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
      rw [LocalizedModule.mk_smul_mk]
      simp only [one_smul]
      congr 1
      ext
      exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (twistInverse (f := f) d) (x : LocalizedModule (.powers f) A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (twistInverse (f := f) d) a (z : LocalizedModule (.powers f) A)

/-- Multiply an ordinary degree-zero fraction by `f ^ d`, obtaining a fraction in `A(d)`. -/
noncomputable def selfToNatShiftLinearMap :
    DegreeZeroLocalization 𝒜 𝒜 (.powers f) →ₗ[
      HomogeneousLocalization 𝒜 (.powers f)]
        DegreeZeroLocalization 𝒜 (natShift 𝒜 d) (.powers f) where
  toFun z := by
    refine ⟨twistForward (f := f) d • (z : LocalizedModule (.powers f) A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg
        num := ⟨(c.num : A) * f ^ d, ?_⟩
        den := c.den
        den_mem := c.den_mem }, ?_⟩
    · simpa using SetLike.mul_mem_graded c.num.2 (SetLike.pow_mem_graded d hf)
    · rw [← hc]
      change LocalizedModule.mk ((c.num : A) * f ^ d)
        (⟨c.den, c.den_mem⟩ : Submonoid.powers f) =
          Localization.mk (f ^ d) 1 •
            LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
      rw [LocalizedModule.mk_smul_mk]
      simp only [one_mul]
      congr 1
      exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (twistForward (f := f) d) (x : LocalizedModule (.powers f) A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (twistForward (f := f) d) a (z : LocalizedModule (.powers f) A)

private theorem twistInverse_mul_forward :
    twistInverse (f := f) d * twistForward (f := f) d = 1 := by
  unfold twistInverse twistForward
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_mul_mk'_eq_one
    (S := Localization (Submonoid.powers f)) (1 : Submonoid.powers f)
      (twistPower (f := f) d)

private theorem twistForward_mul_inverse :
    twistForward (f := f) d * twistInverse (f := f) d = 1 := by
  rw [mul_comm]
  exact twistInverse_mul_forward (f := f) d

/-- On a degree-one chart, the degree-zero localization of `A(d)` is canonically the chart ring
as a module over itself. -/
noncomputable def natShiftSelfLinearEquiv :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) (.powers f) ≃ₗ[
      HomogeneousLocalization 𝒜 (.powers f)]
        DegreeZeroLocalization 𝒜 𝒜 (.powers f) where
  toLinearMap := natShiftToSelfLinearMap 𝒜 hf d
  invFun := selfToNatShiftLinearMap 𝒜 hf d
  left_inv z := by
    apply ext
    change twistForward (f := f) d • (twistInverse (f := f) d •
      (z : LocalizedModule (.powers f) A)) = z
    rw [← mul_smul, twistForward_mul_inverse (f := f) d, one_smul]
  right_inv z := by
    apply ext
    change twistInverse (f := f) d • (twistForward (f := f) d •
      (z : LocalizedModule (.powers f) A)) = z
    rw [← mul_smul, twistInverse_mul_forward (f := f) d, one_smul]

@[simp]
theorem natShiftSelfLinearEquiv_apply_mk
    (c : NumDenSameDeg 𝒜 (natShift 𝒜 d) (.powers f)) :
    natShiftSelfLinearEquiv 𝒜 hf d (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg + d
          num := c.num
          den := ⟨(c.den : A) * f ^ d, by
            simpa using SetLike.mul_mem_graded c.den.2 (SetLike.pow_mem_graded d hf)⟩
          den_mem := (Submonoid.powers f).mul_mem c.den_mem ⟨d, rfl⟩ } := by
  apply ext
  change Localization.mk 1 (twistPower (f := f) d) •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk (c.num : A)
      ⟨(c.den : A) * f ^ d, (Submonoid.powers f).mul_mem c.den_mem ⟨d, rfl⟩⟩
  rw [LocalizedModule.mk_smul_mk]
  simp only [one_smul]
  congr 1
  ext
  exact mul_comm _ _

@[simp]
theorem natShiftSelfLinearEquiv_symm_apply_mk
    (c : NumDenSameDeg 𝒜 𝒜 (.powers f)) :
    (natShiftSelfLinearEquiv 𝒜 hf d).symm (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg
          num := ⟨(c.num : A) * f ^ d, by
            simpa using SetLike.mul_mem_graded c.num.2 (SetLike.pow_mem_graded d hf)⟩
          den := c.den
          den_mem := c.den_mem } := by
  apply ext
  change Localization.mk (f ^ d) 1 •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk ((c.num : A) * f ^ d) ⟨(c.den : A), c.den_mem⟩
  rw [LocalizedModule.mk_smul_mk]
  simp only [one_mul]
  congr 1
  exact mul_comm _ _

/-- The chart trivialization with Mathlib's homogeneous-localization ring as target. -/
noncomputable def natShiftAwayLinearEquiv :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) (.powers f) ≃ₗ[
      HomogeneousLocalization 𝒜 (.powers f)]
        HomogeneousLocalization 𝒜 (.powers f) :=
  (natShiftSelfLinearEquiv 𝒜 hf d).trans
    (selfLinearEquiv 𝒜 (.powers f)).symm

/-! ## Trivialization in any localization containing the degree-one element -/

variable {S : Submonoid A}

private def twistPowerOfMem (hfS : f ∈ S) : S :=
  ⟨f ^ d, S.pow_mem hfS d⟩

private def twistInverseOfMem (hfS : f ∈ S) : Localization S :=
  Localization.mk 1 (twistPowerOfMem (f := f) d hfS)

private def twistForwardOfMem : Localization S :=
  Localization.mk (f ^ d) 1

/-- Divide an `A(d)` fraction by `f ^ d`, given that `f` itself lies in `S`.

Membership is genuinely the hypothesis consumed, not merely invertibility of `f` in
`Localization S`: the graded representative below keeps every denominator inside `S` by
multiplying `c.den` by `f ^ d`, which needs `f ^ d ∈ S`.  When `f` is only invertible — the
Čech-intersection case, where the denominator submonoid contains no degree-one element at
all — use `natShiftLinearEquivOfMulMem`, which asks instead for a homogeneous cofactor `h`
with `f * h ∈ S`; taking `h = 1` recovers the membership hypothesis. -/
noncomputable def natShiftToSelfLinearMapOfMem (hfS : f ∈ S) :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) S →ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 𝒜 S where
  toFun z := by
    refine ⟨twistInverseOfMem (f := f) d hfS • (z : LocalizedModule S A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + d
        num := c.num
        den := ⟨(c.den : A) * f ^ d, ?_⟩
        den_mem := S.mul_mem c.den_mem (S.pow_mem hfS d) }, ?_⟩
    · simpa using SetLike.mul_mem_graded c.den.2 (SetLike.pow_mem_graded d hf)
    · rw [← hc]
      change LocalizedModule.mk (c.num : A)
        (⟨(c.den : A) * f ^ d, _⟩ : S) =
          Localization.mk 1 (twistPowerOfMem (f := f) d hfS) •
            LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
      rw [LocalizedModule.mk_smul_mk]
      simp only [one_smul]
      congr 1
      ext
      exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (twistInverseOfMem (f := f) d hfS)
      (x : LocalizedModule S A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (twistInverseOfMem (f := f) d hfS) a
      (z : LocalizedModule S A)

/-- Multiply an ordinary degree-zero fraction by `f ^ d` in any localization containing `f`. -/
noncomputable def selfToNatShiftLinearMapOfMem :
    DegreeZeroLocalization 𝒜 𝒜 S →ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 (natShift 𝒜 d) S where
  toFun z := by
    refine ⟨twistForwardOfMem (S := S) (f := f) d • (z : LocalizedModule S A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg
        num := ⟨(c.num : A) * f ^ d, ?_⟩
        den := c.den
        den_mem := c.den_mem }, ?_⟩
    · simpa using SetLike.mul_mem_graded c.num.2 (SetLike.pow_mem_graded d hf)
    · rw [← hc]
      change LocalizedModule.mk ((c.num : A) * f ^ d)
        (⟨c.den, c.den_mem⟩ : S) =
          Localization.mk (f ^ d) 1 •
            LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
      rw [LocalizedModule.mk_smul_mk]
      simp only [one_mul]
      congr 1
      exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (twistForwardOfMem (S := S) (f := f) d)
      (x : LocalizedModule S A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (twistForwardOfMem (S := S) (f := f) d) a
      (z : LocalizedModule S A)

private theorem twistInverseOfMem_mul_forward (hfS : f ∈ S) :
    twistInverseOfMem (f := f) d hfS * twistForwardOfMem (S := S) (f := f) d = 1 := by
  unfold twistInverseOfMem twistForwardOfMem
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_mul_mk'_eq_one
    (S := Localization S) (1 : S) (twistPowerOfMem (f := f) d hfS)

/-! ## Trivializing when `f` is only invertible, not a member

`natShiftToSelfLinearMapOfMem` asks for `f ∈ S`, but its own statement only needs `f` to be
invertible in `Localization S`.  The gap is not academic: on a Čech intersection the denominator
submonoid is `.powers (∏ₐ gₐ)`, which for more than one factor contains no degree-one element at
all, while every `gₐ` is invertible there.

The hypothesis below records invertibility in the form the graded bookkeeping can use: a
homogeneous cofactor `h` with `f * h ∈ S`.  Division by `f ^ d` is then performed as
multiplication by `h ^ d / (f * h) ^ d`, which is the same element of the localization but keeps
every denominator literally inside `S`.  Taking `h = 1` recovers the membership hypothesis.
-/

private def twistPowerOfMulMem {h : A} (hfh : f * h ∈ S) : S :=
  ⟨(f * h) ^ d, S.pow_mem hfh d⟩

private def twistInverseOfMulMem {h : A} (hfh : f * h ∈ S) : Localization S :=
  Localization.mk (h ^ d) (twistPowerOfMulMem (f := f) d hfh)

/-- Divide an `A(d)` fraction by `f ^ d` whenever a homogeneous cofactor carries `f` into the
denominator submonoid. -/
noncomputable def natShiftToSelfLinearMapOfMulMem {h : A} {e : ℕ} (h_deg : h ∈ 𝒜 e)
    (hfh : f * h ∈ S) :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) S →ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 𝒜 S where
  toFun z := by
    refine ⟨twistInverseOfMulMem (f := f) d hfh • (z : LocalizedModule S A), ?_⟩
    obtain ⟨c, hc⟩ := z.property
    refine ⟨
      { deg := c.deg + d * (1 + e)
        num := ⟨(c.num : A) * h ^ d, ?_⟩
        den := ⟨(c.den : A) * (f * h) ^ d, ?_⟩
        den_mem := S.mul_mem c.den_mem (S.pow_mem hfh d) }, ?_⟩
    · have hnum : (c.num : A) ∈ 𝒜 (c.deg + d) := c.num.2
      simpa [Nat.mul_add, Nat.mul_comm, ← add_assoc] using
        SetLike.mul_mem_graded hnum (SetLike.pow_mem_graded d h_deg)
    · simpa using SetLike.mul_mem_graded c.den.2
        (SetLike.pow_mem_graded d (SetLike.mul_mem_graded hf h_deg))
    · rw [← hc]
      change LocalizedModule.mk ((c.num : A) * h ^ d)
        (⟨(c.den : A) * (f * h) ^ d, _⟩ : S) =
          Localization.mk (h ^ d) (twistPowerOfMulMem (f := f) d hfh) •
            LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩
      rw [LocalizedModule.mk_smul_mk]
      congr 1
      · exact mul_comm _ _
      · ext
        exact mul_comm _ _
  map_add' x y := by
    apply ext
    simp only [coe_add]
    exact smul_add (twistInverseOfMulMem (f := f) d hfh)
      (x : LocalizedModule S A) y
  map_smul' a z := by
    apply ext
    simp only [coe_smul]
    exact smul_comm (twistInverseOfMulMem (f := f) d hfh) a
      (z : LocalizedModule S A)

private theorem twistInverseOfMulMem_mul_forward {h : A} (hfh : f * h ∈ S) :
    twistInverseOfMulMem (f := f) d hfh * twistForwardOfMem (S := S) (f := f) d = 1 := by
  unfold twistInverseOfMulMem twistForwardOfMem twistPowerOfMulMem
  rw [Localization.mk_mul]
  have hnum : h ^ d * f ^ d = ((f * h) ^ d : A) := by
    rw [mul_pow]; exact mul_comm _ _
  rw [hnum]
  simp

/-- Multiplication and division by `f ^ d` are inverse whenever a homogeneous cofactor carries
`f` into the denominator submonoid.  This is the form the Čech intersections need: there `f` is
one variable and the cofactor is the product of the others. -/
noncomputable def natShiftLinearEquivOfMulMem {h : A} {e : ℕ} (h_deg : h ∈ 𝒜 e)
    (hfh : f * h ∈ S) :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) S ≃ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 𝒜 S where
  toLinearMap := natShiftToSelfLinearMapOfMulMem 𝒜 hf d h_deg hfh
  invFun := selfToNatShiftLinearMapOfMem (S := S) 𝒜 hf d
  left_inv z := by
    apply ext
    change twistForwardOfMem (S := S) (f := f) d •
      (twistInverseOfMulMem (f := f) d hfh • (z : LocalizedModule S A)) = z
    rw [← mul_smul, mul_comm, twistInverseOfMulMem_mul_forward (f := f) d hfh, one_smul]
  right_inv z := by
    apply ext
    change twistInverseOfMulMem (f := f) d hfh •
      (twistForwardOfMem (S := S) (f := f) d • (z : LocalizedModule S A)) = z
    rw [← mul_smul, twistInverseOfMulMem_mul_forward (f := f) d hfh, one_smul]

/-- Multiplication and division by `f ^ d` give inverse degree-zero localization maps whenever
`f` belongs to the denominator submonoid. -/
noncomputable def natShiftLinearEquivOfMem (hfS : f ∈ S) :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) S ≃ₗ[
      HomogeneousLocalization 𝒜 S] DegreeZeroLocalization 𝒜 𝒜 S where
  toLinearMap := natShiftToSelfLinearMapOfMem 𝒜 hf d hfS
  invFun := selfToNatShiftLinearMapOfMem (S := S) 𝒜 hf d
  left_inv z := by
    apply ext
    change twistForwardOfMem (S := S) (f := f) d •
      (twistInverseOfMem (f := f) d hfS • (z : LocalizedModule S A)) = z
    rw [← mul_smul, mul_comm, twistInverseOfMem_mul_forward (f := f) d hfS, one_smul]
  right_inv z := by
    apply ext
    change twistInverseOfMem (f := f) d hfS •
      (twistForwardOfMem (S := S) (f := f) d • (z : LocalizedModule S A)) = z
    rw [← mul_smul, twistInverseOfMem_mul_forward (f := f) d hfS, one_smul]

@[simp]
theorem natShiftLinearEquivOfMem_apply_mk (hfS : f ∈ S)
    (c : NumDenSameDeg 𝒜 (natShift 𝒜 d) S) :
    natShiftLinearEquivOfMem 𝒜 hf d hfS (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg + d
          num := c.num
          den := ⟨(c.den : A) * f ^ d, by
            simpa using SetLike.mul_mem_graded c.den.2 (SetLike.pow_mem_graded d hf)⟩
          den_mem := S.mul_mem c.den_mem (S.pow_mem hfS d) } := by
  apply ext
  change Localization.mk 1 (twistPowerOfMem (f := f) d hfS) •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk (c.num : A)
      ⟨(c.den : A) * f ^ d, S.mul_mem c.den_mem (S.pow_mem hfS d)⟩
  rw [LocalizedModule.mk_smul_mk]
  simp only [one_smul]
  congr 1
  ext
  exact mul_comm _ _

@[simp]
theorem natShiftLinearEquivOfMem_symm_apply_mk (hfS : f ∈ S)
    (c : NumDenSameDeg 𝒜 𝒜 S) :
    (natShiftLinearEquivOfMem 𝒜 hf d hfS).symm (DegreeZeroLocalization.mk c) =
      DegreeZeroLocalization.mk
        { deg := c.deg
          num := ⟨(c.num : A) * f ^ d, by
            simpa using SetLike.mul_mem_graded c.num.2 (SetLike.pow_mem_graded d hf)⟩
          den := c.den
          den_mem := c.den_mem } := by
  apply ext
  change Localization.mk (f ^ d) 1 •
      LocalizedModule.mk (c.num : A) ⟨(c.den : A), c.den_mem⟩ =
    LocalizedModule.mk ((c.num : A) * f ^ d) ⟨(c.den : A), c.den_mem⟩
  rw [LocalizedModule.mk_smul_mk]
  simp only [one_mul]
  congr 1
  exact mul_comm _ _

end DegreeZeroLocalization

end AlgebraicGeometry.Proj
