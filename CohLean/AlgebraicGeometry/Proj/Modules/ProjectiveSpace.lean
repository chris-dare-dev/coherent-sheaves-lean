/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import CohLean.AlgebraicGeometry.Proj.Modules.Finiteness
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Sections of nonnegative twists on polynomial projective space

This file constructs the comparison between degree-`d` homogeneous polynomials and global
sections of `O(d)` on polynomial `Proj`.  The proof uses the variable basic-open cover, the
constructed chart comparison from `TwistChart`, and the generic point of the polynomial ring.

The comparison is stated over a field and for a nonempty finite variable type, which is the
projective-space range consumed by the Serre-finiteness argument.  These hypotheses make the
generic-point and denominator-cancellation steps explicit.
-/

noncomputable section

open CategoryTheory DirectSum Opposite SetLike TopCat TopologicalSpace
open scoped DirectSum Pointwise

namespace CohLean.AlgebraicGeometry.Proj

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Global sections of the natural shift associated to `A(d)` on polynomial `Proj`. -/
abbrev polynomialNatGlobalSections (ι k : Type u) [Field k] (d : ℕ) :=
  (associatedSheafInType (polynomialGrading ι k)
    (natShift (polynomialGrading ι k) d)).1.obj
      (op (⊤ : (AlgebraicGeometry.Proj (polynomialGrading ι k)).Opens))

/-- A homogeneous polynomial of degree `d` defines the global section represented everywhere
by the fraction `p / 1` in the shifted module. -/
noncomputable def polynomialToNatGlobalSections (ι k : Type u) [Field k] (d : ℕ) :
    MvPolynomial.homogeneousSubmodule ι k d →+
      polynomialNatGlobalSections ι k d where
  toFun p := by
    let num : ↥(CohLean.AlgebraicGeometry.Proj.natShift
        (polynomialGrading ι k) d 0) :=
      ⟨p.1, by change p.1 ∈ polynomialGrading ι k (0 + d); simpa using p.2⟩
    let den : polynomialGrading ι k 0 :=
      ⟨1, one_mem_graded (polynomialGrading ι k)⟩
    refine ⟨fun x => DegreeZeroLocalization.mk
      { deg := 0
        num := num
        den := den
        den_mem := Ideal.IsPrime.one_notMem inferInstance }, ?_⟩
    intro x
    exact ⟨⊤, x.2, 𝟙 _, 0, num, den,
      fun _ => Ideal.IsPrime.one_notMem inferInstance, fun _ => rfl⟩
  map_zero' := by
    apply section_ext
    funext x
    apply DegreeZeroLocalization.ext
    change LocalizedModule.mk (0 : MvPolynomial ι k) _ = 0
    simp
  map_add' p q := by
    apply section_ext
    funext x
    apply DegreeZeroLocalization.ext
    change LocalizedModule.mk ((p + q :
      MvPolynomial.homogeneousSubmodule ι k d) : MvPolynomial ι k) _ =
        LocalizedModule.mk (p : MvPolynomial ι k) _ +
          LocalizedModule.mk (q : MvPolynomial ι k) _
    rw [LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
    exact ⟨1, by simp⟩

/-- The zero homogeneous ideal is the generic point of polynomial projective space. -/
def polynomialGenericPoint (ι k : Type u) [Field k] [Nonempty ι] :
    ProjectiveSpectrum (polynomialGrading ι k) where
  asHomogeneousIdeal := ⊥
  isPrime := by
    change (⊥ : Ideal (MvPolynomial ι k)).IsPrime
    exact Ideal.isPrime_bot
  not_irrelevant_le h := by
    let i : ι := Classical.choice inferInstance
    have hX : MvPolynomial.X i ∈
        HomogeneousIdeal.irrelevant (polynomialGrading ι k) :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one
        (MvPolynomial.isHomogeneous_X k i)
    have h0 : (MvPolynomial.X i : MvPolynomial ι k) ∈ (⊥ : Ideal _) := h hX
    rw [Ideal.mem_bot] at h0
    exact (MvPolynomial.X_ne_zero i) h0

/-- Restriction of a global natural-twist section to the variable chart `D₊(Xᵢ)`. -/
noncomputable def restrictNatGlobalSectionsToVariable
    (ι k : Type u) [Field k] (d : ℕ) (i : ι) :
    polynomialNatGlobalSections ι k d →+
      (associatedSheafInType (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d)).1.obj
          (op (ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
            (MvPolynomial.X i))) where
  toFun s := ((associatedSheafInType (polynomialGrading ι k)
    (natShift (polynomialGrading ι k) d)).presheaf.map
      (homOfLE le_top).op).hom s
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The homogeneous fraction representing a global section on the variable chart `D₊(Xᵢ)`. -/
noncomputable def variableFractionOfGlobalSection
    (ι k : Type u) [Field k] (d : ℕ) (i : ι) :
    polynomialNatGlobalSections ι k d →+
      DegreeZeroLocalization (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d) (.powers (MvPolynomial.X i)) :=
  (natShiftBasicOpenSectionAddEquiv (polynomialGrading ι k)
    (MvPolynomial.isHomogeneous_X k i) d).symm.toAddMonoidHom.comp
      (restrictNatGlobalSectionsToVariable ι k d i)

theorem moduleAwayToSection_variableFractionOfGlobalSection
    (ι k : Type u) [Field k] (d : ℕ) (i : ι)
    (s : polynomialNatGlobalSections ι k d) :
    moduleAwayToSection (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d) (MvPolynomial.X i)
        (variableFractionOfGlobalSection ι k d i s) =
      restrictNatGlobalSectionsToVariable ι k d i s := by
  rw [← natShiftBasicOpenSectionAddEquiv_toAddMonoidHom
    (polynomialGrading ι k) (MvPolynomial.isHomogeneous_X k i) d]
  exact (natShiftBasicOpenSectionAddEquiv (polynomialGrading ι k)
    (MvPolynomial.isHomogeneous_X k i) d).apply_symm_apply _

/-- The denominator submonoid at the polynomial generic point. -/
abbrev polynomialGenericDenominators (ι k : Type u) [Field k] [Nonempty ι] :
    Submonoid (MvPolynomial ι k) :=
  (polynomialGenericPoint ι k).asHomogeneousIdeal.toIdeal.primeCompl

/-- Every variable is invertible at the polynomial generic point. -/
theorem powers_X_le_polynomialGenericDenominators
    (ι k : Type u) [Field k] [Nonempty ι] (i : ι) :
    Submonoid.powers (MvPolynomial.X i) ≤ polynomialGenericDenominators ι k := by
  apply Submonoid.powers_le.mpr
  change (MvPolynomial.X i : MvPolynomial ι k) ∉ (⊥ : Ideal _)
  simpa only [Ideal.mem_bot] using MvPolynomial.X_ne_zero (R := k) i

/-- A variable-chart fraction viewed in the common generic localization. -/
noncomputable def variableFractionToGeneric
    (ι k : Type u) [Field k] [Nonempty ι] (d : ℕ) (i : ι) :
    DegreeZeroLocalization (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d) (.powers (MvPolynomial.X i)) →+
      DegreeZeroLocalization (polynomialGrading ι k)
        (natShift (polynomialGrading ι k) d)
          (polynomialGenericDenominators ι k) :=
  DegreeZeroLocalization.mapOfLE
    (powers_X_le_polynomialGenericDenominators ι k i)

/-- All variable-chart representatives of a global section have the same generic value. -/
theorem variableFractionToGeneric_apply_globalSection
    (ι k : Type u) [Field k] [Nonempty ι] (d : ℕ) (i : ι)
    (s : polynomialNatGlobalSections ι k d) :
    variableFractionToGeneric ι k d i
        (variableFractionOfGlobalSection ι k d i s) =
      s.1 ⟨polynomialGenericPoint ι k, Set.mem_univ _⟩ := by
  let x : ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
      (MvPolynomial.X i) :=
    ⟨polynomialGenericPoint ι k,
      powers_X_le_polynomialGenericDenominators ι k i
        ⟨1, by simp⟩⟩
  have h := congr_arg (fun t => t.1 x)
    (moduleAwayToSection_variableFractionOfGlobalSection ι k d i s)
  rw [moduleAwayToSection_apply] at h
  exact h

/-- Passing from a variable localization to the generic localization loses no information. -/
theorem variableFractionToGeneric_injective
    (ι k : Type u) [Field k] [Nonempty ι] (d : ℕ) (i : ι) :
    Function.Injective (variableFractionToGeneric ι k d i) := by
  intro z w hzw
  obtain ⟨c, rfl⟩ := DegreeZeroLocalization.mk_surjective z
  obtain ⟨e, rfl⟩ := DegreeZeroLocalization.mk_surjective w
  simp only [variableFractionToGeneric, DegreeZeroLocalization.mapOfLE_mk] at hzw
  rw [DegreeZeroLocalization.mk_eq_mk_iff] at hzw
  obtain ⟨u, hu⟩ := hzw
  have hu0 : (u : MvPolynomial ι k) ≠ 0 := by
    have hu' := u.2
    change (u : MvPolynomial ι k) ∉ (⊥ : Ideal _) at hu'
    intro h0
    exact hu' (by simpa only [Ideal.mem_bot] using h0)
  have hcancel : (e.den : MvPolynomial ι k) * (c.num : MvPolynomial ι k) =
      (c.den : MvPolynomial ι k) * (e.num : MvPolynomial ι k) :=
    mul_left_cancel₀ hu0 (by simpa only [smul_eq_mul, mul_assoc] using hu)
  rw [DegreeZeroLocalization.mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  simpa [smul_eq_mul] using hcancel

/-- Dividing a homogeneous polynomial of degree `n + d` by `Xᵢⁿ`, when the division is exact,
produces a homogeneous polynomial of degree `d`. -/
theorem divMonomial_single_mem_homogeneousSubmodule
    (ι k : Type u) [Field k] (i : ι) (n d : ℕ) (p : MvPolynomial ι k)
    (hp : p ∈ MvPolynomial.homogeneousSubmodule ι k (n + d)) :
    p.divMonomial (Finsupp.single i n) ∈
      MvPolynomial.homogeneousSubmodule ι k d := by
  intro s hs
  have hcoeff : MvPolynomial.coeff (Finsupp.single i n + s) p ≠ 0 := by
    simpa only [MvPolynomial.coeff_divMonomial] using hs
  have hdeg := hp hcoeff
  simp only [map_add, Finsupp.weight_single, Pi.one_apply, nsmul_eq_mul, mul_one] at hdeg
  exact Nat.add_left_cancel hdeg

/-- Exact division by `Xᵢⁿ` reconstructs the original polynomial. -/
theorem X_pow_mul_divMonomial_single
    (ι k : Type u) [Field k] (i : ι) (n : ℕ) (p : MvPolynomial ι k)
    (hdiv : (MvPolynomial.X i : MvPolynomial ι k) ^ n ∣ p) :
    MvPolynomial.X i ^ n * p.divMonomial (Finsupp.single i n) = p := by
  rw [MvPolynomial.X_pow_eq_monomial]
  have hmod : p.modMonomial (Finsupp.single i n) = 0 :=
    MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero.mp
      (by simpa only [MvPolynomial.X_pow_eq_monomial] using hdiv)
  simpa only [hmod, add_zero] using
    MvPolynomial.divMonomial_add_modMonomial p (Finsupp.single i n)

/-- A fraction with denominator a power of `Xᵢ` that also admits a denominator involving only a
different variable has numerator divisible by the entire power of `Xᵢ`. -/
theorem X_pow_dvd_of_cross_mul
    (ι k : Type u) [Field k] {i j : ι} (hij : i ≠ j) (n m : ℕ)
    (p q : MvPolynomial ι k)
    (hcross : MvPolynomial.X j ^ m * p = MvPolynomial.X i ^ n * q) :
    (MvPolynomial.X i : MvPolynomial ι k) ^ n ∣ p := by
  have hnot : ¬(MvPolynomial.X i : MvPolynomial ι k) ∣ MvPolynomial.X j ^ m := by
    intro h
    have hX : (MvPolynomial.X i : MvPolynomial ι k) ∣ MvPolynomial.X j :=
      (MvPolynomial.X_prime (R := k) (i := i)).dvd_of_dvd_pow h
    exact hij (MvPolynomial.X_dvd_X.mp hX)
  apply (MvPolynomial.X_prime (R := k) (i := i)).pow_dvd_of_dvd_mul_left n hnot
  exact ⟨q, hcross⟩

/-- The chart fraction `p / 1` associated to a degree-`d` homogeneous polynomial. -/
def polynomialVariableFraction
    (ι k : Type u) [Field k] (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule ι k d) (i : ι) :
    DegreeZeroLocalization (polynomialGrading ι k)
      (natShift (polynomialGrading ι k) d) (.powers (MvPolynomial.X i)) :=
  DegreeZeroLocalization.mk
    { deg := 0
      num := ⟨p.1, by
        change p.1 ∈ polynomialGrading ι k (0 + d)
        simpa using p.2⟩
      den := ⟨1, one_mem_graded (polynomialGrading ι k)⟩
      den_mem := Submonoid.one_mem _ }

/-- Restricting the polynomial section to a variable chart recovers the literal fraction
`p / 1`. -/
theorem variableFractionOfGlobalSection_polynomial
    (ι k : Type u) [Field k] (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule ι k d) (i : ι) :
    variableFractionOfGlobalSection ι k d i
        (polynomialToNatGlobalSections ι k d p) =
      polynomialVariableFraction ι k d p i := by
  apply (projectiveSpace_variableSection_bijective ι k i d).1
  rw [moduleAwayToSection_variableFractionOfGlobalSection]
  rw [polynomialVariableFraction, moduleAwayToSection_mk]
  apply section_ext
  funext x
  apply DegreeZeroLocalization.ext
  rfl

/-- The fractions `p / 1` on any two variable charts agree in the generic localization. -/
theorem polynomialVariableFractionToGeneric_independent
    (ι k : Type u) [Field k] [Nonempty ι] (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule ι k d) (i j : ι) :
    variableFractionToGeneric ι k d i (polynomialVariableFraction ι k d p i) =
      variableFractionToGeneric ι k d j (polynomialVariableFraction ι k d p j) := by
  simp only [variableFractionToGeneric, polynomialVariableFraction,
    DegreeZeroLocalization.mapOfLE_mk]

/-- The variables generate the polynomial ring over its degree-zero part.

This is the hypothesis `degreeOneCharts_coversTop` takes, extracted from the cover proof below
so that the twist results can consume it directly. -/
theorem polynomialVariable_adjoin_eq_top (ι k : Type u) [Field k] :
    Algebra.adjoin (polynomialGrading ι k 0)
      (Set.range fun i => ((MvPolynomial.X i : MvPolynomial ι k))) = ⊤ := by
  set S := Algebra.adjoin (polynomialGrading ι k 0)
    (Set.range fun i => ((MvPolynomial.X i : MvPolynomial ι k))) with hS
  apply top_unique
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C r =>
      exact S.algebraMap_mem
        ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (σ := ι) r⟩
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp =>
      exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

/-- The standard variable basic opens cover polynomial projective space. -/
theorem polynomialVariableBasicOpen_cover (ι k : Type u) [Field k] :
    (⨆ i : ι, ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
      (MvPolynomial.X i)) = ⊤ := by
  apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'
  · intro i
    exact ⟨1, MvPolynomial.isHomogeneous_X k i⟩
  · let S := Algebra.adjoin (polynomialGrading ι k 0)
      (Set.range (MvPolynomial.X : ι → MvPolynomial ι k))
    change S = ⊤
    apply top_unique
    intro p hp
    clear hp
    induction p using MvPolynomial.induction_on with
    | C r =>
        exact S.algebraMap_mem
          ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (σ := ι) r⟩
    | add p q hp hq => exact S.add_mem hp hq
    | mul_X p i hp =>
        exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

/-- A global section of a nonnegative twist on polynomial projective space is represented by a
single homogeneous polynomial. -/
theorem polynomialToNatGlobalSections_surjective
    (ι k : Type u) [Field k] [Nontrivial ι] (d : ℕ) :
    Function.Surjective (polynomialToNatGlobalSections ι k d) := by
  intro s
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  let zi := variableFractionOfGlobalSection ι k d i s
  let zj := variableFractionOfGlobalSection ι k d j s
  obtain ⟨ci, hci⟩ := DegreeZeroLocalization.mk_surjective zi
  obtain ⟨cj, hcj⟩ := DegreeZeroLocalization.mk_surjective zj
  obtain ⟨n, hn⟩ := ci.den_mem
  obtain ⟨m, hm⟩ := cj.den_mem
  have hpowi : (MvPolynomial.X i : MvPolynomial ι k) ^ n ∈
      polynomialGrading ι k n := by
    simpa using SetLike.pow_mem_graded (A := polynomialGrading ι k) n
      (MvPolynomial.isHomogeneous_X k i)
  have hpowj : (MvPolynomial.X j : MvPolynomial ι k) ^ m ∈
      polynomialGrading ι k m := by
    simpa using SetLike.pow_mem_graded (A := polynomialGrading ι k) m
      (MvPolynomial.isHomogeneous_X k j)
  have hdegi : ci.deg = n := by
    apply DirectSum.degree_eq_of_mem_mem (polynomialGrading ι k) ci.den.2
      (hn ▸ hpowi)
    simpa only [← hn] using pow_ne_zero n (MvPolynomial.X_ne_zero (R := k) i)
  have hdegj : cj.deg = m := by
    apply DirectSum.degree_eq_of_mem_mem (polynomialGrading ι k) cj.den.2
      (hm ▸ hpowj)
    simpa only [← hm] using pow_ne_zero m (MvPolynomial.X_ne_zero (R := k) j)
  have hgeneric :
      variableFractionToGeneric ι k d i (DegreeZeroLocalization.mk ci) =
        variableFractionToGeneric ι k d j (DegreeZeroLocalization.mk cj) := by
    rw [hci, hcj, variableFractionToGeneric_apply_globalSection,
      variableFractionToGeneric_apply_globalSection]
  simp only [variableFractionToGeneric, DegreeZeroLocalization.mapOfLE_mk] at hgeneric
  rw [DegreeZeroLocalization.mk_eq_mk_iff] at hgeneric
  obtain ⟨u, hu⟩ := hgeneric
  have hu0 : (u : MvPolynomial ι k) ≠ 0 := by
    have hu' := u.2
    change (u : MvPolynomial ι k) ∉ (⊥ : Ideal _) at hu'
    intro h0
    exact hu' (by simpa only [Ideal.mem_bot] using h0)
  have hcross0 : (cj.den : MvPolynomial ι k) * (ci.num : MvPolynomial ι k) =
      (ci.den : MvPolynomial ι k) * (cj.num : MvPolynomial ι k) :=
    mul_left_cancel₀ hu0 (by simpa only [smul_eq_mul, mul_assoc] using hu)
  have hcross : MvPolynomial.X j ^ m * (ci.num : MvPolynomial ι k) =
      MvPolynomial.X i ^ n * (cj.num : MvPolynomial ι k) := by
    simpa only [hn, hm] using hcross0
  have hdiv : (MvPolynomial.X i : MvPolynomial ι k) ^ n ∣
      (ci.num : MvPolynomial ι k) :=
    X_pow_dvd_of_cross_mul ι k hij n m _ _ hcross
  have hpnum : (ci.num : MvPolynomial ι k) ∈
      MvPolynomial.homogeneousSubmodule ι k (n + d) := by
    have hpnum0 := ci.num.2
    change (ci.num : MvPolynomial ι k) ∈
      polynomialGrading ι k (ci.deg + d) at hpnum0
    simpa only [hdegi] using hpnum0
  let p : MvPolynomial.homogeneousSubmodule ι k d :=
    ⟨MvPolynomial.divMonomial (ci.num : MvPolynomial ι k) (Finsupp.single i n), by
      apply divMonomial_single_mem_homogeneousSubmodule ι k i n d _ hpnum⟩
  refine ⟨p, ?_⟩
  apply section_ext
  funext x
  have hx : x.1 ∈ (⨆ a : ι, ProjectiveSpectrum.basicOpen
      (polynomialGrading ι k) (MvPolynomial.X a)) := by
    rw [polynomialVariableBasicOpen_cover]
    trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let xa : ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
      (MvPolynomial.X a) := ⟨x.1, ha⟩
  have hp_generic : variableFractionToGeneric ι k d i
      (polynomialVariableFraction ι k d p i) =
        variableFractionToGeneric ι k d i
          (variableFractionOfGlobalSection ι k d i s) := by
    change variableFractionToGeneric ι k d i
      (polynomialVariableFraction ι k d p i) =
        variableFractionToGeneric ι k d i zi
    rw [← hci]
    simp only [polynomialVariableFraction, variableFractionToGeneric,
      DegreeZeroLocalization.mapOfLE_mk]
    rw [DegreeZeroLocalization.mk_eq_mk_iff]
    refine ⟨1, ?_⟩
    have hdenmul : (ci.den : MvPolynomial ι k) * (p : MvPolynomial ι k) =
        (ci.num : MvPolynomial ι k) := by
      rw [← hn]
      simpa [p] using
        X_pow_mul_divMonomial_single ι k i n (ci.num : MvPolynomial ι k) hdiv
    simpa [smul_eq_mul] using hdenmul
  have ha_fraction : variableFractionOfGlobalSection ι k d a s =
      polynomialVariableFraction ι k d p a := by
    apply variableFractionToGeneric_injective ι k d a
    calc
      variableFractionToGeneric ι k d a
          (variableFractionOfGlobalSection ι k d a s) =
          s.1 ⟨polynomialGenericPoint ι k, Set.mem_univ _⟩ :=
        variableFractionToGeneric_apply_globalSection ι k d a s
      _ = variableFractionToGeneric ι k d i
          (variableFractionOfGlobalSection ι k d i s) :=
        (variableFractionToGeneric_apply_globalSection ι k d i s).symm
      _ = variableFractionToGeneric ι k d i
          (polynomialVariableFraction ι k d p i) := hp_generic.symm
      _ = variableFractionToGeneric ι k d a
          (polynomialVariableFraction ι k d p a) :=
        polynomialVariableFractionToGeneric_independent ι k d p i a
  have hsections := congr_arg (fun t => t.1 xa)
    (congr_arg (moduleAwayToSection (polynomialGrading ι k)
      (natShift (polynomialGrading ι k) d) (MvPolynomial.X a)) ha_fraction)
  rw [moduleAwayToSection_variableFractionOfGlobalSection,
    ← variableFractionOfGlobalSection_polynomial,
    moduleAwayToSection_variableFractionOfGlobalSection] at hsections
  exact hsections.symm

/-- Distinct homogeneous polynomials define distinct global sections. -/
theorem polynomialToNatGlobalSections_injective
    (ι k : Type u) [Field k] [Nonempty ι] (d : ℕ) :
    Function.Injective (polynomialToNatGlobalSections ι k d) := by
  intro p q hpq
  let i : ι := Classical.choice inferInstance
  have hchart := congr_arg (variableFractionOfGlobalSection ι k d i) hpq
  rw [variableFractionOfGlobalSection_polynomial,
    variableFractionOfGlobalSection_polynomial] at hchart
  have hgeneric := congr_arg (variableFractionToGeneric ι k d i) hchart
  simp only [variableFractionToGeneric, polynomialVariableFraction,
    DegreeZeroLocalization.mapOfLE_mk] at hgeneric
  rw [DegreeZeroLocalization.mk_eq_mk_iff] at hgeneric
  obtain ⟨u, hu⟩ := hgeneric
  have hu0 : (u : MvPolynomial ι k) ≠ 0 := by
    have hu' := u.2
    change (u : MvPolynomial ι k) ∉ (⊥ : Ideal _) at hu'
    intro h0
    exact hu' (by simpa only [Ideal.mem_bot] using h0)
  apply Subtype.ext
  apply mul_left_cancel₀ hu0
  simpa [smul_eq_mul] using hu

/-- Concrete additive comparison between degree-`d` homogeneous polynomials and global sections
of the natural-shift model of `O(d)`. -/
noncomputable def polynomialNatGlobalSectionsAddEquiv
    (ι k : Type u) [Field k] [Nontrivial ι] (d : ℕ) :
    MvPolynomial.homogeneousSubmodule ι k d ≃+
      polynomialNatGlobalSections ι k d :=
  AddEquiv.ofBijective (polynomialToNatGlobalSections ι k d)
    ⟨polynomialToNatGlobalSections_injective ι k d,
      polynomialToNatGlobalSections_surjective ι k d⟩

/-- Global sections of the integer-indexed twisting sheaf `O(d)`. -/
abbrev polynomialTwistingGlobalSections (ι k : Type u) [Field k] (d : ℕ) :=
  (twistingSheaf (polynomialGrading ι k) (d : ℤ)).val.obj
    (op (⊤ : (AlgebraicGeometry.Proj (polynomialGrading ι k)).Opens))

/-- For a nonnegative twist, transport global sections from the natural-shift model to the
integer-indexed twisting sheaf. -/
noncomputable def polynomialNatToTwistingGlobalSectionsAddEquiv
    (ι k : Type u) [Field k] (d : ℕ) :
    polynomialNatGlobalSections ι k d ≃+
      polynomialTwistingGlobalSections ι k d :=
  (asIso ((twistingSheafOfNatIso (polynomialGrading ι k) d).hom.app
    (⊤ : (AlgebraicGeometry.Proj (polynomialGrading ι k)).Opens))).addCommGroupIsoToAddEquiv.symm

/-- The concrete global-section comparison requested for polynomial projective space:
degree-`d` homogeneous polynomials are exactly `Γ(Proj k[Xᵢ], O(d))`. -/
noncomputable def polynomialTwistingGlobalSectionsAddEquiv
    (ι k : Type u) [Field k] [Nontrivial ι] (d : ℕ) :
    MvPolynomial.homogeneousSubmodule ι k d ≃+
      polynomialTwistingGlobalSections ι k d :=
  (polynomialNatGlobalSectionsAddEquiv ι k d).trans
    (polynomialNatToTwistingGlobalSectionsAddEquiv ι k d)

/-- Global sections equipped with the canonical field-module structure transported through the
explicit polynomial comparison.  This avoids pretending that a separate base-ring action is
definitionally present in Mathlib's sheaf-of-modules section type. -/
noncomputable def polynomialTwistingGlobalSectionsModule
    (ι k : Type u) [Field k] [Nontrivial ι] (d : ℕ) : ModuleCat.{u} k := by
  let e := polynomialTwistingGlobalSectionsAddEquiv ι k d
  letI : Module k (polynomialTwistingGlobalSections ι k d) := e.symm.module k
  exact ModuleCat.of k (polynomialTwistingGlobalSections ι k d)

/-- The concrete comparison as an isomorphism of `k`-modules, using the transported action made
explicit by `polynomialTwistingGlobalSectionsModule`. -/
noncomputable def polynomialTwistingGlobalSectionsModuleIso
    (ι k : Type u) [Field k] [Nontrivial ι] (d : ℕ) :
    ModuleCat.of k (MvPolynomial.homogeneousSubmodule ι k d) ≅
      polynomialTwistingGlobalSectionsModule ι k d := by
  let e := polynomialTwistingGlobalSectionsAddEquiv ι k d
  letI : Module k (polynomialTwistingGlobalSections ι k d) := e.symm.module k
  exact LinearEquiv.toModuleIso (e.symm.linearEquiv (A := k)).symm

/-- Nonnegative twists on polynomial projective space are quasi-coherent.

The variable charts have degree one and cover, which is exactly the hypothesis of
`natShift_isQuasicoherent`.  No comparison on higher-degree charts is needed or available. -/
theorem polynomialNatShift_isQuasicoherent (ι k : Type u) [Field k] (d : ℕ) :
    (associatedSheaf (polynomialGrading ι k)
      (natShift (polynomialGrading ι k) d)).IsQuasicoherent :=
  natShift_isQuasicoherent (polynomialGrading ι k)
    (fun i => ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X k i⟩) d
    (polynomialVariable_adjoin_eq_top ι k)

/-! ## Degreewise algebra for the variable Čech cover -/

/-- The product of the variables indexing one `(n + 1)`-fold Čech intersection. -/
def polynomialVariableCechDenominator
    (ι k : Type u) [Field k] {n : ℕ} (x : Fin (n + 1) → ι) :
    MvPolynomial ι k :=
  ∏ a, MvPolynomial.X (x a)

/-- The Čech denominator for an `(n + 1)`-fold intersection is homogeneous of degree `n + 1`. -/
theorem polynomialVariableCechDenominator_mem
    (ι k : Type u) [Field k] {n : ℕ} (x : Fin (n + 1) → ι) :
    polynomialVariableCechDenominator ι k x ∈ polynomialGrading ι k (n + 1) := by
  classical
  simpa [polynomialVariableCechDenominator] using
    SetLike.prod_mem_graded (polynomialGrading ι k)
      (fun _ : Fin (n + 1) => 1) (fun a => MvPolynomial.X (x a))
      (F := Finset.univ) (fun a _ => MvPolynomial.isHomogeneous_X k (x a))

/-- The basic open of the product denominator is exactly the finite intersection of the
corresponding variable charts. -/
theorem basicOpen_polynomialVariableCechDenominator
    (ι k : Type u) [Field k] {n : ℕ} (x : Fin (n + 1) → ι) :
    ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (polynomialVariableCechDenominator ι k x) =
      ⨅ a, ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
        (MvPolynomial.X (x a)) := by
  classical
  have hInf : (⨅ a, ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
      (MvPolynomial.X (x a))) =
      Finset.univ.inf fun a => ProjectiveSpectrum.basicOpen
        (polynomialGrading ι k) (MvPolynomial.X (x a)) := by
    rw [Finset.inf_eq_iInf]
    simp
  rw [hInf]
  unfold polynomialVariableCechDenominator
  change ProjectiveSpectrum.basicOpen (polynomialGrading ι k)
      (∏ a ∈ Finset.univ, MvPolynomial.X (x a)) =
    Finset.univ.inf fun a => ProjectiveSpectrum.basicOpen
      (polynomialGrading ι k) (MvPolynomial.X (x a))
  generalize (Finset.univ : Finset (Fin (n + 1))) = F
  induction F using Finset.induction_on with
  | empty => simp
  | @insert a F ha ih =>
      rw [Finset.prod_insert ha, Finset.inf_insert, ProjectiveSpectrum.basicOpen_mul, ih]

/-- The algebraic degree-`d` term attached to one variable Čech intersection.  It is a
degree-zero homogeneous localization, with no finite-dimensionality assertion. -/
abbrev polynomialVariableCechTerm
    (ι k : Type u) [Field k] (d n : ℕ) (x : Fin (n + 1) → ι) :=
  DegreeZeroLocalization (polynomialGrading ι k)
    (natShift (polynomialGrading ι k) d)
      (.powers (polynomialVariableCechDenominator ι k x))

/-- Degree-`n` algebraic Čech cochains for the nonnegative twist `O(d)`, expressed as the
product of the explicit homogeneous localizations over all variable tuples. -/
abbrev polynomialVariableCechCochains
    (ι k : Type u) [Field k] (d n : ℕ) :=
  ∀ x : Fin (n + 1) → ι, polynomialVariableCechTerm ι k d n x

end CohLean.AlgebraicGeometry.Proj
