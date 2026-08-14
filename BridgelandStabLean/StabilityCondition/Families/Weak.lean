/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Families.Basic
import BridgelandStabLean.StabilityCondition.Weak.Support.Quadratic
import BridgelandStabLean.StabilityCondition.Weak.Tilting.Property

/-!
# Weak stability data in an abstract family

This module binds the logical probes of `Families.Basic` to the repository's
actual weak-stability and quotient-support APIs.  The binding is intentionally
limited to an indexed family of weak stability functions on one fixed
category and one fixed heart.  It is therefore an abstract model of the
separable clauses of Definitions 20.5 and 21.15 of arXiv:1902.08184v4, not a
construction of derived categories on geometric fibers.

The fields of `WeakStabilityInFamiliesData` record:

* Definition 20.5(0): a `ℚ[i]`-valued charge and a noetherian zero-charge
  torsion subcategory on every fiber;
* Definition 20.5(1), (2'), and (3') through the probes from `Families.Basic`;
* Definition 21.15(4) using the genuine one-form-on-the-quotient predicate
  from `Weak.Support.Quadratic`;
* Definition 21.15(5) as an explicit caller-supplied boundedness obligation.

No field asserts the existence of base changes, relative hearts, moduli
spaces, or bounded families.  Those remain data which a geometric client must
supply.
-/

namespace BridgelandStabLean.StabilityFamilies

open BridgelandStabLean.Foundation
open CategoryTheory Limits Pretriangulated CategoryTheory.Triangulated
open BridgelandStabLean.Support
open BridgelandStabLean.WeakStability

noncomputable section

universe u

/-- The coefficient condition denoted `ℚ[i]` in Definition 20.5(0): every
complex value admits rational real and imaginary coefficients.  This is a
pointwise range predicate, not a bundled Gaussian-rational subring object. -/
def HasGaussianRationalValues {A : Type*} (Z : A → ℂ) : Prop :=
  ∀ a, ∃ p q : ℚ, Z a = (p : ℂ) + (q : ℂ) * Complex.I

/-- The zero function is Gaussian-rational-valued. -/
theorem hasGaussianRationalValues_zero {A : Type*} :
    HasGaussianRationalValues (fun _ : A ↦ (0 : ℂ)) := by
  intro a
  exact ⟨0, 0, by simp⟩

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C] [IsTriangulated C]

variable {I V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {v : K₀ C →+ V}

/-- An actual charge probe for the fixed-category model: every point chooses
a fiber index and a numerical class, so the observed value is forced to be
the corresponding weak charge rather than an unrelated function. -/
structure WeakChargeProbe (I Λ : Type*) where
  /-- Points of the supplied base-change test. -/
  Point : Type u
  /-- Their topology. -/
  topology : TopologicalSpace Point
  /-- Which indexed weak stability function is observed at a point. -/
  fiber : Point → I
  /-- Which fixed-category Grothendieck class is observed at a point. -/
  klass : Point → Λ

/-- Forget a bound weak charge probe to its derived complex-valued probe. -/
def WeakChargeProbe.toChargeProbe {t : TStructure C}
    (W : I → WeakStabilityFunction t) (P : WeakChargeProbe I (K₀ C)) :
    ChargeProbe ℂ where
  Point := P.Point
  topology := P.topology
  value := fun x ↦ (W (P.fiber x)).Z (P.klass x)

/-- A constant fixed-fiber, fixed-class charge probe. -/
def WeakChargeProbe.constant
    (X : Type u) [TopologicalSpace X] (i : I) { Λ : Type* } (k : Λ) :
    WeakChargeProbe I Λ where
  Point := X
  topology := inferInstance
  fiber := Function.const X i
  klass := Function.const X k

omit [IsTriangulated C] in
/-- A constant weak charge probe is locally constant. -/
theorem WeakChargeProbe.constant_isLocallyConstant {t : TStructure C}
    (W : I → WeakStabilityFunction t)
    (X : Type u) [TopologicalSpace X] (i : I) (k : K₀ C) :
    ((WeakChargeProbe.constant X i k).toChargeProbe W).IsLocallyConstant := by
  unfold ChargeProbe.IsLocallyConstant WeakChargeProbe.toChargeProbe
  change _root_.IsLocallyConstant
    (Function.const X ((W i).Z k))
  exact _root_.IsLocallyConstant.const _

/-- A semistability probe bound to actual objects and actual weak stability
functions in the fixed-category model. -/
structure WeakSemistabilityProbe (I C : Type*) where
  /-- Points of the supplied base-change test. -/
  Point : Type u
  /-- Their topology. -/
  topology : TopologicalSpace Point
  /-- The distinguished generic point. -/
  genericPoint : Point
  /-- Which weak stability function is used at each point. -/
  fiber : Point → I
  /-- The fixed-category object tested at each point. -/
  object : Point → C

/-- Forget a bound weak probe to the generic semistability locus it defines. -/
def WeakSemistabilityProbe.toGenericProbe {t : TStructure C}
    (W : I → WeakStabilityFunction t) (P : WeakSemistabilityProbe I C) :
    GenericSemistabilityProbe where
  Point := P.Point
  topology := P.topology
  genericPoint := P.genericPoint
  semistableLocus := {x | (W (P.fiber x)).IsSemistable (P.object x)}

/-- A constant fixed-fiber, fixed-object semistability probe. -/
def WeakSemistabilityProbe.constant
    (X : Type u) [TopologicalSpace X] (genericPoint : X)
    (i : I) (E : C) : WeakSemistabilityProbe I C where
  Point := X
  topology := inferInstance
  genericPoint := genericPoint
  fiber := Function.const X i
  object := Function.const X E

omit [IsTriangulated C] in
/-- A constant semistability probe is generically open: its locus is either
the whole space or empty. -/
theorem WeakSemistabilityProbe.constant_isGenericallyOpen
    {t : TStructure C} (W : I → WeakStabilityFunction t)
    (X : Type u) [TopologicalSpace X] (genericPoint : X)
    (i : I) (E : C) :
    GenericSemistabilityProbe.IsGenericallyOpen
      ((WeakSemistabilityProbe.constant X genericPoint i E).toGenericProbe W) := by
  intro hgeneric
  refine ⟨Set.univ, ?_, Set.mem_univ _, ?_⟩
  · exact @isOpen_univ X inferInstance
  · intro x _
    exact hgeneric

/-- Definition 20.5(0), bound to actual weak stability functions. -/
structure WeakDefinition20_5ClauseZero {t : TStructure C}
    (W : I → WeakStabilityFunction t) : Prop where
  /-- Every fiber charge is defined over `ℚ[i]`. -/
  gaussianRationalCharge : ∀ i, HasGaussianRationalValues (W i).Z
  /-- Every zero-charge class is a noetherian torsion subcategory. -/
  zeroChargeNoetherian : ∀ i,
    IsNoetherianTorsionSubcategory t (W i).zeroCharge

omit [IsTriangulated C] in
/-- Clause (0) is preserved by reindexing. -/
theorem WeakDefinition20_5ClauseZero.reindex {J : Type*}
    {t : TStructure C} {W : I → WeakStabilityFunction t}
    (h : WeakDefinition20_5ClauseZero W) (f : J → I) :
    WeakDefinition20_5ClauseZero (fun j ↦ W (f j)) :=
  ⟨fun j ↦ h.gaussianRationalCharge (f j),
    fun j ↦ h.zeroChargeNoetherian (f j)⟩

omit [IsTriangulated C] in
/-- One fiber satisfying clause (0) gives a constant family satisfying it. -/
theorem weakDefinition20_5ClauseZero_constant {t : TStructure C}
    (W : WeakStabilityFunction t)
    (hZ : HasGaussianRationalValues W.Z)
    (hN : IsNoetherianTorsionSubcategory t W.zeroCharge)
    (I : Type*) :
    WeakDefinition20_5ClauseZero (fun _ : I ↦ W) :=
  ⟨fun _ ↦ hZ, fun _ ↦ hN⟩

/-- Single-fiber quotient support data, introduced only to state the honest
constant-family constructor below. -/
private local instance quotientSubmoduleClosed (V₀ : Submodule ℝ V) :
    IsClosed (V₀ : Set V) :=
  V₀.closed_of_finiteDimensional

/-- The actual one-fiber charge, zero-class, and quotient-quadratic-support
package used to build a uniform constant family. -/
structure WeakQuotientQuadraticSupportData {t : TStructure C}
    (W : WeakStabilityFunction t) (v : K₀ C →+ V)
    (V₀ : Submodule ℝ V) (Zlin : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Zlin) : Prop where
  /-- The real-linear charge realizes the weak charge. -/
  charge_compatible : ∀ k : K₀ C, Zlin (v k) = W.Z k
  /-- Every zero-charge class is killed in the quotient. -/
  zero_class_mem : ∀ E : C, W.zeroCharge E → v (K₀.of C E) ∈ V₀
  /-- Genuine quadratic support on the mapped semistable locus. -/
  quadratic : HasQuadraticSupportProperty
    (quotientCharge V₀ Zlin hV₀)
    (V₀.mkQ '' W.semistableClasses v)

omit [IsTriangulated C] in
/-- Single-fiber quotient support gives the same fixed form on every member
of a constant indexed family. -/
theorem WeakQuotientQuadraticSupportData.constant {t : TStructure C}
    {W : WeakStabilityFunction t} {V₀ : Submodule ℝ V}
    {Zlin : V →ₗ[ℝ] ℂ} {hV₀ : V₀ ≤ LinearMap.ker Zlin}
    (h : WeakQuotientQuadraticSupportData W v V₀ Zlin hV₀)
    (I : Type*) :
    WeakStabilityFunction.QuotientUniformQuadraticSupportData
      (fun _ : I ↦ W) v V₀ Zlin hV₀ :=
  ⟨fun _ ↦ h.charge_compatible,
    fun _ ↦ h.zero_class_mem,
    h.quadratic.constant_modulo V₀ Zlin hV₀ I⟩

omit [IsTriangulated C] in
/-- Quotient-uniform weak support is preserved by reindexing. -/
theorem quotientUniformQuadraticSupportData_reindex {J : Type*}
    {t : TStructure C} {W : I → WeakStabilityFunction t}
    {V₀ : Submodule ℝ V} {Zlin : V →ₗ[ℝ] ℂ}
    {hV₀ : V₀ ≤ LinearMap.ker Zlin}
    (h : WeakStabilityFunction.QuotientUniformQuadraticSupportData
      W v V₀ Zlin hV₀)
    (f : J → I) :
    WeakStabilityFunction.QuotientUniformQuadraticSupportData
      (fun j ↦ W (f j)) v V₀ Zlin hV₀ :=
  ⟨fun j ↦ h.charge_compatible (f j),
    fun j ↦ h.zero_class_mem (f j), h.quadratic.reindex f⟩

/-- The separable clauses of weak stability in families which can be stated
in the current abstract library.  Every source clause is a named projection.

The `charge` and `semistable` probes are bound to actual weak functions via
`toChargeProbe` and `toGenericProbe`; the support field is the actual
quotient-uniform support package from issue #82.  Relative HN and boundedness
remain explicit geometric inputs. -/
structure WeakStabilityInFamiliesData
    {JCharge JGeneric D M : Type u} {t : TStructure C}
    (W : I → WeakStabilityFunction t)
    (charge : JCharge → WeakChargeProbe I (K₀ C))
    (semistable : JGeneric → WeakSemistabilityProbe I C)
    (dedekind : WeakDedekindHNProblem D)
    (V₀ : Submodule ℝ V) (Zlin : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Zlin)
    (boundedness : BoundednessProblem M) : Prop where
  /-- Definition 20.5(0). -/
  clauseZero : WeakDefinition20_5ClauseZero W
  /-- Definition 20.5(1), (2'), and (3'). -/
  definition20_5 : WeakDefinition20_5Conditions
    (fun j ↦ (charge j).toChargeProbe W)
    (fun j ↦ (semistable j).toGenericProbe W) dedekind
  /-- Definition 21.15(4). -/
  uniformSupport :
    WeakStabilityFunction.QuotientUniformQuadraticSupportData
      W v V₀ Zlin hV₀
  /-- Definition 21.15(5), retained as a geometric premise. -/
  bounded : UniversalBoundedness boundedness

omit [IsTriangulated C] in
/-- A fully explicit constant-family witness for the abstract interface.

It starts from one weak function satisfying clause (0) and one single-fiber
quotient support package.  Charge and semistability probes are constant on
`PUnit`; the relative HN witness type is `PUnit`; boundedness is the true
predicate.  This proves logical nonvacuity without claiming that `PUnit`
models a nontrivial geometric family. -/
theorem WeakStabilityInFamiliesData.constant
    {JCharge JGeneric D M : Type u} {t : TStructure C}
    (W : WeakStabilityFunction t)
    (hZ : HasGaussianRationalValues W.Z)
    (hN : IsNoetherianTorsionSubcategory t W.zeroCharge)
    (V₀ : Submodule ℝ V) (Zlin : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Zlin)
    (hQ : WeakQuotientQuadraticSupportData W v V₀ Zlin hV₀)
    (I : Type*) (i₀ : I) (k : JCharge → K₀ C) (E : JGeneric → C) :
    WeakStabilityInFamiliesData (v := v)
      (fun _ : I ↦ W)
      (fun j ↦ WeakChargeProbe.constant PUnit i₀ (k j))
      (fun j ↦ WeakSemistabilityProbe.constant PUnit PUnit.unit i₀ (E j))
      (WeakDedekindHNProblem.constant D PUnit)
      V₀ Zlin hV₀ (BoundednessProblem.trivial M) where
  clauseZero := weakDefinition20_5ClauseZero_constant W hZ hN I
  definition20_5 :=
    { locallyConstantCharge := fun j ↦
        WeakChargeProbe.constant_isLocallyConstant
          (fun _ : I ↦ W) PUnit i₀ (k j)
      genericOpennessOfSemistability := fun j ↦
        WeakSemistabilityProbe.constant_isGenericallyOpen
          (fun _ : I ↦ W) PUnit PUnit.unit i₀ (E j)
      dedekindWeakHN :=
        weakIntegratesAfterDedekindBaseChange_constant D PUnit }
  uniformSupport := hQ.constant I
  bounded := universalBoundedness_trivial M

omit [IsTriangulated C] in
/-- The fully inhabited `PUnit` specialization of `constant`.  Every
universal index in the returned interface has an element, so its clauses are
not discharged by empty-index quantification. -/
theorem WeakStabilityInFamiliesData.punit
    {t : TStructure C} (W : WeakStabilityFunction t)
    (hZ : HasGaussianRationalValues W.Z)
    (hN : IsNoetherianTorsionSubcategory t W.zeroCharge)
    (V₀ : Submodule ℝ V) (Zlin : V →ₗ[ℝ] ℂ)
    (hV₀ : V₀ ≤ LinearMap.ker Zlin)
    (hQ : WeakQuotientQuadraticSupportData W v V₀ Zlin hV₀)
    (k : K₀ C) (E : C) :
    WeakStabilityInFamiliesData (v := v)
      (fun _ : PUnit.{1} ↦ W)
      (fun _ : PUnit.{1} ↦
        WeakChargeProbe.constant PUnit.{1} PUnit.unit k)
      (fun _ : PUnit.{1} ↦
        WeakSemistabilityProbe.constant PUnit.{1} PUnit.unit PUnit.unit E)
      (WeakDedekindHNProblem.constant PUnit.{1} PUnit.{1})
      V₀ Zlin hV₀ (BoundednessProblem.trivial PUnit.{1}) :=
  WeakStabilityInFamiliesData.constant W hZ hN V₀ Zlin hV₀ hQ
    PUnit.{1} PUnit.unit (fun _ : PUnit.{1} ↦ k)
      (fun _ : PUnit.{1} ↦ E)

end

end BridgelandStabLean.StabilityFamilies
