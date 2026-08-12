/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Families.Basic
import BridgelandStabLean.StabilityCondition.Support.Quotient

/-!
# Ordinary stability-in-families interface

This file combines the three ordinary clauses of Definition 20.5 with the
uniform support and boundedness clauses (4)--(5) of Definition 21.15 of
arXiv:1902.08184v4.  It is the top-level ordinary abstract family package.

The index types stand for geometric base-change, object, fiber, and numerical
moduli tests supplied by a client.  The library neither constructs nor
recognizes those geometric objects.  The support field, by contrast, is the
genuine quotient-uniform quadratic support predicate already implemented in
the support subsystem.
-/

namespace BridgelandStabLean.StabilityFamilies

open BridgelandStabLean.Support

noncomputable section

variable {JCharge JOpen D I M V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

private local instance quotientSubmoduleClosed (V₀ : Submodule ℝ V) :
    IsClosed (V₀ : Set V) :=
  V₀.closed_of_finiteDimensional

/-- The five separately auditable ordinary family conditions: Definition
20.5(1)--(3) followed by Definition 21.15(4)--(5). -/
structure OrdinaryStabilityInFamiliesData
    (charge : JCharge → ChargeProbe ℂ)
    (stable : JOpen → OpenLocusProbe)
    (dedekind : DedekindHNProblem D)
    (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] W)
    (hV₀ : V₀ ≤ LinearMap.ker Z) (semistableClasses : I → Set V)
    (boundedness : BoundednessProblem M) : Prop where
  /-- Definition 20.5(1)--(3). -/
  definition20_5 : OrdinaryDefinition20_5Conditions charge stable dedekind
  /-- Definition 21.15(4). -/
  uniformSupport : HasUniformQuadraticSupportPropertyModulo
    V₀ Z hV₀ semistableClasses
  /-- Definition 21.15(5). -/
  bounded : UniversalBoundedness boundedness

/-- A concrete `PUnit`-indexed constant-family witness.

All universal index types are inhabited, so this is not an empty-quantifier
witness.  The only mathematical input is genuine quadratic support for the
single selected locus; the topological, HN-witness, and boundedness probes are
manifest constant data.  It does not assert that `PUnit` is a geometric base. -/
theorem OrdinaryStabilityInFamiliesData.punit
    (a : ℂ) (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] W)
    (hV₀ : V₀ ≤ LinearMap.ker Z) (S : Set V)
    (hQ : HasQuadraticSupportProperty (quotientCharge V₀ Z hV₀)
      (V₀.mkQ '' S)) :
    OrdinaryStabilityInFamiliesData
      (fun _ : PUnit.{1} ↦ ChargeProbe.constant PUnit.{1} a)
      (fun _ : PUnit.{1} ↦ OpenLocusProbe.full PUnit.{1})
      (DedekindHNProblem.constant PUnit.{1} PUnit.{1})
      V₀ Z hV₀ (fun _ : PUnit.{1} ↦ S)
      (BoundednessProblem.trivial PUnit.{1}) where
  definition20_5 :=
    { locallyConstantCharge :=
        universallyLocallyConstantCharge_constant PUnit.{1}
          (fun _ : PUnit.{1} ↦ a)
      opennessOfGeometricStability := universalOpenness_full PUnit.{1}
      dedekindHN := integratesAfterDedekindBaseChange_constant PUnit.{1} PUnit.{1} }
  uniformSupport := hQ.constant_modulo V₀ Z hV₀ PUnit.{1}
  bounded := universalBoundedness_trivial PUnit.{1}

/-- The `PUnit` witness exposes the locally constant charge clause. -/
theorem ordinary_punit_locallyConstantCharge
    (a : ℂ) (V₀ : Submodule ℝ V) (Z : V →ₗ[ℝ] W)
    (hV₀ : V₀ ≤ LinearMap.ker Z) (S : Set V)
    (hQ : HasQuadraticSupportProperty (quotientCharge V₀ Z hV₀)
      (V₀.mkQ '' S)) :
    UniversallyLocallyConstantCharge
      (fun _ : PUnit.{1} ↦ ChargeProbe.constant PUnit.{1} a) :=
  (OrdinaryStabilityInFamiliesData.punit a V₀ Z hV₀ S hQ).definition20_5.locallyConstantCharge

end

end BridgelandStabLean.StabilityFamilies
