/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.StructureModule
import DerivedAlgGeo.AlgebraicGeometry.Proj.Modules.TwistLocalization

/-!
# Nonnegative twists on degree-one Proj charts

Multiplication and division by a degree-one homogeneous element `f` identify `A(d)` with `A`
over `D₊(f)`.  This file lifts the localization equivalence to the locally fractional sheaves and
then identifies the canonical map

`(A(d)₍f₎)₀ ⟶ Γ(D₊(f), A(d)̃)`

as an equivalence.  Thus the degree-one charts used by polynomial projective space no longer
require a `BasicOpenSectionData` certificate.
-/

noncomputable section

open CategoryTheory DirectSum Opposite SetLike TopCat TopologicalSpace
open scoped DirectSum Pointwise

namespace AlgebraicGeometry.Proj

universe u

variable {A σ : Type u}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

local notation3 "X" => ProjectiveSpectrum.top 𝒜
local notation3 "𝒪" => AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf 𝒜

/-- The pointwise trivialization of `A(d)` at a point lying in `D₊(f)`.

The membership proof is taken directly rather than through a bundled element of the chart, so
that one equivalence serves every open contained in `D₊(f)`. -/
noncomputable def natShiftFiberLinearEquivOfMem {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {x : ProjectiveSpectrum 𝒜} (hx : x ∈ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Fiber 𝒜 (natShift 𝒜 d) x ≃ₗ[
      HomogeneousLocalization 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl]
        Fiber 𝒜 𝒜 x :=
  DegreeZeroLocalization.natShiftLinearEquivOfMem 𝒜 hf d hx

/-- The pointwise trivialization of `A(d)` at a point of `D₊(f)`. -/
noncomputable def natShiftFiberLinearEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    (x : ProjectiveSpectrum.basicOpen 𝒜 f) :
    Fiber 𝒜 (natShift 𝒜 d) x.1 ≃ₗ[
      HomogeneousLocalization 𝒜 x.1.asHomogeneousIdeal.toIdeal.primeCompl]
        Fiber 𝒜 𝒜 x.1 :=
  natShiftFiberLinearEquivOfMem 𝒜 hf d x.2

/-- Divide a locally fractional section of `A(d)̃` by `f ^ d`, over any open contained in
`D₊(f)`.

The trivialization is pointwise, so nothing in the construction refers to the chart itself: only
membership in `D₊(f)` is used, and `hU` supplies exactly that. -/
noncomputable def natShiftSectionToSelfOn {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj (op U)) :
    (associatedSheafInType 𝒜 𝒜).1.obj (op U) := by
  refine ⟨fun x => natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2) (s.1 x), ?_⟩
  intro x
  obtain ⟨V, hxV, i, e, r, t, ht, h⟩ := s.2 x
  refine ⟨V, hxV, i, e + d, r,
    ⟨(t : A) * f ^ d,
      by simpa using SetLike.mul_mem_graded t.2 (SetLike.pow_mem_graded d hf)⟩,
    (fun y => y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem
      (ht y) (y.1.asHomogeneousIdeal.toIdeal.primeCompl.pow_mem (hU (i y).2) d)),
    fun y => ?_⟩
  · change natShiftFiberLinearEquivOfMem 𝒜 hf d (hU (i y).2) (s.1 (i y)) = _
    have hy := h y
    change s.1 (i y) = _ at hy
    rw [hy]
    exact DegreeZeroLocalization.natShiftLinearEquivOfMem_apply_mk
      𝒜 hf d (hU (i y).2) _

/-- Multiply a locally fractional section of `Ã` by `f ^ d`, over any open contained in
`D₊(f)`. -/
noncomputable def natShiftSectionFromSelfOn {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (s : (associatedSheafInType 𝒜 𝒜).1.obj (op U)) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj (op U) := by
  refine ⟨fun x => (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).symm (s.1 x), ?_⟩
  intro x
  obtain ⟨V, hxV, i, e, r, t, ht, h⟩ := s.2 x
  refine ⟨V, hxV, i, e,
    ⟨(r : A) * f ^ d,
      by simpa using SetLike.mul_mem_graded r.2 (SetLike.pow_mem_graded d hf)⟩,
    t, ht, fun y => ?_⟩
  change (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU (i y).2)).symm (s.1 (i y)) = _
  have hy := h y
  change s.1 (i y) = _ at hy
  rw [hy]
  exact DegreeZeroLocalization.natShiftLinearEquivOfMem_symm_apply_mk
    𝒜 hf d (hU (i y).2) _

/-- Divide a locally fractional section of `A(d)̃` by `f ^ d`. -/
noncomputable def natShiftSectionToSelf {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    (s : (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (associatedSheafInType 𝒜 𝒜).1.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  natShiftSectionToSelfOn 𝒜 hf d le_rfl s

/-- Multiply a locally fractional section of `Ã` by `f ^ d`. -/
noncomputable def natShiftSectionFromSelf {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    (s : (associatedSheafInType 𝒜 𝒜).1.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj
      (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  natShiftSectionFromSelfOn 𝒜 hf d le_rfl s

/-- Dividing by `f ^ d` commutes with restriction to a smaller open.

This is what makes the pointwise trivialization a map of presheaves rather than a family of
unrelated maps: restriction in `M̃` is precomposition of the underlying function, and the
trivialization is applied pointwise, so the two operations do not interact. -/
theorem natShiftSectionToSelfOn_map {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U U' : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (hU' : U' ≤ U)
    (s : (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj (op U)) :
    (associatedSheafInType 𝒜 𝒜).1.map (homOfLE hU').op
        (natShiftSectionToSelfOn 𝒜 hf d hU s) =
      natShiftSectionToSelfOn 𝒜 hf d (hU'.trans hU)
        ((associatedSheafInType 𝒜 (natShift 𝒜 d)).1.map (homOfLE hU').op s) := by
  apply section_ext
  funext x
  rfl

/-- Multiplying by `f ^ d` commutes with restriction to a smaller open. -/
theorem natShiftSectionFromSelfOn_map {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U U' : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) (hU' : U' ≤ U)
    (s : (associatedSheafInType 𝒜 𝒜).1.obj (op U)) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.map (homOfLE hU').op
        (natShiftSectionFromSelfOn 𝒜 hf d hU s) =
      natShiftSectionFromSelfOn 𝒜 hf d (hU'.trans hU)
        ((associatedSheafInType 𝒜 𝒜).1.map (homOfLE hU').op s) := by
  apply section_ext
  funext x
  rfl

/-- Over any open contained in `D₊(f)`, a nonnegative twist is additively equivalent to the
structure module when `f` has degree one. -/
noncomputable def natShiftSectionAddEquivOn {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj (op U) ≃+
      (associatedSheafInType 𝒜 𝒜).1.obj (op U) where
  toFun := natShiftSectionToSelfOn 𝒜 hf d hU
  invFun := natShiftSectionFromSelfOn 𝒜 hf d hU
  left_inv s := by
    apply section_ext
    funext x
    exact (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).symm_apply_apply (s.1 x)
  right_inv s := by
    apply section_ext
    funext x
    exact (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).apply_symm_apply (s.1 x)
  map_add' s t := by
    apply section_ext
    funext x
    exact (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).map_add (s.1 x) (t.1 x)

/-- Over any open contained in `D₊(f)`, the chart trivialization is linear over the
structure-sheaf sections of that open. -/
noncomputable def natShiftSectionLinearEquivOn {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    {U : Opens X} (hU : U ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj (op U) ≃ₗ[𝒪.1.obj (op U)]
      (associatedSheafInType 𝒜 𝒜).1.obj (op U) :=
  { natShiftSectionAddEquivOn 𝒜 hf d hU with
    map_smul' := fun r s => by
      apply section_ext
      funext x
      exact (natShiftFiberLinearEquivOfMem 𝒜 hf d (hU x.2)).map_smul
        (AlgebraicGeometry.openToLocalization 𝒜 U x.1 x.2 r) (s.1 x) }

/-- Over `D₊(f)`, a nonnegative twist is additively equivalent to the structure module when
`f` has degree one. -/
noncomputable def natShiftSectionAddEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℕ) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)) ≃+
      (associatedSheafInType 𝒜 𝒜).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  natShiftSectionAddEquivOn 𝒜 hf d le_rfl

/-- The chart trivialization is linear over the structure-sheaf sections on `D₊(f)`. -/
noncomputable def natShiftSectionLinearEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℕ) :
    (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)) ≃ₗ[
      𝒪.1.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f))]
      (associatedSheafInType 𝒜 𝒜).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  natShiftSectionLinearEquivOn 𝒜 hf d le_rfl

/-! ## The canonical basic-open map -/

/-- The algebraic chart trivialization, the structure-module comparison, and the sheaf chart
trivialization combine to identify the localized shift with its sections on `D₊(f)`. -/
noncomputable def natShiftBasicOpenSectionAddEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℕ) :
    DegreeZeroLocalization 𝒜 (natShift 𝒜 d) (.powers f) ≃+
      (associatedSheafInType 𝒜 (natShift 𝒜 d)).1.obj
        (op (ProjectiveSpectrum.basicOpen 𝒜 f)) :=
  (DegreeZeroLocalization.natShiftSelfLinearEquiv 𝒜 hf d).toAddEquiv |>.trans
    (selfBasicOpenSectionAddEquiv 𝒜 hf Nat.zero_lt_one) |>.trans
      (natShiftSectionAddEquiv 𝒜 hf d).symm

/-- The chart equivalence above is the canonical homogeneous-fraction section map. -/
theorem natShiftBasicOpenSectionAddEquiv_apply_mk {f : A} (hf : f ∈ 𝒜 1) (d : ℕ)
    (c : NumDenSameDeg 𝒜 (natShift 𝒜 d) (.powers f)) :
    natShiftBasicOpenSectionAddEquiv 𝒜 hf d (DegreeZeroLocalization.mk c) =
      moduleAwayToSection 𝒜 (natShift 𝒜 d) f (DegreeZeroLocalization.mk c) := by
  change natShiftSectionFromSelf 𝒜 hf d
    (selfBasicOpenSectionAddEquiv 𝒜 hf Nat.zero_lt_one
      (DegreeZeroLocalization.natShiftSelfLinearEquiv 𝒜 hf d
        (DegreeZeroLocalization.mk c))) = _
  rw [DegreeZeroLocalization.natShiftSelfLinearEquiv_apply_mk,
    selfBasicOpenSectionAddEquiv_apply_mk]
  apply section_ext
  funext x
  change (natShiftFiberLinearEquiv 𝒜 hf d x).symm
      ((moduleAwayToSection 𝒜 𝒜 f (DegreeZeroLocalization.mk _)).1 x) =
    (moduleAwayToSection 𝒜 (natShift 𝒜 d) f (DegreeZeroLocalization.mk c)).1 x
  rw [moduleAwayToSection_apply, moduleAwayToSection_apply,
    DegreeZeroLocalization.mapOfLE_mk, DegreeZeroLocalization.mapOfLE_mk]
  let x' : ProjectiveSpectrum.basicOpen 𝒜 f := ⟨x.1, x.2⟩
  change (DegreeZeroLocalization.natShiftLinearEquivOfMem 𝒜 hf d x'.2).symm
      (DegreeZeroLocalization.mk _) = DegreeZeroLocalization.mk _
  rw [DegreeZeroLocalization.natShiftLinearEquivOfMem_symm_apply_mk]
  apply DegreeZeroLocalization.ext
  simp only [DegreeZeroLocalization.coe_mk, NumDenSameDeg.embedding]
  rw [LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul]
  change (c.den : A) * ((c.num : A) * f ^ d) =
    ((c.den : A) * f ^ d) * (c.num : A)
  ac_rfl

/-- As an additive map, the constructed chart equivalence is exactly the canonical map from
homogeneous fractions to locally fractional sections. -/
theorem natShiftBasicOpenSectionAddEquiv_toAddMonoidHom {f : A}
    (hf : f ∈ 𝒜 1) (d : ℕ) :
    (natShiftBasicOpenSectionAddEquiv 𝒜 hf d).toAddMonoidHom =
      moduleAwayToSection 𝒜 (natShift 𝒜 d) f :=
  moduleAwayToSection_unique 𝒜 (natShift 𝒜 d) f _
    (natShiftBasicOpenSectionAddEquiv_apply_mk 𝒜 hf d)

/-- For a nonnegative twist, the canonical basic-open section map is bijective on every
degree-one chart. -/
theorem moduleAwayToSection_natShift_degreeOne_bijective {f : A}
    (hf : f ∈ 𝒜 1) (d : ℕ) :
    Function.Bijective (moduleAwayToSection 𝒜 (natShift 𝒜 d) f) := by
  rw [← moduleAwayToSection_unique 𝒜 (natShift 𝒜 d) f
    (natShiftBasicOpenSectionAddEquiv 𝒜 hf d).toAddMonoidHom
    (natShiftBasicOpenSectionAddEquiv_apply_mk 𝒜 hf d)]
  exact (natShiftBasicOpenSectionAddEquiv 𝒜 hf d).bijective

end AlgebraicGeometry.Proj
