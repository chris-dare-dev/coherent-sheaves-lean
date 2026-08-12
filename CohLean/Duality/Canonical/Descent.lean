/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Duality.Canonical.Differentials
import CohLean.Topology.Opens.CoversTop

/-!
# Fixed-rank descent for the relative cotangent sheaf

This file isolates the genuinely sheaf-theoretic step in issue #119.  A family of local
trivializations by the free sheaf on `Fin n` canonically produces the repository's
`FiniteLocallyFreeData`.  For a smooth morphism of pure relative dimension `n`, Mathlib supplies
a standard-smooth affine chart around every point.  Over the one-point scheme `Spec k`, the
chart is normalized to the exact base-field map used by `relativeDifferentialsPresheaf`; its
Kähler module then has a concrete `Fin n` basis and rank-one top exterior power.
`SmoothCotangentTrivializations` records only the still-missing comparison which carries that
affine calculation through sheafification.

Thus the global fixed-rank conclusion below is a theorem from explicit local comparisons, not a
new existence axiom.  Constructing those comparisons from smoothness alone, and descending the
top exterior power with its transition determinants, remain the two upstream-facing parts of
#119.
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

/-- A cover on which a module sheaf is explicitly trivial of fixed rank `n`. -/
structure FixedRankTrivializations (E : X.Modules) (n : ℕ) where
  /-- Indexing type of the chosen cover. -/
  I : Type u
  /-- Opens in the trivializing cover. -/
  chartOpen : I → X.Opens
  /-- The chosen opens cover the scheme. -/
  coversTop : (_root_.Opens.grothendieckTopology X).CoversTop chartOpen
  /-- A rank-`n` free trivialization on every cover member. -/
  trivialization : ∀ i,
    SheafOfModules.free (R := X.ringCatSheaf.over (chartOpen i))
        (ULift.{u} (Fin n)) ≅
      E.over (chartOpen i)

namespace FixedRankTrivializations

variable {E : X.Modules} {n : ℕ}

/-- The local generating sections induced by the chosen free trivializations. -/
noncomputable def localGenerators (T : FixedRankTrivializations E n) :
    SheafOfModules.LocalGeneratorsData.{u}
      (show SheafOfModules X.ringCatSheaf from E) where
  I := T.I
  X := T.chartOpen
  coversTop := T.coversTop
  generators i :=
    { I := ULift.{u} (Fin n)
      s := (E.over (T.chartOpen i)).freeHomEquiv (T.trivialization i).hom
      epi := by
        rw [Equiv.symm_apply_apply]
        infer_instance }

/-- The induced local generators are bases rather than merely epimorphic generating families. -/
theorem localGenerators_isLocallyFreeData (T : FixedRankTrivializations E n) :
    T.localGenerators.IsLocallyFreeData := by
  constructor
  intro i
  change IsIso ((E.over (T.chartOpen i)).freeHomEquiv.symm
    ((E.over (T.chartOpen i)).freeHomEquiv (T.trivialization i).hom))
  rw [Equiv.symm_apply_apply]
  infer_instance

/-- Explicit rank-`n` trivializations produce fixed-rank locally-free data. -/
noncomputable def finiteLocallyFree (T : FixedRankTrivializations E n) :
    FiniteLocallyFreeData E n where
  localGenerators := T.localGenerators
  isLocallyFreeData := T.localGenerators_isLocallyFreeData
  rankEquiv _ := ⟨Equiv.ulift⟩

/-- In particular, an explicitly rank-`n`-trivialized sheaf is locally free. -/
theorem isLocallyFree (T : FixedRankTrivializations E n) :
    SheafOfModules.IsLocallyFree.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from E) :=
  T.finiteLocallyFree.isLocallyFree

end FixedRankTrivializations

end

end Scheme.Modules

namespace Variety

variable {k : Type u} [Field k] (X : Variety k)

/-- A standard-smooth affine chart of relative dimension `n` around a point. -/
structure SmoothChart (n : ℕ) (x : X.toScheme) where
  source : X.toScheme.Opens
  sourceAffine : IsAffineOpen source
  mem_source : x ∈ source
  standardSmooth :
    RingHom.IsStandardSmoothOfRelativeDimension n
      ((baseFieldToStructurePresheaf X).app (.op source)).hom

namespace SmoothChart

/-- The Kähler differential module on a chosen smooth chart has a concrete `Fin n` basis. -/
noncomputable def cotangentBasis {n : ℕ} {x : X.toScheme} (C : SmoothChart X n x) :
    Module.Basis (Fin n) (X.toScheme.presheaf.obj (.op C.source))
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app (.op C.source))) := by
  letI : Nonempty C.source := ⟨⟨x, C.mem_source⟩⟩
  exact relativeDifferentialsPresheaf_obj_basis X (.op C.source) n C.standardSmooth

/-- The chart basis localizes to a basis on every principal open inside the chart. -/
noncomputable def cotangentBasicOpenBasis {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x)
    (f : X.toScheme.presheaf.obj (.op C.source)) :
    Module.Basis (Fin n)
      (X.toScheme.presheaf.obj (.op (X.toScheme.basicOpen f)))
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app
          (.op (X.toScheme.basicOpen f)))) := by
  let e := (homOfLE (X.toScheme.basicOpen_le f)).op
  letI : Algebra (X.toScheme.presheaf.obj (.op C.source))
      (X.toScheme.presheaf.obj (.op (X.toScheme.basicOpen f))) :=
    (X.toScheme.presheaf.map e).hom.toAlgebra
  letI : IsLocalization.Away f
      (X.toScheme.presheaf.obj (.op (X.toScheme.basicOpen f))) :=
    C.sourceAffine.isLocalization_basicOpen f
  letI : Module (X.toScheme.presheaf.obj (.op C.source))
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app
          (.op (X.toScheme.basicOpen f)))) :=
    Module.compHom _ (X.toScheme.presheaf.map e).hom
  letI : IsScalarTower (X.toScheme.presheaf.obj (.op C.source))
      (X.toScheme.presheaf.obj (.op (X.toScheme.basicOpen f)))
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app
          (.op (X.toScheme.basicOpen f)))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : IsLocalizedModule (Submonoid.powers f)
      (relativeDifferentialsBasicOpenRestriction X f) :=
    relativeDifferentialsBasicOpenRestriction_isLocalizedModule
      X C.sourceAffine f
  exact C.cotangentBasis.ofIsLocalizedModule
    (X.toScheme.presheaf.obj (.op (X.toScheme.basicOpen f)))
      (Submonoid.powers f) (relativeDifferentialsBasicOpenRestriction X f)

/-- The sheaf section on a chart obtained by sending a chosen Kähler basis vector through the
sheafification unit. -/
noncomputable def cotangentSection {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) (i : Fin n) :
    ((relativeDifferentials X).over C.source).sections :=
  SheafOfModules.overSection (relativeDifferentials X)
    ((relativeDifferentialsSheafification X).app (.op C.source)
      ((cotangentBasis X C) i))

/-- The canonical free-to-cotangent morphism on a smooth chart, generated by the sheafified
Kähler basis.  Proving this map invertible is the remaining sheafification comparison. -/
noncomputable def cotangentFreeMap {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) :
    SheafOfModules.free (R := X.toScheme.ringCatSheaf.over C.source)
        (ULift.{u} (Fin n)) ⟶
      (relativeDifferentials X).over C.source :=
  ((relativeDifferentials X).over C.source).freeHomEquiv.symm
    (fun i ↦ cotangentSection X C i.down)

/-- The canonical chart morphism sends each free generator to the corresponding sheafified
Kähler basis vector. -/
@[simp]
theorem cotangentFreeMap_generator {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) (i : ULift.{u} (Fin n)) :
    ((relativeDifferentials X).over C.source).freeHomEquiv
      (cotangentFreeMap X C) i = cotangentSection X C i.down := by
  unfold cotangentFreeMap
  rw [Equiv.apply_symm_apply]

/-- The chart Kähler module is explicitly the standard free rank-`n` module. -/
noncomputable def cotangentLinearEquiv {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) :
    (Fin n → X.toScheme.presheaf.obj (.op C.source))
      ≃ₗ[X.toScheme.presheaf.obj (.op C.source)]
        CommRingCat.KaehlerDifferential
          ((baseFieldToStructurePresheaf X).app (.op C.source)) :=
  C.cotangentBasis.equivFun.symm

/-- The top exterior power of the chart's Kähler differential module is free of rank one. -/
noncomputable def cotangentTopExteriorPowerEquiv
    {n : ℕ} {x : X.toScheme} (C : SmoothChart X n x) :
    (⋀[X.toScheme.presheaf.obj (.op C.source)]^n
      (CommRingCat.KaehlerDifferential
        ((baseFieldToStructurePresheaf X).app (.op C.source))))
      ≃ₗ[X.toScheme.presheaf.obj (.op C.source)]
        X.toScheme.presheaf.obj (.op C.source) := by
  letI : Nonempty C.source := ⟨⟨x, C.mem_source⟩⟩
  exact relativeDifferentialsPresheaf_obj_topExteriorPowerEquiv
    X (.op C.source) n C.standardSmooth

/-- Choose the standard-smooth chart supplied at a point by smooth pure relative dimension. -/
noncomputable def ofSmooth {n : ℕ}
    (h : SmoothOfRelativeDimension n X.structureMorphism) (x : X.toScheme) :
    SmoothChart X n x :=
  Classical.choice (show Nonempty (SmoothChart X n x) from by
    obtain ⟨U, hU, V, hV, hx, e, hstd⟩ :=
      h.exists_isStandardSmoothOfRelativeDimension x
    have hUtop : U = ⊤ := by
      letI : Subsingleton (Spec (CommRingCat.of k)) := inferInstance
      ext y
      constructor
      · intro _
        trivial
      · intro _
        rw [Subsingleton.elim y (X.structureMorphism x)]
        exact e hx
    subst U
    have hbase : RingHom.IsStandardSmoothOfRelativeDimension 0
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
      RingHom.IsStandardSmoothOfRelativeDimension.equiv
        (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    have hcomp := hstd.comp hbase
    have hrelative : RingHom.IsStandardSmoothOfRelativeDimension n
        ((baseFieldToStructurePresheaf X).app (.op V)).hom := by
      change RingHom.IsStandardSmoothOfRelativeDimension n
        (((X.toScheme.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom.comp
          X.structureMorphism.appTop.hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
      simpa [Scheme.Hom.appLE, CommRingCat.hom_comp] using hcomp
    exact ⟨
      { source := V
        sourceAffine := hV
        mem_source := hx
        standardSmooth := hrelative }⟩)

end SmoothChart

/-- The missing sheafification comparison on the canonical standard-smooth chart cover.

The standard-smooth calculation and localization theorem construct a specific free-to-cotangent
map on every chosen chart. This structure asks precisely that those canonical maps are
isomorphisms; it cannot be populated by unrelated sheaf trivializations, and it does not ask
again for a global locally-free atlas or determinant line. -/
structure SmoothCotangentTrivializations {n : ℕ}
    (h : SmoothOfRelativeDimension n X.structureMorphism) where
  isIso_cotangentFreeMap : ∀ x : X.toScheme,
    IsIso (SmoothChart.cotangentFreeMap X (SmoothChart.ofSmooth X h x))

namespace SmoothCotangentTrivializations

variable {X} {n : ℕ} {h : SmoothOfRelativeDimension n X.structureMorphism}

/-- The canonical chart map, regarded as an isomorphism using the recorded sheafification
comparison. -/
noncomputable def trivialization (T : SmoothCotangentTrivializations X h)
    (x : X.toScheme) :
    SheafOfModules.free
        (R := X.toScheme.ringCatSheaf.over ((SmoothChart.ofSmooth X h x).source))
        (ULift.{u} (Fin n)) ≅
      (relativeDifferentials X).over ((SmoothChart.ofSmooth X h x).source) :=
  @asIso _ _ _ _
    (SmoothChart.cotangentFreeMap X (SmoothChart.ofSmooth X h x))
      (T.isIso_cotangentFreeMap x)

/-- The source opens of the chosen smooth charts cover the variety. -/
theorem chartSources_coversTop (_T : SmoothCotangentTrivializations X h) :
    (_root_.Opens.grothendieckTopology X.toScheme).CoversTop
      (fun x : X.toScheme ↦ (SmoothChart.ofSmooth X h x).source) := by
  rw [_root_.Opens.coversTop_iff]
  apply top_unique
  intro x _hx
  exact Opens.mem_iSup.mpr
    ⟨x, (SmoothChart.ofSmooth X h x).mem_source⟩

/-- Package the smooth-chart comparisons as fixed-rank trivializations of `Ω¹_{X/k}`. -/
noncomputable def fixedRankTrivializations (T : SmoothCotangentTrivializations X h) :
    Scheme.Modules.FixedRankTrivializations (relativeDifferentials X) n where
  I := X.toScheme
  chartOpen x := (SmoothChart.ofSmooth X h x).source
  coversTop := T.chartSources_coversTop
  trivialization := T.trivialization

/-- The chartwise sheafification comparisons globalize to fixed-rank locally-free cotangent
data. -/
noncomputable def finiteLocallyFree (T : SmoothCotangentTrivializations X h) :
    Scheme.Modules.FiniteLocallyFreeData (relativeDifferentials X) n :=
  T.fixedRankTrivializations.finiteLocallyFree

/-- The constructed relative cotangent sheaf is locally free once the chart comparisons are
supplied. -/
theorem relativeDifferentials_isLocallyFree (T : SmoothCotangentTrivializations X h) :
    SheafOfModules.IsLocallyFree.{u, u, u}
      (show SheafOfModules X.toScheme.ringCatSheaf from relativeDifferentials X) :=
  T.finiteLocallyFree.isLocallyFree

end SmoothCotangentTrivializations

end Variety

end AlgebraicGeometry
