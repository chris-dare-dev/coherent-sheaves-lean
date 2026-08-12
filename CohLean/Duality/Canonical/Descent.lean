/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.Duality.Canonical.Differentials
import CohLean.Topology.Opens.CoversTop
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Fixed-rank descent for the relative cotangent sheaf

This file isolates the genuinely sheaf-theoretic step in issue #119.  A family of local
trivializations by the free sheaf on `Fin n` canonically produces the repository's
`FiniteLocallyFreeData`.  For a smooth morphism of pure relative dimension `n`, Mathlib supplies
a standard-smooth affine chart around every point.  Over the one-point scheme `Spec k`, the
chart is normalized to the exact base-field map used by `relativeDifferentialsPresheaf`; its
Kähler module then has a concrete `Fin n` basis and rank-one top exterior power.
The comparison is constructed by mapping the objectwise free presheaf into the Kähler
differential presheaf. Localization proves it is an isomorphism on the principal-open basis, so
sheafification makes it an isomorphism. Thus smoothness alone now supplies the global fixed-rank
cotangent atlas; no separate trivialization certificate remains.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

section FreeAppBasis

variable {U : X.Opens}

/-- Evaluation of a finite free sheaf is the ordinary finite free module. -/
noncomputable def freeAppIsoFinsupp (I : Type u) [Fintype I]
    (W : (Over U)ᵒᵖ) :
    (SheafOfModules.free (R := X.ringCatSheaf.over U) I).val.obj W ≅
      ModuleCat.of ((X.ringCatSheaf.over U).obj.obj W)
        (I →₀ (X.ringCatSheaf.over U).obj.obj W) := by
  letI : CommRing ((X.ringCatSheaf.over U).obj.obj W) :=
    inferInstanceAs (CommRing ((X.sheaf.over U).obj.obj W))
  let E := SheafOfModules.evaluation (X.ringCatSheaf.over U) W
  letI : E.Additive := by
    dsimp only [E, SheafOfModules.evaluation]
    infer_instance
  let hfree : IsColimit (E.mapCocone (SheafOfModules.freeCofan I)) :=
    isColimitOfPreserves E (SheafOfModules.isColimitFreeCofan I)
  exact IsColimit.coconePointUniqueUpToIso hfree
    (ModuleCat.finsuppCoconeIsColimit
      ((X.ringCatSheaf.over U).obj.obj W) ((X.ringCatSheaf.over U).obj.obj W) I)

@[simp]
theorem ιFree_app_freeAppIsoFinsupp_hom_apply_one (I : Type u) [Fintype I]
    (W : (Over U)ᵒᵖ) (i : I) :
    ((SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i).val.app W ≫
        (freeAppIsoFinsupp I W).hom)
      (show (SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj W from
        (1 : (X.ringCatSheaf.over U).obj.obj W)) = Finsupp.single i 1 := by
  letI : CommRing ((X.ringCatSheaf.over U).obj.obj W) :=
    inferInstanceAs (CommRing ((X.sheaf.over U).obj.obj W))
  let E := SheafOfModules.evaluation (X.ringCatSheaf.over U) W
  letI : E.Additive := by
    dsimp only [E, SheafOfModules.evaluation]
    infer_instance
  let hfree : IsColimit (E.mapCocone (SheafOfModules.freeCofan I)) :=
    isColimitOfPreserves E (SheafOfModules.isColimitFreeCofan I)
  change (((E.mapCocone (SheafOfModules.freeCofan I)).ι.app ⟨i⟩ ≫
      (hfree.coconePointUniqueUpToIso
        (ModuleCat.finsuppCoconeIsColimit
          ((X.ringCatSheaf.over U).obj.obj W)
          ((X.ringCatSheaf.over U).obj.obj W) I)).hom)
    (show ((Discrete.functor fun _ : I ↦
      SheafOfModules.unit (X.ringCatSheaf.over U)) ⋙ E).obj ⟨i⟩ from
        (1 : (X.ringCatSheaf.over U).obj.obj W))) = Finsupp.single i 1
  have hi := IsColimit.comp_coconePointUniqueUpToIso_hom hfree
    (ModuleCat.finsuppCoconeIsColimit
      ((X.ringCatSheaf.over U).obj.obj W)
      ((X.ringCatSheaf.over U).obj.obj W) I) ⟨i⟩
  have hi' := congrArg (fun q :
      ((Discrete.functor fun _ : I ↦
        SheafOfModules.unit (X.ringCatSheaf.over U)) ⋙ E).obj ⟨i⟩ ⟶
          ModuleCat.of ((X.ringCatSheaf.over U).obj.obj W)
            (I →₀ (X.ringCatSheaf.over U).obj.obj W) ↦
      q (show ((Discrete.functor fun _ : I ↦
        SheafOfModules.unit (X.ringCatSheaf.over U)) ⋙ E).obj ⟨i⟩ from
          (1 : (X.ringCatSheaf.over U).obj.obj W))) hi
  exact hi'.trans (by rfl)

/-- A basis of the sections of a module sheaf on one object identifies the corresponding
component of a finite free sheaf with those sections. -/
noncomputable def freeAppBasisIso (I : Type u) [Fintype I]
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) (W : (Over U)ᵒᵖ)
    (b : Module.Basis I ((X.ringCatSheaf.over U).obj.obj W) (M.val.obj W)) :
    (SheafOfModules.free (R := X.ringCatSheaf.over U) I).val.obj W ≅ M.val.obj W :=
  freeAppIsoFinsupp I W ≪≫ b.repr.symm.toModuleIso

/-- A map out of a finite free sheaf is an isomorphism on an object whenever the images of
the free generators form a basis there. -/
theorem isIso_app_free_of_basis (I : Type u) [Fintype I]
    (M : SheafOfModules.{u} (X.ringCatSheaf.over U)) (W : (Over U)ᵒᵖ)
    (f : SheafOfModules.free (R := X.ringCatSheaf.over U) I ⟶ M)
    (b : Module.Basis I ((X.ringCatSheaf.over U).obj.obj W) (M.val.obj W))
    (h : ∀ i, f.val.app W
      ((SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i).val.app W
        (show (SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj W from
          (1 : (X.ringCatSheaf.over U).obj.obj W))) = b i) :
    IsIso (f.val.app W) := by
  let E := SheafOfModules.evaluation (X.ringCatSheaf.over U) W
  letI : E.Additive := by
    dsimp only [E, SheafOfModules.evaluation]
    infer_instance
  let hfree : IsColimit (E.mapCocone (SheafOfModules.freeCofan I)) :=
    isColimitOfPreserves E (SheafOfModules.isColimitFreeCofan I)
  have hmap : f.val.app W = (freeAppBasisIso I M W b).hom := by
    apply hfree.hom_ext
    rintro ⟨i⟩
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    change f.val.app W
      ((SheafOfModules.ιFree (R := X.ringCatSheaf.over U) i).val.app W
        (show (SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj W from
          (1 : (X.ringCatSheaf.over U).obj.obj W))) = _
    rw [h i]
    change b i = b.repr.symm (((SheafOfModules.ιFree
      (R := X.ringCatSheaf.over U) i).val.app W ≫
        (freeAppIsoFinsupp I W).hom)
          (show (SheafOfModules.unit (X.ringCatSheaf.over U)).val.obj W from
            (1 : (X.ringCatSheaf.over U).obj.obj W)))
    rw [ιFree_app_freeAppIsoFinsupp_hom_apply_one]
    simp
  rw [hmap]
  infer_instance

end FreeAppBasis

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

/-- A principal open inside a smooth chart, regarded as an object of the slice site over the
chart. -/
noncomputable def cotangentBasicOpenObject {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x)
    (f : X.toScheme.presheaf.obj (.op C.source)) : Over C.source :=
  Over.mk (homOfLE (X.toScheme.basicOpen_le f))

private noncomputable abbrev cotangentOverPresheafFunctor {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) :=
  PresheafOfModules.pushforward
    (𝟙 (X.toScheme.ringCatSheaf.over C.source).obj)

/-- The objectwise Kähler-differential presheaf restricted to a smooth chart's slice site. -/
noncomputable def cotangentPresheafOver {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) :
    PresheafOfModules.{u} (X.toScheme.ringCatSheaf.over C.source).obj :=
  (cotangentOverPresheafFunctor (X := X) C).obj (relativeDifferentialsPresheaf X)

/-- The constant presheaf of the chart's `Fin n` basis indices. -/
private abbrev cotangentBasisIndexPresheaf {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) : (Over C.source)ᵒᵖ ⥤ Type u :=
  (Functor.const (Over C.source)ᵒᵖ).obj (ULift.{u} (Fin n))

/-- A chart-basis vector, restricted coherently to the entire slice site. -/
noncomputable def cotangentPresheafGeneratorSection {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) (i : ULift.{u} (Fin n)) :
    (cotangentPresheafOver X C).sections :=
  SheafOfModules.sectionOfInitial (cotangentPresheafOver X C)
    (.op (Over.mk (𝟙 C.source)))
    (initialOpOfTerminal Over.mkIdTerminal)
    (cotangentBasis X C i.down)

/-- Restrict each chart-basis vector from the chart to every object of its slice site. -/
noncomputable def cotangentPresheafGenerators {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) :
    cotangentBasisIndexPresheaf (X := X) C ⟶
      (cotangentPresheafOver X C).presheaf ⋙ forget _ where
  app W := ↾fun i ↦ (cotangentPresheafGeneratorSection X C i).eval W
  naturality W V g := by
    ext i
    change (cotangentPresheafGeneratorSection X C i).eval V =
      (cotangentPresheafOver X C).map g
        ((cotangentPresheafGeneratorSection X C i).eval W)
    exact (PresheafOfModules.sections_property
      (cotangentPresheafGeneratorSection X C i) g).symm

/-- The objectwise free presheaf maps to the restricted differential presheaf by the localized
chart basis. -/
noncomputable def cotangentPresheafMap {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) :
    PresheafOfModules.freeObj (R := (X.toScheme.ringCatSheaf.over C.source).obj)
        (cotangentBasisIndexPresheaf (X := X) C) ⟶
      cotangentPresheafOver X C :=
  PresheafOfModules.freeObjDesc (cotangentPresheafGenerators X C)

/-- On every principal open of a smooth affine chart, the free-presheaf comparison is the
linear isomorphism supplied by the localized Kähler basis. -/
theorem cotangentPresheafMap_app_basicOpen_isIso {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x)
    (f : X.toScheme.presheaf.obj (.op C.source)) :
    IsIso ((cotangentPresheafMap X C).app
      (.op (cotangentBasicOpenObject X C f))) := by
  let b := (cotangentBasicOpenBasis X C f).reindex
    (Equiv.ulift.{u, 0}.symm : Fin n ≃ ULift.{u} (Fin n))
  have hmap : (cotangentPresheafMap X C).app
      (.op (cotangentBasicOpenObject X C f)) =
      b.repr.symm.toModuleIso.hom := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext_ring
    change ModuleCat.freeDesc
        ((cotangentPresheafGenerators X C).app
          (.op (cotangentBasicOpenObject X C f))) (ModuleCat.freeMk i) =
      b.repr.symm (Finsupp.single i 1)
    rw [ModuleCat.freeDesc_apply]
    change (cotangentPresheafGeneratorSection X C i).eval
      (.op (cotangentBasicOpenObject X C f)) = b i
    change relativeDifferentialsBasicOpenRestriction X f
        (cotangentBasis X C i.down) = b i
    rw [show b i = cotangentBasicOpenBasis X C f i.down by
      simp [b, Module.Basis.reindex_apply]]
    simp [cotangentBasicOpenBasis]
  rw [hmap]
  infer_instance

/-- The chart comparison is a local equivalence: sheafification inverts it.  The proof checks
the comparison on the principal-open basis of the affine chart and uses the localized Kähler
bases above. -/
theorem cotangentPresheafMap_mem_W {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) :
    ((_root_.Opens.grothendieckTopology X.toScheme).over C.source).W
      ((PresheafOfModules.toPresheaf
        (X.toScheme.ringCatSheaf.over C.source).obj).map
          (cotangentPresheafMap X C)) := by
  letI : IsAffine (C.source : Scheme) := C.sourceAffine
  let B : Set (TopologicalSpace.Opens C.source) :=
    Set.range (fun f : X.toScheme.presheaf.obj (.op C.source) ↦
      C.source.toScheme.basicOpen (C.source.topIso.inv f))
  have hB : TopologicalSpace.Opens.IsBasis B := by
    have hBeq : B = Set.range (fun g : (C.source : Scheme).presheaf.obj (.op ⊤) ↦
        (C.source : Scheme).basicOpen g) := by
      ext V
      change (∃ f, C.source.toScheme.basicOpen (C.source.topIso.inv f) = V) ↔
        ∃ g, C.source.toScheme.basicOpen g = V
      constructor
      · rintro ⟨f, rfl⟩
        exact ⟨C.source.topIso.inv f, rfl⟩
      · rintro ⟨g, rfl⟩
        exact ⟨C.source.topIso.hom g, congrArg
          (C.source.toScheme.basicOpen)
            (Iso.hom_inv_id_apply (C := CommRingCat) C.source.topIso g)⟩
    rw [hBeq]
    exact isBasis_basicOpen (C.source : Scheme)
  apply TopCat.Presheaf.grothendieckTopology_over_W_of_isIso_app_of_isBasis
    (X := X.toScheme) hB
  intro V hV
  obtain ⟨f, rfl⟩ := hV
  let W₁ := C.source.overEquivalence.inverse.obj
    (C.source.toScheme.basicOpen (C.source.topIso.inv f))
  let W₂ := cotangentBasicOpenObject X C f
  let e : W₁ ≅ W₂ := Over.isoMk
    (eqToIso (C.source.ι_image_basicOpen_topIso_inv f))
  let α := ((PresheafOfModules.toPresheaf
    (X.toScheme.ringCatSheaf.over C.source).obj).map
      (cotangentPresheafMap X C))
  let F := (PresheafOfModules.toPresheaf
    (X.toScheme.ringCatSheaf.over C.source).obj).obj
      (PresheafOfModules.freeObj
        (cotangentBasisIndexPresheaf (X := X) C))
  haveI h₂ : IsIso (α.app (.op W₂)) := by
    dsimp only [α, W₂]
    haveI := cotangentPresheafMap_app_basicOpen_isIso X C f
    change IsIso ((forget₂ (ModuleCat _) AddCommGrpCat).map
      ((cotangentPresheafMap X C).app
        (.op (cotangentBasicOpenObject X C f))))
    infer_instance
  have hnat := α.naturality e.hom.op
  haveI hcomp : IsIso (F.map e.hom.op ≫ α.app (.op W₁)) := by
    rw [hnat]
    infer_instance
  change IsIso (α.app (.op W₁))
  exact IsIso.of_isIso_comp_left (F.map e.hom.op) (α.app (.op W₁))

/-- The tautological generator family in the finite free sheaf, viewed objectwise. -/
noncomputable def cotangentFreePresheafGenerators {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) :
    cotangentBasisIndexPresheaf (X := X) C ⟶
      (SheafOfModules.free
        (R := X.toScheme.ringCatSheaf.over C.source)
          (ULift.{u} (Fin n))).val.presheaf ⋙ forget _ where
  app W := ↾fun i ↦ (SheafOfModules.freeSection
    (R := X.toScheme.ringCatSheaf.over C.source) i).val W
  naturality W V g := by
    ext i
    change (SheafOfModules.freeSection
      (R := X.toScheme.ringCatSheaf.over C.source) i).val V =
        (SheafOfModules.free
          (R := X.toScheme.ringCatSheaf.over C.source)
            (ULift.{u} (Fin n))).val.map g
          ((SheafOfModules.freeSection
            (R := X.toScheme.ringCatSheaf.over C.source) i).val W)
    exact (PresheafOfModules.sections_property
      (SheafOfModules.freeSection
        (R := X.toScheme.ringCatSheaf.over C.source) i) g).symm

/-- The objectwise free presheaf maps canonically to the underlying presheaf of the finite free
sheaf. -/
noncomputable def cotangentFreePresheafComparison {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) :
    PresheafOfModules.freeObj (R := (X.toScheme.ringCatSheaf.over C.source).obj)
        (cotangentBasisIndexPresheaf (X := X) C) ⟶
      (SheafOfModules.free
        (R := X.toScheme.ringCatSheaf.over C.source)
          (ULift.{u} (Fin n))).val :=
  PresheafOfModules.freeObjDesc (cotangentFreePresheafGenerators X C)

/-- The objectwise-free comparison is an isomorphism on every object because the index type is
finite, so finite coproducts of the structure sheaf are computed objectwise. -/
theorem cotangentFreePresheafComparison_app_isIso {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) (W : (Over C.source)ᵒᵖ) :
    IsIso ((cotangentFreePresheafComparison X C).app W) := by
  let e := Scheme.Modules.freeAppIsoFinsupp
    (X := X.toScheme) (ULift.{u} (Fin n)) W
  have hmap : (cotangentFreePresheafComparison X C).app W = e.inv := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext_ring
    change ModuleCat.freeDesc
        ((cotangentFreePresheafGenerators X C).app W) (ModuleCat.freeMk i) =
      e.inv (Finsupp.single i 1)
    rw [ModuleCat.freeDesc_apply]
    change (SheafOfModules.freeSection
        (R := X.toScheme.ringCatSheaf.over C.source) i).val W =
      e.inv (Finsupp.single i 1)
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    rw [Iso.inv_hom_id_apply]
    change (((SheafOfModules.ιFree
      (R := X.toScheme.ringCatSheaf.over C.source) i).val.app W ≫ e.hom)
        (show (SheafOfModules.unit
          (X.toScheme.ringCatSheaf.over C.source)).val.obj W from
            (1 : (X.toScheme.ringCatSheaf.over C.source).obj.obj W))) =
      Finsupp.single i 1
    exact Scheme.Modules.ιFree_app_freeAppIsoFinsupp_hom_apply_one
      (X := X.toScheme) (ULift.{u} (Fin n)) W i
  rw [hmap]
  infer_instance

/-- Consequently, the comparison from the objectwise free presheaf is an isomorphism of
presheaves. -/
noncomputable def cotangentFreePresheafIso
    {n : ℕ} {x : X.toScheme} (C : SmoothChart X n x) :
    PresheafOfModules.freeObj (R := (X.toScheme.ringCatSheaf.over C.source).obj)
        (cotangentBasisIndexPresheaf (X := X) C) ≅
      (SheafOfModules.free
        (R := X.toScheme.ringCatSheaf.over C.source)
          (ULift.{u} (Fin n))).val :=
  PresheafOfModules.isoMk
    (fun W ↦ @asIso _ _ _ _
      ((cotangentFreePresheafComparison X C).app W)
        (cotangentFreePresheafComparison_app_isIso X C W))
    (by
      intro W V f
      simpa using (cotangentFreePresheafComparison X C).naturality f)

@[simp]
theorem cotangentFreePresheafIso_hom
    {n : ℕ} {x : X.toScheme} (C : SmoothChart X n x) :
    (cotangentFreePresheafIso X C).hom =
      cotangentFreePresheafComparison X C := by
  ext W
  simp [cotangentFreePresheafIso]

private noncomputable abbrev cotangentSheafification {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) :=
  PresheafOfModules.sheafification
    (𝟙 (X.toScheme.ringCatSheaf.over C.source).obj)

/-- Sheafifying the objectwise-free presheaf gives the finite free sheaf. -/
noncomputable def cotangentFreeSheafificationIso
    {n : ℕ} {x : X.toScheme} (C : SmoothChart X n x) :
    (cotangentSheafification (X := X) C).obj
        (PresheafOfModules.freeObj
          (cotangentBasisIndexPresheaf (X := X) C)) ≅
      SheafOfModules.free
        (R := X.toScheme.ringCatSheaf.over C.source)
          (ULift.{u} (Fin n)) :=
  (cotangentSheafification (X := X) C).mapIso (cotangentFreePresheafIso X C) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.toScheme.ringCatSheaf.over C.source).obj)).counit).app _

/-- Sheafification turns the principal-open local equivalence into an isomorphism. -/
theorem cotangentSheafificationMap_isIso
    {n : ℕ} {x : X.toScheme} (C : SmoothChart X n x) :
    IsIso ((cotangentSheafification (X := X) C).map (cotangentPresheafMap X C)) := by
  apply Localization.inverts (cotangentSheafification (X := X) C)
    (((_root_.Opens.grothendieckTopology X.toScheme).over C.source).W.inverseImage
      (PresheafOfModules.toPresheaf
        (X.toScheme.ringCatSheaf.over C.source).obj))
  exact cotangentPresheafMap_mem_W X C

/-- The canonical local trivialization of the cotangent sheaf on a standard-smooth chart. -/
noncomputable def cotangentFreeToDifferentialsIso
    {n : ℕ} {x : X.toScheme} (C : SmoothChart X n x) :
    SheafOfModules.free
        (R := X.toScheme.ringCatSheaf.over C.source)
          (ULift.{u} (Fin n)) ≅
      (relativeDifferentials X).over C.source :=
  (cotangentFreeSheafificationIso X C).symm ≪≫
    (@asIso _ _ _ _
      ((cotangentSheafification (X := X) C).map (cotangentPresheafMap X C))
        (cotangentSheafificationMap_isIso X C)) ≪≫
    @asIso _ _ _ _
      (Scheme.Modules.overSheafificationComparison
        (relativeDifferentialsPresheaf X) C.source)
      (Scheme.Modules.isIso_overSheafificationComparison _ _)

/-- On a standard-smooth chart, the constructed top exterior power of the cotangent sheaf is
the structure sheaf.  The comparison is obtained before sheafification from the determinant
coordinate of the localized `Fin n` basis. -/
noncomputable def cotangentTopExteriorOverTrivialization
    {n : ℕ} {x : X.toScheme} (C : SmoothChart X n x) :
    Scheme.Modules.exteriorPowerOver (relativeDifferentials X) C.source n ≅
      SheafOfModules.unit (X.toScheme.ringCatSheaf.over C.source) := by
  let A := (X.toScheme.sheaf.over C.source).obj
  let a := PresheafOfModules.sheafification
    (𝟙 (X.toScheme.ringCatSheaf.over C.source).obj)
  let eFree : PresheafOfModules.freeObj
        (R := (X.toScheme.ringCatSheaf.over C.source).obj)
        ((Functor.const (Over C.source)ᵒᵖ).obj (ULift.{u} (Fin n))) ≅
      (SheafOfModules.forget
        (X.toScheme.ringCatSheaf.over C.source)).obj
          (SheafOfModules.free (R := X.toScheme.ringCatSheaf.over C.source)
            (ULift.{u} (Fin n))) :=
    cotangentFreePresheafIso X C
  let e₁ := PresheafOfModules.exteriorPower.mapIso (A := A)
    ((SheafOfModules.forget
      (X.toScheme.ringCatSheaf.over C.source)).mapIso
        (cotangentFreeToDifferentialsIso X C).symm) n
  let e₂ := (PresheafOfModules.exteriorPower.mapIso (A := A) eFree n).symm
  let e₃ := PresheafOfModules.topExteriorFreeObjIso A n
  exact Iso.trans (a.mapIso (Iso.trans e₁ (Iso.trans e₂ e₃)))
    ((asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (X.toScheme.ringCatSheaf.over C.source).obj)).counit).app
        (SheafOfModules.unit (X.toScheme.ringCatSheaf.over C.source)))

/-- Restriction of the global top exterior cotangent sheaf is trivial on every
standard-smooth chart. -/
noncomputable def cotangentTopExteriorTrivialization
    {n : ℕ} {x : X.toScheme} (C : SmoothChart X n x) :
    (Scheme.Modules.exteriorPower (relativeDifferentials X) n).over C.source ≅
      SheafOfModules.unit (X.toScheme.ringCatSheaf.over C.source) :=
  Iso.trans
    (Scheme.Modules.exteriorPowerOverIso (relativeDifferentials X) C.source n)
    (cotangentTopExteriorOverTrivialization X C)

/-- The sheaf section on a chart obtained by sending a chosen Kähler basis vector through the
sheafification unit. -/
noncomputable def cotangentSection {n : ℕ} {x : X.toScheme}
    (C : SmoothChart X n x) (i : Fin n) :
    ((relativeDifferentials X).over C.source).sections :=
  SheafOfModules.overSection (relativeDifferentials X)
    ((relativeDifferentialsSheafification X).app (.op C.source)
      ((cotangentBasis X C) i))

/-- The canonical free-to-cotangent morphism on a smooth chart, generated by the sheafified
Kähler basis. -/
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

namespace SmoothCotangentDescent

variable {X} {n : ℕ} {h : SmoothOfRelativeDimension n X.structureMorphism}

/-- The canonical chart trivialization obtained from principal-open localization and
sheafification. -/
noncomputable def trivialization (x : X.toScheme) :
    SheafOfModules.free
        (R := X.toScheme.ringCatSheaf.over ((SmoothChart.ofSmooth X h x).source))
        (ULift.{u} (Fin n)) ≅
      (relativeDifferentials X).over ((SmoothChart.ofSmooth X h x).source) :=
  SmoothChart.cotangentFreeToDifferentialsIso X (SmoothChart.ofSmooth X h x)

/-- The source opens of the chosen smooth charts cover the variety. -/
theorem chartSources_coversTop :
    (_root_.Opens.grothendieckTopology X.toScheme).CoversTop
      (fun x : X.toScheme ↦ (SmoothChart.ofSmooth X h x).source) := by
  rw [_root_.Opens.coversTop_iff]
  apply top_unique
  intro x _hx
  exact Opens.mem_iSup.mpr
    ⟨x, (SmoothChart.ofSmooth X h x).mem_source⟩

/-- Package the smooth-chart comparisons as fixed-rank trivializations of `Ω¹_{X/k}`. -/
noncomputable def fixedRankTrivializations :
    Scheme.Modules.FixedRankTrivializations (relativeDifferentials X) n where
  I := X.toScheme
  chartOpen x := (SmoothChart.ofSmooth X h x).source
  coversTop := chartSources_coversTop (X := X) (h := h)
  trivialization := trivialization (X := X) (h := h)

/-- The chartwise sheafification comparisons globalize to fixed-rank locally-free cotangent
data. -/
noncomputable def finiteLocallyFree :
    Scheme.Modules.FiniteLocallyFreeData (relativeDifferentials X) n :=
  (fixedRankTrivializations (X := X) (h := h)).finiteLocallyFree

/-- The constructed relative cotangent sheaf is locally free on a smooth variety of pure relative
dimension `n`. -/
theorem relativeDifferentials_isLocallyFree
    (h : SmoothOfRelativeDimension n X.structureMorphism) :
    SheafOfModules.IsLocallyFree.{u, u, u}
      (show SheafOfModules X.toScheme.ringCatSheaf from relativeDifferentials X) :=
  (finiteLocallyFree (X := X) (h := h)).isLocallyFree

/-- The top exterior power of the cotangent sheaf is an invertible sheaf.  Its rank-one
trivializations are constructed on the same smooth-chart cover as the fixed-rank cotangent
atlas. -/
theorem topExteriorPower_isInvertible
    (h : SmoothOfRelativeDimension n X.structureMorphism) :
    SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.toScheme.ringCatSheaf from
        Scheme.Modules.exteriorPower (relativeDifferentials X) n) := by
  apply SheafOfModules.IsInvertible.of_trivializations
    (fun x : X.toScheme ↦ (SmoothChart.ofSmooth X h x).source)
    (chartSources_coversTop (X := X) (h := h))
  intro x
  exact (SmoothChart.cotangentTopExteriorTrivialization X
    (SmoothChart.ofSmooth X h x)).symm

end SmoothCotangentDescent

end Variety

end AlgebraicGeometry
