/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.ForMathlib.AffineComparison
import CohLean.ForMathlib.QuasicoherentBasicOpen
import CohLean.AlgebraicGeometry.Modules.RestrictOver

/-!
# Gluing the affine comparison from a basic-open cover

This file proves the remaining quasi-coherent half of the affine comparison theorem. Its local
input is a presentation on each member of a basic-open cover; quasi-compactness supplies uniform
exponents, after which the sheaf condition glues the resulting sections.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open _root_.PrimeSpectrum

variable {R : CommRingCat.{u}}

/-- A localisation at the image of a submonoid remains a localisation at the original
submonoid after restricting scalars. -/
lemma IsLocalizedModule.restrictScalars_algebraMapSubmonoid
    {A : Type*} [CommSemiring A] [Algebra R A]
    {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] [Module A M] [Module A N]
    [IsScalarTower R A M] [IsScalarTower R A N]
    (S : Submonoid R) (l : M →ₗ[A] N)
    [h : IsLocalizedModule (Algebra.algebraMapSubmonoid A S) l] :
    IsLocalizedModule S (l.restrictScalars R) where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hs := h.map_units
      ⟨algebraMap R A s, ⟨s, s.2, rfl⟩⟩
    rw [Module.End.isUnit_iff] at hs
    simpa only [← IsScalarTower.algebraMap_apply] using hs
  surj y := by
    obtain ⟨⟨x, t⟩, ht⟩ := h.surj y
    obtain ⟨s, hs, hst⟩ := t.2
    refine ⟨⟨x, ⟨s, hs⟩⟩, ?_⟩
    change s • y = l x
    rw [← IsScalarTower.algebraMap_smul A s y, hst]
    exact ht
  exists_of_eq {x₁ x₂} hx := by
    obtain ⟨t, ht⟩ := h.exists_of_eq hx
    obtain ⟨s, hs, hst⟩ := t.2
    refine ⟨⟨s, hs⟩, ?_⟩
    change s • x₁ = s • x₂
    rw [← IsScalarTower.algebraMap_smul A s x₁,
      ← IsScalarTower.algebraMap_smul A s x₂, hst]
    exact ht

namespace Scheme.Modules

local instance (U : TopologicalSpace.Opens (Spec R)) : HasBinaryProducts (Over U) :=
  Over.ConstructProducts.over_binaryProduct_of_pullback

/-- The canonical open immersion `Spec R[1/g] ⟶ Spec R`. -/
noncomputable def basicOpenSpecMap (g : R) :
    Spec (.of (Localization.Away g)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))

instance (g : R) : IsOpenImmersion (basicOpenSpecMap g) :=
  Scheme.isOpenImmersion_SpecMap_localizationAway g

/-- The range of `Spec R[1/g] ⟶ Spec R` is `D(g)`. -/
lemma basicOpenSpecMap_opensRange (g : R) :
    (basicOpenSpecMap g).opensRange = PrimeSpectrum.basicOpen g := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (Localization.Away g) g

/-- The image of the top open under the canonical open immersion is `D(g)`. -/
private lemma basicOpenSpecMap_image_top (g : R) :
    basicOpenSpecMap g ''ᵁ ⊤ = PrimeSpectrum.basicOpen g := by
  rw [Scheme.Hom.image_top_eq_opensRange, basicOpenSpecMap_opensRange]

/-- Under `Spec R[1/g] ⟶ Spec R`, the basic open defined by the image of `f` has image
`D(gf) = D(g) ∩ D(f)`. -/
private lemma basicOpenSpecMap_image_basicOpen (g f : R) :
    basicOpenSpecMap g ''ᵁ
        PrimeSpectrum.basicOpen (algebraMap R (Localization.Away g) f) =
      PrimeSpectrum.basicOpen (g * f) := by
  change Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g))) ''ᵁ
      PrimeSpectrum.basicOpen ((CommRingCat.ofHom
        (algebraMap R (Localization.Away g))) f) = _
  rw [← AlgebraicGeometry.SpecMap_preimage_basicOpen]
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  have hrange :
      (Spec.map (CommRingCat.ofHom
        (algebraMap R (Localization.Away g)))).opensRange =
          PrimeSpectrum.basicOpen g := by
    simpa only [basicOpenSpecMap] using basicOpenSpecMap_opensRange (R := R) g
  rw [hrange]
  exact (PrimeSpectrum.basicOpen_mul g f).symm

/-- A presentation on the slice over `D(g)` transports to the corresponding module on
`Spec R[1/g]`. -/
private noncomputable def Presentation.restrictBasicOpen (M : (Spec R).Modules) (g : R)
    (P : (M.over (PrimeSpectrum.basicOpen g)).Presentation) :
    (M.restrict (basicOpenSpecMap g)).Presentation := by
  apply (basicOpenSpecMap g).restrictPresentation M
  rw [basicOpenSpecMap_opensRange]
  exact P

/-- Restriction of sections along an inclusion of opens, viewed as an `R`-linear map. -/
private noncomputable def restrictionLE (M : (Spec R).Modules) {U V : (Spec R).Opens}
    (hVU : V ≤ U) :
    (modulesSpecToSheaf.obj M).presheaf.obj (op U) ⟶
      (modulesSpecToSheaf.obj M).presheaf.obj (op V) :=
  (modulesSpecToSheaf.obj M).presheaf.map (homOfLE hVU).op

/-- Restricting along two nested inclusions is restriction along their composite. -/
private lemma restrictionLE_comp (M : (Spec R).Modules) {U V W : (Spec R).Opens}
    (hVU : V ≤ U) (hWV : W ≤ V) :
    M.restrictionLE hVU ≫ M.restrictionLE hWV =
      M.restrictionLE (hWV.trans hVU) := by
  dsimp only [restrictionLE]
  rw [← (modulesSpecToSheaf.obj M).presheaf.map_comp]
  congr 1

private lemma restrictionLE_comp_apply (M : (Spec R).Modules)
    {U V W : (Spec R).Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (x : (modulesSpecToSheaf.obj M).presheaf.obj (op U)) :
    (M.restrictionLE hWV).hom ((M.restrictionLE hVU).hom x) =
      (M.restrictionLE (hWV.trans hVU)).hom x := by
  have h := congrArg (fun q ↦ q.hom x) (M.restrictionLE_comp hVU hWV)
  simpa only [ConcreteCategory.comp_apply] using h

/-- `basicOpenRestriction` is the generic restriction from `⊤` to `D(f)`. -/
private lemma basicOpenRestriction_eq_restrictionLE (M : (Spec R).Modules) (f : R) :
    M.basicOpenRestriction f = M.restrictionLE
      (U := (⊤ : (Spec R).Opens)) (V := PrimeSpectrum.basicOpen f)
      (fun _ _ => trivial) := rfl

/-- Restriction from `D(g)` to `D(gf)`, viewed as an `R`-linear map. -/
noncomputable def basicOpenRestrictionOver (M : (Spec R).Modules) (g f : R) :
    (modulesSpecToSheaf.obj M).presheaf.obj
        (op (PrimeSpectrum.basicOpen g)) ⟶
      (modulesSpecToSheaf.obj M).presheaf.obj
        (op (PrimeSpectrum.basicOpen (g * f))) :=
  (modulesSpecToSheaf.obj M).presheaf.map
    (homOfLE ((PrimeSpectrum.basicOpen_mul g f).trans_le inf_le_left)).op

/-- `basicOpenRestrictionOver` is the generic restriction from `D(g)` to `D(gf)`. -/
private lemma basicOpenRestrictionOver_eq_restrictionLE (M : (Spec R).Modules) (g f : R) :
    M.basicOpenRestrictionOver g f =
      M.restrictionLE ((PrimeSpectrum.basicOpen_mul g f).trans_le inf_le_left) := rfl

/-- Restricting first to `D(g)` and then to `D(gf)` is the same as restricting first to
`D(f)` and then to `D(gf)`. -/
private lemma restrictionLE_basicOpen_comm (M : (Spec R).Modules) (g f : R) :
    M.restrictionLE
          (show PrimeSpectrum.basicOpen g ≤
              (⟨Set.univ, isOpen_univ⟩ : (Spec R).Opens) from fun _ _ ↦ trivial) ≫
        M.basicOpenRestrictionOver g f =
      M.basicOpenRestriction f ≫
        M.restrictionLE
          ((PrimeSpectrum.basicOpen_mul g f).trans_le inf_le_right) := by
  rw [basicOpenRestrictionOver_eq_restrictionLE,
    basicOpenRestriction_eq_restrictionLE, restrictionLE_comp, restrictionLE_comp]
  congr 1

/-- From a possibly infinite family generating the unit ideal, choose a finite reindexed
subfamily which still generates the unit ideal. -/
private lemma exists_finite_basicOpen_cover {I : Type u} (g : I → R)
    (hg : Ideal.span (Set.range g) = ⊤) :
    ∃ (J : Type u) (_ : Fintype J) (k : J → I),
      Ideal.span (Set.range (fun j ↦ g (k j))) = ⊤ ∧
        (⊤ : (Spec R).Opens) ≤
          ⨆ j, PrimeSpectrum.basicOpen (g (k j)) := by
  have h_one : (1 : R) ∈ Ideal.span (Set.range g) := by
    rw [hg]
    trivial
  obtain ⟨s : Finset R, hs, h_one_s⟩ :=
    Submodule.mem_span_finite_of_mem_span h_one
  let J := {r // r ∈ s}
  let k : J → I := fun r ↦ Classical.choose (hs r.property)
  have hk (r : J) : g (k r) = r := Classical.choose_spec (hs r.property)
  have hspan : Ideal.span (Set.range (fun j ↦ g (k j))) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    apply Ideal.span_mono _ h_one_s
    intro r hr
    exact ⟨⟨r, hr⟩, hk ⟨r, hr⟩⟩
  refine ⟨J, inferInstance, k, hspan, ?_⟩
  exact (PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hspan).ge

private lemma basicOpen_mul_mul_le_mul_left (a b f : R) :
    PrimeSpectrum.basicOpen ((a * b) * f) ≤ PrimeSpectrum.basicOpen (a * f) := by
  rw [PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_mul,
    PrimeSpectrum.basicOpen_mul]
  exact le_inf (inf_le_left.trans inf_le_left) inf_le_right

private lemma basicOpen_mul_mul_le_mul_right (a b f : R) :
    PrimeSpectrum.basicOpen ((a * b) * f) ≤ PrimeSpectrum.basicOpen (b * f) := by
  rw [PrimeSpectrum.basicOpen_mul, PrimeSpectrum.basicOpen_mul,
    PrimeSpectrum.basicOpen_mul]
  exact le_inf (inf_le_left.trans inf_le_right) inf_le_right

/-- The two restriction paths from `D(a)` to `D(abf)` agree. -/
private lemma restrictionLE_basicOpen_pair_left (M : (Spec R).Modules) (a b f : R) :
    M.restrictionLE
        ((PrimeSpectrum.basicOpen_mul a b).trans_le inf_le_left) ≫
      M.basicOpenRestrictionOver (a * b) f =
    M.basicOpenRestrictionOver a f ≫
      M.restrictionLE (basicOpen_mul_mul_le_mul_left a b f) := by
  rw [basicOpenRestrictionOver_eq_restrictionLE,
    basicOpenRestrictionOver_eq_restrictionLE, restrictionLE_comp, restrictionLE_comp]

/-- The two restriction paths from `D(b)` to `D(abf)` agree. -/
private lemma restrictionLE_basicOpen_pair_right (M : (Spec R).Modules) (a b f : R) :
    M.restrictionLE
        ((PrimeSpectrum.basicOpen_mul a b).trans_le inf_le_right) ≫
      M.basicOpenRestrictionOver (a * b) f =
    M.basicOpenRestrictionOver b f ≫
      M.restrictionLE (basicOpen_mul_mul_le_mul_right a b f) := by
  rw [basicOpenRestrictionOver_eq_restrictionLE,
    basicOpenRestrictionOver_eq_restrictionLE, restrictionLE_comp, restrictionLE_comp]

private lemma restrictBasicOpen_smul (M : (Spec R).Modules) (g : R)
    (U : (Spec (.of (Localization.Away g))).Opens) (r : R)
    (x : (modulesSpecToSheaf.obj (M.restrict (basicOpenSpecMap g))).presheaf.obj (op U)) :
    (algebraMap R (Localization.Away g) r) • x =
      r • (show (modulesSpecToSheaf.obj M).presheaf.obj
        (op (basicOpenSpecMap g ''ᵁ U)) from x) := by
  letI : OrderTop (Spec (CommRingCat.of (Localization.Away g))).Opens :=
    (@CompleteLattice.toBoundedOrder _
      (inferInstance : CompleteLattice
        (Spec (CommRingCat.of (Localization.Away g))).Opens)).toOrderTop
  letI : OrderTop (Spec R).Opens :=
    (@CompleteLattice.toBoundedOrder _
      (inferInstance : CompleteLattice (Spec R).Opens)).toOrderTop
  change
    ((Spec (CommRingCat.of (Localization.Away g))).presheaf.map
      ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op U))
      ((StructureSheaf.globalSectionsIso
        (CommRingCat.of (Localization.Away g))).hom.hom
        (algebraMap R (Localization.Away g) r))) •
          (show Γ(M.restrict (basicOpenSpecMap g), U) from x) =
      ((Spec R).presheaf.map
        ((Limits.initialOpOfTerminal Limits.isTerminalTop).to
          (op (basicOpenSpecMap g ''ᵁ U)))
        ((StructureSheaf.globalSectionsIso R).hom.hom r)) •
          (show Γ(M, basicOpenSpecMap g ''ᵁ U) from x)
  change
    ((basicOpenSpecMap g).appIso U).inv.hom
      ((Spec (CommRingCat.of (Localization.Away g))).presheaf.map
        ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op U))
        ((StructureSheaf.globalSectionsIso
          (CommRingCat.of (Localization.Away g))).hom.hom
            (algebraMap R (Localization.Away g) r))) •
        (show Γ(M, basicOpenSpecMap g ''ᵁ U) from x) =
      ((Spec R).presheaf.map
        ((Limits.initialOpOfTerminal Limits.isTerminalTop).to
          (op (basicOpenSpecMap g ''ᵁ U)))
        ((StructureSheaf.globalSectionsIso R).hom.hom r)) •
        (show Γ(M, basicOpenSpecMap g ''ᵁ U) from x)
  congr 1
  rw [← ConcreteCategory.comp_apply, Scheme.Hom.appIso_inv_naturality]
  let φ : R ⟶ CommRingCat.of (Localization.Away g) :=
    CommRingCat.ofHom (algebraMap R (Localization.Away g))
  have hr :
      (StructureSheaf.globalSectionsIso
          (CommRingCat.of (Localization.Away g))).hom.hom
          (algebraMap R (Localization.Away g) r) =
        (basicOpenSpecMap g).appTop.hom
          ((StructureSheaf.globalSectionsIso R).hom.hom r) := by
    change (ΓSpecIso (CommRingCat.of (Localization.Away g))).inv.hom (φ r) =
      (Spec.map φ).appTop.hom ((ΓSpecIso R).inv.hom r)
    exact congrArg (fun k : R ⟶ Γ(Spec (CommRingCat.of (Localization.Away g)), ⊤) =>
      k.hom r) (ΓSpecIso_inv_naturality φ)
  rw [hr]
  rw [← ConcreteCategory.comp_apply]
  congr 1
  have happ := (basicOpenSpecMap g).app_appIso_inv (⊤ : (Spec R).Opens)
  have happ' :
      (basicOpenSpecMap g).appTop ≫ ((basicOpenSpecMap g).appIso ⊤).inv =
        (Spec R).presheaf.map
          (homOfLE (show basicOpenSpecMap g ''ᵁ (⊤ :
            (Spec (CommRingCat.of (Localization.Away g))).Opens) ≤
              (⊤ : (Spec R).Opens) from le_top)).op := by
    simpa using happ
  let k := (Spec R).presheaf.map
    ((basicOpenSpecMap g).opensFunctor.op.map
      ((Limits.initialOpOfTerminal Limits.isTerminalTop).to (op U)))
  have hcomp :
      (basicOpenSpecMap g).appTop ≫
          ((basicOpenSpecMap g).appIso ⊤).inv ≫ k =
        ((basicOpenSpecMap g).appTop ≫
          ((basicOpenSpecMap g).appIso ⊤).inv) ≫ k :=
    (Category.assoc _ _ _).symm
  dsimp only [k] at hcomp
  refine (congrArg ConcreteCategory.hom hcomp).trans ?_
  rw [happ']
  apply congrArg ConcreteCategory.hom
  exact ((Spec R).presheaf.map_comp _ _).symm.trans
    (congrArg (Spec R).presheaf.map (Subsingleton.elim _ _))

/-- Identify sections of the restriction to `Spec R[1/g]` over its top open with sections of
the original sheaf over `D(g)`, after restricting scalars to `R`. -/
noncomputable def restrictBasicOpenTopLinearEquiv (M : (Spec R).Modules) (g : R) :
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away g))).obj
        ((modulesSpecToSheaf.obj
          (M.restrict (basicOpenSpecMap g))).presheaf.obj (op ⊤)) ≃ₗ[R]
      (modulesSpecToSheaf.obj M).presheaf.obj
        (op (PrimeSpectrum.basicOpen g)) := by
  let e := ((modulesSpecToSheaf.obj M).presheaf.mapIso
    (eqToIso (basicOpenSpecMap_image_top (R := R) g)).op).symm
  refine
    { toFun := e.hom
      invFun := e.inv
      left_inv := fun x => Iso.hom_inv_id_apply e x
      right_inv := fun x => Iso.inv_hom_id_apply e x
      map_add' := fun x y => e.hom.hom.map_add x y
      map_smul' := ?_ }
  intro r x
  change e.hom.hom (algebraMap R (Localization.Away g) r • x) = _
  have hx : (algebraMap R (Localization.Away g) r) • x =
      r • (show (modulesSpecToSheaf.obj M).presheaf.obj
        (op (basicOpenSpecMap g ''ᵁ ⊤)) from x) :=
    restrictBasicOpen_smul M g ⊤ r x
  rw [hx]
  exact e.hom.hom.map_smul r _

/-- Identify sections over `D(f)` inside `Spec R[1/g]` with sections of the original sheaf
over `D(gf)`, after restricting scalars to `R`. -/
private noncomputable def restrictBasicOpenLinearEquiv (M : (Spec R).Modules) (g f : R) :
    (ModuleCat.restrictScalars (algebraMap R (Localization.Away g))).obj
        ((modulesSpecToSheaf.obj
          (M.restrict (basicOpenSpecMap g))).presheaf.obj
            (op (PrimeSpectrum.basicOpen
              (algebraMap R (Localization.Away g) f)))) ≃ₗ[R]
      (modulesSpecToSheaf.obj M).presheaf.obj
        (op (PrimeSpectrum.basicOpen (g * f))) := by
  let e := ((modulesSpecToSheaf.obj M).presheaf.mapIso
    (eqToIso (basicOpenSpecMap_image_basicOpen (R := R) g f)).op).symm
  refine
    { toFun := e.hom
      invFun := e.inv
      left_inv := fun x => Iso.hom_inv_id_apply e x
      right_inv := fun x => Iso.inv_hom_id_apply e x
      map_add' := fun x y => e.hom.hom.map_add x y
      map_smul' := ?_ }
  intro r x
  change e.hom.hom (algebraMap R (Localization.Away g) r • x) = _
  have hx : (algebraMap R (Localization.Away g) r) • x =
      r • (show (modulesSpecToSheaf.obj M).presheaf.obj
        (op (basicOpenSpecMap g ''ᵁ PrimeSpectrum.basicOpen
          (algebraMap R (Localization.Away g) f))) from x) :=
    restrictBasicOpen_smul M g
      (PrimeSpectrum.basicOpen (algebraMap R (Localization.Away g) f)) r x
  rw [hx]
  exact e.hom.hom.map_smul r _

/-- A presentation on `D(g)` makes restriction from `D(g)` to `D(gf)` a localisation at `f`.
This is the local exponent input used twice in the gluing argument. -/
theorem isLocalizedModule_basicOpenRestrictionOver_of_presentation
    (M : (Spec R).Modules) (g : R)
    (P : (M.over (PrimeSpectrum.basicOpen g)).Presentation) (f : R) :
    IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestrictionOver g f).hom := by
  let A := Localization.Away g
  let N := M.restrict (basicOpenSpecMap g)
  let q : A := algebraMap R A f
  let L₀ := (modulesSpecToSheaf.obj N).presheaf.obj (op ⊤)
  let L₁ := (modulesSpecToSheaf.obj N).presheaf.obj
    (op (PrimeSpectrum.basicOpen q))
  let L₀R := (ModuleCat.restrictScalars (algebraMap R A)).obj L₀
  let L₁R := (ModuleCat.restrictScalars (algebraMap R A)).obj L₁
  let l : L₀R →ₗ[A] L₁R := (N.basicOpenRestriction q).hom
  letI : IsScalarTower R A L₀R :=
    .of_algebraMap_smul fun _ _ => rfl
  letI : IsScalarTower R A L₁R :=
    .of_algebraMap_smul fun _ _ => rfl
  haveI hq : IsLocalizedModule (Submonoid.powers q) l := by
    dsimp only [l, N, q]
    exact N.isLocalizedModule_basicOpenRestriction_of_presentation
      (Presentation.restrictBasicOpen M g P) q
  haveI hq' : IsLocalizedModule
      (Algebra.algebraMapSubmonoid A (Submonoid.powers f)) l := by
    rw [Algebra.algebraMapSubmonoid_powers]
    exact hq
  haveI hres : IsLocalizedModule (Submonoid.powers f) (l.restrictScalars R) :=
    IsLocalizedModule.restrictScalars_algebraMapSubmonoid (Submonoid.powers f) l
  let e₀ : L₀R ≃ₗ[R]
      (modulesSpecToSheaf.obj M).presheaf.obj
        (op (PrimeSpectrum.basicOpen g)) :=
    M.restrictBasicOpenTopLinearEquiv g
  let e₁ : L₁R ≃ₗ[R]
      (modulesSpecToSheaf.obj M).presheaf.obj
        (op (PrimeSpectrum.basicOpen (g * f))) :=
    M.restrictBasicOpenLinearEquiv g f
  haveI hcod : IsLocalizedModule (Submonoid.powers f)
      (e₁.toLinearMap ∘ₗ l.restrictScalars R) :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers f) (l.restrictScalars R) e₁
  have hdom := IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
    (e₁.toLinearMap ∘ₗ l.restrictScalars R) e₀.symm
  convert hdom using 1
  apply LinearMap.ext
  intro x
  change (M.basicOpenRestrictionOver g f).hom x = e₁ (l (e₀.symm x))
  let F := (modulesSpecToSheaf.obj M).presheaf
  let a : op (PrimeSpectrum.basicOpen g) ⟶
      op (PrimeSpectrum.basicOpen (g * f)) :=
    (homOfLE ((PrimeSpectrum.basicOpen_mul g f).trans_le inf_le_left)).op
  let d : op (PrimeSpectrum.basicOpen g) ⟶
      op (basicOpenSpecMap g ''ᵁ ⊤) :=
    ((eqToIso (basicOpenSpecMap_image_top (R := R) g)).op).hom
  let b : op (basicOpenSpecMap g ''ᵁ ⊤) ⟶
      op (basicOpenSpecMap g ''ᵁ PrimeSpectrum.basicOpen q) :=
    (basicOpenSpecMap g).opensFunctor.op.map
      (homOfLE (fun _ _ => trivial)).op
  let c : op (basicOpenSpecMap g ''ᵁ PrimeSpectrum.basicOpen q) ⟶
      op (PrimeSpectrum.basicOpen (g * f)) :=
    ((eqToIso (basicOpenSpecMap_image_basicOpen (R := R) g f)).op).inv
  have ha : (M.basicOpenRestrictionOver g f).hom x = F.map a x := rfl
  have hd : e₀.symm x = F.map d x := rfl
  have hl (y : L₀R) : l y = F.map b y := by rfl
  have hc (y : L₁R) : e₁ y = F.map c y := by rfl
  have hmaps : (F.map d ≫ F.map b) ≫ F.map c = F.map a := by
    calc
      (F.map d ≫ F.map b) ≫ F.map c = F.map (d ≫ b) ≫ F.map c := by
        exact congrArg (fun k => k ≫ F.map c) (F.map_comp d b).symm
      _ = F.map ((d ≫ b) ≫ c) := (F.map_comp (d ≫ b) c).symm
      _ = F.map a := congrArg F.map (Subsingleton.elim _ _)
  have hmapx : F.map a x = F.map c (F.map b (F.map d x)) := by
    simpa only [ConcreteCategory.comp_apply] using
      congrArg (fun k : F.obj (op (PrimeSpectrum.basicOpen g)) ⟶
        F.obj (op (PrimeSpectrum.basicOpen (g * f))) => k.hom x) hmaps.symm
  have htransport : F.map c (F.map b (F.map d x)) = e₁ (l (e₀.symm x)) := by
    symm
    calc
      e₁ (l (e₀.symm x)) = F.map c (l (e₀.symm x)) := hc _
      _ = F.map c (F.map b (e₀.symm x)) := congrArg _ (hl _)
      _ = F.map c (F.map b (F.map d x)) :=
        congrArg (fun z => F.map c (F.map b z)) hd
  exact ha.trans (hmapx.trans htransport)

/-- If two global sections agree on `D(f)`, then a single power of `f` makes them equal.
The exponent is chosen uniformly from a finite basic-open subcover. -/
theorem exists_power_smul_eq_of_basicOpenRestriction_eq_of_cover
    (M : (Spec R).Modules) {I : Type u} (g : I → R)
    (hg : Ideal.span (Set.range g) = ⊤)
    (hP : ∀ i, Nonempty ((M.over (PrimeSpectrum.basicOpen (g i))).Presentation))
    (f : R)
    {x₁ x₂ : (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)}
    (hx : (M.basicOpenRestriction f).hom x₁ =
      (M.basicOpenRestriction f).hom x₂) :
    ∃ n : ℕ, f ^ n • x₁ = f ^ n • x₂ := by
  classical
  obtain ⟨J, hJ, k, hspan, hcover⟩ := exists_finite_basicOpen_cover g hg
  letI : Fintype J := hJ
  let r (j : J) := M.restrictionLE
    (show PrimeSpectrum.basicOpen (g (k j)) ≤
      (⟨Set.univ, isOpen_univ⟩ : (Spec R).Opens) from fun _ _ ↦ trivial)
  have hpath (j : J) (x : (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)) :
      (M.basicOpenRestrictionOver (g (k j)) f).hom ((r j).hom x) =
        (M.restrictionLE
          ((PrimeSpectrum.basicOpen_mul (g (k j)) f).trans_le inf_le_right)).hom
          ((M.basicOpenRestriction f).hom x) := by
    have h := congrArg (fun q ↦ q.hom x)
      (M.restrictionLE_basicOpen_comm (g (k j)) f)
    simpa only [ConcreteCategory.comp_apply] using h
  have hlocal_eq (j : J) :
      (M.basicOpenRestrictionOver (g (k j)) f).hom ((r j).hom x₁) =
        (M.basicOpenRestrictionOver (g (k j)) f).hom ((r j).hom x₂) := by
    rw [hpath j x₁, hpath j x₂, hx]
  have hexp (j : J) : ∃ n : ℕ,
      f ^ n • (r j).hom x₁ = f ^ n • (r j).hom x₂ := by
    let P := Classical.choice (hP (k j))
    let hloc := M.isLocalizedModule_basicOpenRestrictionOver_of_presentation
      (g (k j)) P f
    obtain ⟨s, hs⟩ := hloc.exists_of_eq (hlocal_eq j)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s.1 f).mp s.2
    refine ⟨n, ?_⟩
    simpa only [hn] using hs
  choose n hn using hexp
  let N := Finset.univ.sup n
  have hN (j : J) : f ^ N • (r j).hom x₁ = f ^ N • (r j).hom x₂ := by
    have hj : n j ≤ N := Finset.le_sup (s := Finset.univ) (f := n)
      (Finset.mem_univ j)
    have h := congrArg (fun z ↦ f ^ (N - n j) • z) (hn j)
    simpa only [← mul_smul, ← pow_add, Nat.sub_add_cancel hj] using h
  refine ⟨N, ?_⟩
  refine (modulesSpecToSheaf.obj M).eq_of_locally_eq'
    (fun j : J ↦ PrimeSpectrum.basicOpen (g (k j))) ⊤
    (fun _ ↦ homOfLE (fun _ _ ↦ trivial)) hcover _ _ ?_
  intro j
  change (r j).hom (f ^ N • x₁) = (r j).hom (f ^ N • x₂)
  exact ((r j).hom.map_smul (f ^ N) x₁).trans
    ((hN j).trans ((r j).hom.map_smul (f ^ N) x₂).symm)

/-- Local surjectivity on a finite basic-open cover, with one exponent valid on every member. -/
private theorem exists_uniform_basicOpen_lifts (M : (Spec R).Modules)
    {J : Type u} [Fintype J] (g : J → R)
    (hP : ∀ j, (M.over (PrimeSpectrum.basicOpen (g j))).Presentation)
    (f : R)
    (y : (modulesSpecToSheaf.obj M).presheaf.obj
      (op (PrimeSpectrum.basicOpen f))) :
    ∃ (N : ℕ)
      (x : ∀ j, (modulesSpecToSheaf.obj M).presheaf.obj
        (op (PrimeSpectrum.basicOpen (g j)))),
      ∀ j, (M.basicOpenRestrictionOver (g j) f).hom (x j) =
        f ^ N • (M.restrictionLE
          ((PrimeSpectrum.basicOpen_mul (g j) f).trans_le inf_le_right)).hom y := by
  classical
  have hexp (j : J) :
      ∃ (n : ℕ) (x : (modulesSpecToSheaf.obj M).presheaf.obj
        (op (PrimeSpectrum.basicOpen (g j)))),
        (M.basicOpenRestrictionOver (g j) f).hom x =
          f ^ n • (M.restrictionLE
            ((PrimeSpectrum.basicOpen_mul (g j) f).trans_le inf_le_right)).hom y := by
    let hloc := M.isLocalizedModule_basicOpenRestrictionOver_of_presentation
      (g j) (hP j) f
    obtain ⟨⟨x, s⟩, hs⟩ := hloc.surj
      ((M.restrictionLE
        ((PrimeSpectrum.basicOpen_mul (g j) f).trans_le inf_le_right)).hom y)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s.1 f).mp s.2
    refine ⟨n, x, ?_⟩
    simpa only [hn] using hs.symm
  choose n x hx using hexp
  let N := Finset.univ.sup n
  let x' (j : J) := f ^ (N - n j) • x j
  refine ⟨N, x', ?_⟩
  intro j
  have hj : n j ≤ N := Finset.le_sup (s := Finset.univ) (f := n)
    (Finset.mem_univ j)
  calc
    (M.basicOpenRestrictionOver (g j) f).hom (x' j) =
        f ^ (N - n j) •
          (M.basicOpenRestrictionOver (g j) f).hom (x j) :=
      (M.basicOpenRestrictionOver (g j) f).hom.map_smul _ _
    _ = f ^ (N - n j) •
        (f ^ n j • (M.restrictionLE
          ((PrimeSpectrum.basicOpen_mul (g j) f).trans_le inf_le_right)).hom y) :=
      congrArg _ (hx j)
    _ = f ^ N • (M.restrictionLE
        ((PrimeSpectrum.basicOpen_mul (g j) f).trans_le inf_le_right)).hom y := by
      rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hj]

/-- Uniform local lifts have equal images on every pairwise overlap after restricting once more
to `D(f)`. -/
private theorem basicOpen_pair_images_eq (M : (Spec R).Modules)
    {J : Type u} (g : J → R) (f : R) (N : ℕ)
    (y : (modulesSpecToSheaf.obj M).presheaf.obj
      (op (PrimeSpectrum.basicOpen f)))
    (x : ∀ j, (modulesSpecToSheaf.obj M).presheaf.obj
      (op (PrimeSpectrum.basicOpen (g j))))
    (hx : ∀ j, (M.basicOpenRestrictionOver (g j) f).hom (x j) =
      f ^ N • (M.restrictionLE
        ((PrimeSpectrum.basicOpen_mul (g j) f).trans_le inf_le_right)).hom y)
    (j k : J) :
    (M.basicOpenRestrictionOver (g j * g k) f).hom
        ((M.restrictionLE
          ((PrimeSpectrum.basicOpen_mul (g j) (g k)).trans_le inf_le_left)).hom (x j)) =
      (M.basicOpenRestrictionOver (g j * g k) f).hom
        ((M.restrictionLE
          ((PrimeSpectrum.basicOpen_mul (g j) (g k)).trans_le inf_le_right)).hom (x k)) := by
  let rjf := M.restrictionLE
    ((PrimeSpectrum.basicOpen_mul (g j) f).trans_le inf_le_right)
  let rkf := M.restrictionLE
    ((PrimeSpectrum.basicOpen_mul (g k) f).trans_le inf_le_right)
  let rjft := M.restrictionLE (basicOpen_mul_mul_le_mul_left (g j) (g k) f)
  let rkft := M.restrictionLE (basicOpen_mul_mul_le_mul_right (g j) (g k) f)
  let rt := M.restrictionLE
    ((PrimeSpectrum.basicOpen_mul (g j * g k) f).trans_le inf_le_right)
  have hleft := congrArg (fun q ↦ q.hom (x j))
    (M.restrictionLE_basicOpen_pair_left (g j) (g k) f)
  have hright := congrArg (fun q ↦ q.hom (x k))
    (M.restrictionLE_basicOpen_pair_right (g j) (g k) f)
  have hyj : rjft.hom (rjf.hom y) = rt.hom y := by
    simpa only [rjft, rjf, rt] using M.restrictionLE_comp_apply
      ((PrimeSpectrum.basicOpen_mul (g j) f).trans_le inf_le_right)
      (basicOpen_mul_mul_le_mul_left (g j) (g k) f) y
  have hyk : rkft.hom (rkf.hom y) = rt.hom y := by
    simpa only [rkft, rkf, rt] using M.restrictionLE_comp_apply
      ((PrimeSpectrum.basicOpen_mul (g k) f).trans_le inf_le_right)
      (basicOpen_mul_mul_le_mul_right (g j) (g k) f) y
  calc
    (M.basicOpenRestrictionOver (g j * g k) f).hom
        ((M.restrictionLE
          ((PrimeSpectrum.basicOpen_mul (g j) (g k)).trans_le inf_le_left)).hom (x j)) =
        rjft.hom ((M.basicOpenRestrictionOver (g j) f).hom (x j)) := by
      simpa only [ConcreteCategory.comp_apply, rjft] using hleft
    _ = rjft.hom (f ^ N • rjf.hom y) := congrArg _ (hx j)
    _ = f ^ N • rjft.hom (rjf.hom y) := rjft.hom.map_smul _ _
    _ = f ^ N • rt.hom y := congrArg _ hyj
    _ = f ^ N • rkft.hom (rkf.hom y) := congrArg _ hyk.symm
    _ = rkft.hom (f ^ N • rkf.hom y) := (rkft.hom.map_smul _ _).symm
    _ = rkft.hom ((M.basicOpenRestrictionOver (g k) f).hom (x k)) :=
      congrArg _ (hx k).symm
    _ = (M.basicOpenRestrictionOver (g j * g k) f).hom
        ((M.restrictionLE
          ((PrimeSpectrum.basicOpen_mul (g j) (g k)).trans_le inf_le_right)).hom (x k)) := by
      simpa only [ConcreteCategory.comp_apply, rkft] using hright.symm

/-- A second uniform exponent makes the normalized local lifts agree on every pairwise overlap. -/
private theorem exists_uniform_compatible_basicOpen_lifts (M : (Spec R).Modules)
    {J : Type u} [Fintype J] (g : J → R)
    (hP : ∀ j, (M.over (PrimeSpectrum.basicOpen (g j))).Presentation)
    (f : R) (N : ℕ)
    (y : (modulesSpecToSheaf.obj M).presheaf.obj
      (op (PrimeSpectrum.basicOpen f)))
    (x : ∀ j, (modulesSpecToSheaf.obj M).presheaf.obj
      (op (PrimeSpectrum.basicOpen (g j))))
    (hx : ∀ j, (M.basicOpenRestrictionOver (g j) f).hom (x j) =
      f ^ N • (M.restrictionLE
        ((PrimeSpectrum.basicOpen_mul (g j) f).trans_le inf_le_right)).hom y) :
    ∃ K : ℕ, ∀ j k,
      f ^ K • (M.restrictionLE
        ((PrimeSpectrum.basicOpen_mul (g j) (g k)).trans_le inf_le_left)).hom (x j) =
      f ^ K • (M.restrictionLE
        ((PrimeSpectrum.basicOpen_mul (g j) (g k)).trans_le inf_le_right)).hom (x k) := by
  classical
  have hexp (p : J × J) : ∃ n : ℕ,
      f ^ n • (M.restrictionLE
        ((PrimeSpectrum.basicOpen_mul (g p.1) (g p.2)).trans_le inf_le_left)).hom (x p.1) =
      f ^ n • (M.restrictionLE
        ((PrimeSpectrum.basicOpen_mul (g p.1) (g p.2)).trans_le inf_le_right)).hom (x p.2) := by
    let W : Over (PrimeSpectrum.basicOpen (g p.1)) := Over.mk
      (homOfLE ((PrimeSpectrum.basicOpen_mul (g p.1) (g p.2)).trans_le inf_le_left))
    let P : (M.over (PrimeSpectrum.basicOpen (g p.1 * g p.2))).Presentation :=
      (hP p.1).over W
    let hloc := M.isLocalizedModule_basicOpenRestrictionOver_of_presentation
      (g p.1 * g p.2) P f
    obtain ⟨s, hs⟩ := hloc.exists_of_eq
      (basicOpen_pair_images_eq M g f N y x hx p.1 p.2)
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s.1 f).mp s.2
    refine ⟨n, ?_⟩
    simpa only [hn] using hs
  choose n hn using hexp
  let K := Finset.univ.sup n
  refine ⟨K, ?_⟩
  intro j k
  have hp : n (j, k) ≤ K := Finset.le_sup (s := Finset.univ) (f := n)
    (Finset.mem_univ (j, k))
  have h := congrArg (fun z ↦ f ^ (K - n (j, k)) • z) (hn (j, k))
  simpa only [← mul_smul, ← pow_add, Nat.sub_add_cancel hp] using h

private theorem compatible_smul_basicOpen_lifts (M : (Spec R).Modules)
    {J : Type u} (g : J → R) (f : R) (K : ℕ)
    (x : ∀ j, (modulesSpecToSheaf.obj M).presheaf.obj
      (op (PrimeSpectrum.basicOpen (g j))))
    (h : ∀ j k,
      f ^ K • (M.restrictionLE
        ((PrimeSpectrum.basicOpen_mul (g j) (g k)).trans_le inf_le_left)).hom (x j) =
      f ^ K • (M.restrictionLE
        ((PrimeSpectrum.basicOpen_mul (g j) (g k)).trans_le inf_le_right)).hom (x k)) :
    TopCat.Presheaf.IsCompatible (modulesSpecToSheaf.obj M).presheaf
      (fun j ↦ PrimeSpectrum.basicOpen (g j)) (fun j ↦ f ^ K • x j) := by
  intro j k
  let hEq : PrimeSpectrum.basicOpen (g j) ⊓ PrimeSpectrum.basicOpen (g k) ≤
      PrimeSpectrum.basicOpen (g j * g k) :=
    le_of_eq (PrimeSpectrum.basicOpen_mul (g j) (g k)).symm
  let transport := M.restrictionLE hEq
  let rL := M.restrictionLE
    ((PrimeSpectrum.basicOpen_mul (g j) (g k)).trans_le inf_le_left)
  let rR := M.restrictionLE
    ((PrimeSpectrum.basicOpen_mul (g j) (g k)).trans_le inf_le_right)
  let dL := M.restrictionLE
    (inf_le_left : PrimeSpectrum.basicOpen (g j) ⊓
      PrimeSpectrum.basicOpen (g k) ≤ PrimeSpectrum.basicOpen (g j))
  let dR := M.restrictionLE
    (inf_le_right : PrimeSpectrum.basicOpen (g j) ⊓
      PrimeSpectrum.basicOpen (g k) ≤ PrimeSpectrum.basicOpen (g k))
  have hpathL (z : (modulesSpecToSheaf.obj M).presheaf.obj
      (op (PrimeSpectrum.basicOpen (g j)))) :
      transport.hom (rL.hom z) = dL.hom z := by
    simpa only [transport, rL, dL, hEq] using M.restrictionLE_comp_apply
      ((PrimeSpectrum.basicOpen_mul (g j) (g k)).trans_le inf_le_left) hEq z
  have hpathR (z : (modulesSpecToSheaf.obj M).presheaf.obj
      (op (PrimeSpectrum.basicOpen (g k)))) :
      transport.hom (rR.hom z) = dR.hom z := by
    simpa only [transport, rR, dR, hEq] using M.restrictionLE_comp_apply
      ((PrimeSpectrum.basicOpen_mul (g j) (g k)).trans_le inf_le_right) hEq z
  change dL.hom (f ^ K • x j) = dR.hom (f ^ K • x k)
  calc
    dL.hom (f ^ K • x j) = transport.hom (rL.hom (f ^ K • x j)) :=
      (hpathL _).symm
    _ = transport.hom (f ^ K • rL.hom (x j)) :=
      congrArg transport.hom (rL.hom.map_smul _ _)
    _ = transport.hom (f ^ K • rR.hom (x k)) := congrArg transport.hom (h j k)
    _ = transport.hom (rR.hom (f ^ K • x k)) :=
      congrArg transport.hom (rR.hom.map_smul _ _).symm
    _ = dR.hom (f ^ K • x k) := hpathR _

/-- A section over `D(f)` extends globally after multiplication by one power of `f`. -/
theorem exists_power_smul_eq_basicOpenRestriction_of_cover
    (M : (Spec R).Modules) {I : Type u} (g : I → R)
    (hg : Ideal.span (Set.range g) = ⊤)
    (hP : ∀ i, Nonempty ((M.over (PrimeSpectrum.basicOpen (g i))).Presentation))
    (f : R)
    (y : (modulesSpecToSheaf.obj M).presheaf.obj
      (op (PrimeSpectrum.basicOpen f))) :
    ∃ (n : ℕ) (x : (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)),
      f ^ n • y = (M.basicOpenRestriction f).hom x := by
  classical
  obtain ⟨J, hJ, k, hspan, hcover⟩ := exists_finite_basicOpen_cover g hg
  letI : Fintype J := hJ
  let g' : J → R := fun j ↦ g (k j)
  let P (j : J) : (M.over (PrimeSpectrum.basicOpen (g' j))).Presentation :=
    Classical.choice (hP (k j))
  obtain ⟨N, x, hx⟩ := exists_uniform_basicOpen_lifts M g' P f y
  obtain ⟨K, hK⟩ := exists_uniform_compatible_basicOpen_lifts M g' P f N y x hx
  let z (j : J) := f ^ K • x j
  have hz : TopCat.Presheaf.IsCompatible (modulesSpecToSheaf.obj M).presheaf
      (fun j ↦ PrimeSpectrum.basicOpen (g' j)) z :=
    compatible_smul_basicOpen_lifts M g' f K x hK
  obtain ⟨x₀, hx₀, _⟩ := (modulesSpecToSheaf.obj M).existsUnique_gluing'
    (fun j : J ↦ PrimeSpectrum.basicOpen (g' j)) ⊤
    (fun _ ↦ homOfLE (fun _ _ ↦ trivial)) (by simpa only [g'] using hcover) z hz
  have hcover_f : PrimeSpectrum.basicOpen f ≤
      ⨆ j : J, PrimeSpectrum.basicOpen (g' j * f) := by
    calc
      PrimeSpectrum.basicOpen f = ⊤ ⊓ PrimeSpectrum.basicOpen f := by simp
      _ ≤ (⨆ j : J, PrimeSpectrum.basicOpen (g' j)) ⊓
          PrimeSpectrum.basicOpen f := inf_le_inf_right _ (by simpa only [g'] using hcover)
      _ = ⨆ j : J, PrimeSpectrum.basicOpen (g' j) ⊓
          PrimeSpectrum.basicOpen f :=
        iSup_inf_eq (fun j : J ↦ PrimeSpectrum.basicOpen (g' j))
          (PrimeSpectrum.basicOpen f)
      _ = ⨆ j : J, PrimeSpectrum.basicOpen (g' j * f) := by
        simp_rw [PrimeSpectrum.basicOpen_mul]
  refine ⟨K + N, x₀, ?_⟩
  symm
  refine (modulesSpecToSheaf.obj M).eq_of_locally_eq'
    (fun j : J ↦ PrimeSpectrum.basicOpen (g' j * f))
    (PrimeSpectrum.basicOpen f)
    (fun j ↦ homOfLE
      ((PrimeSpectrum.basicOpen_mul (g' j) f).trans_le inf_le_right))
    hcover_f _ _ ?_
  intro j
  let rTop := M.restrictionLE
    (show PrimeSpectrum.basicOpen (g' j) ≤
      (⟨Set.univ, isOpen_univ⟩ : (Spec R).Opens) from fun _ _ ↦ trivial)
  let rf := M.restrictionLE
    ((PrimeSpectrum.basicOpen_mul (g' j) f).trans_le inf_le_right)
  have hpath := congrArg (fun q ↦ q.hom x₀)
    (M.restrictionLE_basicOpen_comm (g' j) f)
  have hx₀j : rTop.hom x₀ = z j := by
    simpa only [rTop, g'] using hx₀ j
  change rf.hom ((M.basicOpenRestriction f).hom x₀) = rf.hom (f ^ (K + N) • y)
  calc
    rf.hom ((M.basicOpenRestriction f).hom x₀) =
        (M.basicOpenRestrictionOver (g' j) f).hom (rTop.hom x₀) := by
      simpa only [ConcreteCategory.comp_apply, rf, rTop] using hpath.symm
    _ = (M.basicOpenRestrictionOver (g' j) f).hom (f ^ K • x j) :=
      congrArg _ hx₀j
    _ = f ^ K • (M.basicOpenRestrictionOver (g' j) f).hom (x j) :=
      (M.basicOpenRestrictionOver (g' j) f).hom.map_smul _ _
    _ = f ^ K • (f ^ N • rf.hom y) := congrArg _ (hx j)
    _ = f ^ (K + N) • rf.hom y := by rw [← mul_smul, ← pow_add]
    _ = rf.hom (f ^ (K + N) • y) := (rf.hom.map_smul _ _).symm

/-- Presentations on a basic-open cover make global restriction to every `D(f)` a localisation.

This is the Hartshorne II.5.1 gluing argument: the two finiteness clauses of
`IsLocalizedModule` are obtained by choosing uniform exponents on a finite subcover. -/
theorem isLocalizedModule_basicOpenRestriction_of_cover
    (M : (Spec R).Modules) {I : Type u} (g : I → R)
    (hg : Ideal.span (Set.range g) = ⊤)
    (hP : ∀ i, Nonempty ((M.over (PrimeSpectrum.basicOpen (g i))).Presentation))
    (f : R) :
    IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom where
  map_units s := by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff s.1 f).mp s.2
    rw [← hn, map_pow]
    exact (tilde.isUnit_algebraMap_end_basicOpen M f).pow n
  surj y := by
    obtain ⟨n, x, hx⟩ :=
      exists_power_smul_eq_basicOpenRestriction_of_cover M g hg hP f y
    exact ⟨⟨x, ⟨f ^ n, ⟨n, rfl⟩⟩⟩, hx⟩
  exists_of_eq {x₁ x₂} hx := by
    obtain ⟨n, hn⟩ :=
      exists_power_smul_eq_of_basicOpenRestriction_eq_of_cover M g hg hP f hx
    exact ⟨⟨f ^ n, ⟨n, rfl⟩⟩, hn⟩

/-- For a quasi-coherent sheaf on an affine scheme, restriction to every basic open is the
corresponding module localisation. -/
theorem isLocalizedModule_basicOpenRestriction_of_isQuasicoherent
    (M : (Spec R).Modules) [M.IsQuasicoherent] (f : R) :
    IsLocalizedModule (Submonoid.powers f) (M.basicOpenRestriction f).hom := by
  obtain ⟨I, g, hg, hP⟩ := M.exists_basicOpen_presentation_cover
  exact M.isLocalizedModule_basicOpenRestriction_of_cover g hg hP f

/-- Explicit quasi-coherent presentation data suffices for the affine comparison. This form is
useful when the data has just been transported across an equivalence and constructing a
typeclass witness would force Lean to normalize that transport repeatedly. -/
theorem isIso_fromTildeΓ_of_quasicoherentData
    (M : (Spec R).Modules) (q : SheafOfModules.QuasicoherentData.{u, u, u, u} M) :
    IsIso M.fromTildeΓ := by
  apply M.isIso_fromTildeΓ_iff_isLocalizedModule.mpr
  intro f
  obtain ⟨I, g, hg, hP⟩ :=
    M.exists_basicOpen_presentation_cover_of_quasicoherentData q
  exact M.isLocalizedModule_basicOpenRestriction_of_cover g hg hP f

/-- The affine comparison counit is an isomorphism for every quasi-coherent sheaf. -/
theorem isIso_fromTildeΓ_of_isQuasicoherent
    (M : (Spec R).Modules) [M.IsQuasicoherent] : IsIso M.fromTildeΓ :=
  let q := SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData (M := M).some
  M.isIso_fromTildeΓ_of_quasicoherentData q

end Scheme.Modules

end AlgebraicGeometry
