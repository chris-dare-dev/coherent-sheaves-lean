/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.Foundation
import BridgelandStability.GrothendieckGroup.Basic
import BridgelandStability.Slicing.Defs
import BridgelandStability.StabilityCondition.Defs

/-!
# Compatibility with the vendored BridgelandStability API

This file is the explicit boundary between the repository-owned MIT API and
the temporarily retained Apache-2.0 vendor API. The conversions are lossless;
they allow downstream modules to migrate one layer at a time without making
the owner-authored foundation depend conceptually on vendor definitions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace BridgelandStabLean.Compatibility.BridgelandStability

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

namespace GrothendieckGroup

instance vendorOf_isTriangleAdditive :
    Foundation.IsTriangleAdditive (fun X => CategoryTheory.Triangulated.K₀.of C X) where
  additive T hT := CategoryTheory.Triangulated.K₀.of_triangle C T hT

/-- Convert an owner Grothendieck class to the retained vendor quotient. -/
def toVendor : Foundation.K₀ C →+ CategoryTheory.Triangulated.K₀ C :=
  Foundation.K₀.lift C (fun X => CategoryTheory.Triangulated.K₀.of C X)

@[simp]
theorem toVendor_of (X : C) :
    toVendor C (Foundation.K₀.of C X) = CategoryTheory.Triangulated.K₀.of C X :=
  Foundation.K₀.lift_of C _ X

instance ownerOf_isTriangleAdditive :
    CategoryTheory.Triangulated.IsTriangleAdditive (fun X => Foundation.K₀.of C X) where
  additive T hT := Foundation.K₀.of_triangle C T hT

/-- Convert a retained vendor Grothendieck class to the owner quotient. -/
def ofVendor : CategoryTheory.Triangulated.K₀ C →+ Foundation.K₀ C :=
  CategoryTheory.Triangulated.K₀.lift C (fun X => Foundation.K₀.of C X)

@[simp]
theorem ofVendor_of (X : C) :
    ofVendor C (CategoryTheory.Triangulated.K₀.of C X) = Foundation.K₀.of C X :=
  CategoryTheory.Triangulated.K₀.lift_of C _ X

@[simp]
theorem ofVendor_toVendor : (ofVendor C).comp (toVendor C) = AddMonoidHom.id (Foundation.K₀ C) := by
  apply Foundation.K₀.hom_ext C
  intro X
  simp

@[simp]
theorem toVendor_ofVendor : (toVendor C).comp (ofVendor C) =
    AddMonoidHom.id (CategoryTheory.Triangulated.K₀ C) := by
  apply CategoryTheory.Triangulated.K₀.hom_ext C
  intro X
  simp

/-- The owner and retained Grothendieck quotients are canonically additively
equivalent because they impose the same distinguished-triangle relations. -/
def equiv : Foundation.K₀ C ≃+ CategoryTheory.Triangulated.K₀ C where
  toFun := toVendor C
  invFun := ofVendor C
  left_inv x := by
    have h := DFunLike.congr_fun (ofVendor_toVendor C) x
    exact h
  right_inv x := by
    have h := DFunLike.congr_fun (toVendor_ofVendor C) x
    exact h
  map_add' x y := map_add (toVendor C) x y

end GrothendieckGroup

namespace PostnikovTower

/-- Convert an owner-authored Postnikov tower to the vendored representation. -/
def toVendor {E : C} (P : Foundation.PostnikovTower C E) :
    CategoryTheory.Triangulated.PostnikovTower C E where
  n := P.n
  chain := P.chain
  triangle := P.triangle
  triangle_dist := P.triangle_dist
  triangle_obj₁ := P.triangle_obj₁
  triangle_obj₂ := P.triangle_obj₂
  base_isZero := P.base_isZero
  top_iso := P.top_iso
  zero_isZero := P.zero_isZero

/-- Convert a vendored Postnikov tower to the owner-authored representation. -/
def ofVendor {E : C} (P : CategoryTheory.Triangulated.PostnikovTower C E) :
    Foundation.PostnikovTower C E where
  n := P.n
  chain := P.chain
  triangle := P.triangle
  triangle_dist := P.triangle_dist
  triangle_obj₁ := P.triangle_obj₁
  triangle_obj₂ := P.triangle_obj₂
  base_isZero := P.base_isZero
  top_iso := P.top_iso
  zero_isZero := P.zero_isZero

@[simp]
theorem ofVendor_toVendor {E : C} (P : Foundation.PostnikovTower C E) :
    ofVendor C (toVendor C P) = P := by
  cases P
  rfl

@[simp]
theorem toVendor_ofVendor {E : C} (P : CategoryTheory.Triangulated.PostnikovTower C E) :
    toVendor C (ofVendor C P) = P := by
  cases P
  rfl

end PostnikovTower

namespace HNFiltration

/-- Convert an owner-authored HN filtration to the vendored representation. -/
def toVendor {P : ℝ → ObjectProperty C} {E : C} (F : Foundation.HNFiltration C P E) :
    CategoryTheory.Triangulated.HNFiltration C P E where
  toPostnikovTower := PostnikovTower.toVendor C F.toPostnikovTower
  φ := F.φ
  hφ := F.hφ
  semistable := F.semistable

/-- Convert a vendored HN filtration to the owner-authored representation. -/
def ofVendor {P : ℝ → ObjectProperty C} {E : C}
    (F : CategoryTheory.Triangulated.HNFiltration C P E) : Foundation.HNFiltration C P E where
  toPostnikovTower := PostnikovTower.ofVendor C F.toPostnikovTower
  φ := F.φ
  hφ := F.hφ
  semistable := F.semistable

@[simp]
theorem ofVendor_toVendor {P : ℝ → ObjectProperty C} {E : C}
    (F : Foundation.HNFiltration C P E) : ofVendor C (toVendor C F) = F := by
  cases F
  rfl

@[simp]
theorem toVendor_ofVendor {P : ℝ → ObjectProperty C} {E : C}
    (F : CategoryTheory.Triangulated.HNFiltration C P E) : toVendor C (ofVendor C F) = F := by
  cases F
  rfl

end HNFiltration

namespace Slicing

/-- Convert an owner-authored slicing to the vendored representation. -/
def toVendor (s : Foundation.Slicing C) : CategoryTheory.Triangulated.Slicing C where
  P := s.P
  closedUnderIso := s.closedUnderIso
  zero_mem := s.zero_mem
  shift_iff := s.shift_iff
  hom_vanishing := s.hom_vanishing
  hn_exists E := Nonempty.map (HNFiltration.toVendor C) (s.hn_exists E)

/-- Convert a vendored slicing to the owner-authored representation. -/
def ofVendor (s : CategoryTheory.Triangulated.Slicing C) : Foundation.Slicing C where
  P := s.P
  closedUnderIso := s.closedUnderIso
  zero_mem := s.zero_mem
  shift_iff := s.shift_iff
  hom_vanishing := s.hom_vanishing
  hn_exists E := Nonempty.map (HNFiltration.ofVendor C) (s.hn_exists E)

@[simp]
theorem toVendor_P (s : Foundation.Slicing C) : (toVendor C s).P = s.P := rfl

@[simp]
theorem ofVendor_P (s : CategoryTheory.Triangulated.Slicing C) : (ofVendor C s).P = s.P := rfl

@[simp]
theorem ofVendor_toVendor (s : Foundation.Slicing C) : ofVendor C (toVendor C s) = s :=
  Foundation.Slicing.ext C rfl

@[simp]
theorem toVendor_ofVendor (s : CategoryTheory.Triangulated.Slicing C) : toVendor C (ofVendor C s) = s :=
  CategoryTheory.Triangulated.Slicing.ext C rfl

/-- Owner and retained thin-interval predicates agree under slicing
conversion. -/
theorem toVendor_intervalProp_iff (s : Foundation.Slicing C) (a b : ℝ) (E : C) :
    (toVendor C s).intervalProp C a b E ↔ s.intervalProp C a b E := by
  constructor
  · rintro (hE | ⟨F, hF⟩)
    · exact Or.inl hE
    · exact Or.inr ⟨HNFiltration.ofVendor C F, hF⟩
  · rintro (hE | ⟨F, hF⟩)
    · exact Or.inl hE
    · exact Or.inr ⟨HNFiltration.toVendor C F, hF⟩

/-- Owner and retained non-strict upper phase cuts agree. -/
theorem toVendor_leProp_iff (s : Foundation.Slicing C) (t : ℝ) (E : C) :
    (toVendor C s).leProp C t E ↔ s.leProp C t E := by
  constructor
  · rintro (hE | ⟨F, hF, hle⟩)
    · exact Or.inl hE
    · exact Or.inr ⟨HNFiltration.ofVendor C F, hF, hle⟩
  · rintro (hE | ⟨F, hF, hle⟩)
    · exact Or.inl hE
    · exact Or.inr ⟨HNFiltration.toVendor C F, hF, hle⟩

/-- Owner and retained strict lower phase cuts agree. -/
theorem toVendor_gtProp_iff (s : Foundation.Slicing C) (t : ℝ) (E : C) :
    (toVendor C s).gtProp C t E ↔ s.gtProp C t E := by
  constructor
  · rintro (hE | ⟨F, hF, hgt⟩)
    · exact Or.inl hE
    · exact Or.inr ⟨HNFiltration.ofVendor C F, hF, hgt⟩
  · rintro (hE | ⟨F, hF, hgt⟩)
    · exact Or.inl hE
    · exact Or.inr ⟨HNFiltration.toVendor C F, hF, hgt⟩

/-- Owner and retained strict upper phase cuts agree. -/
theorem toVendor_ltProp_iff (s : Foundation.Slicing C) (t : ℝ) (E : C) :
    (toVendor C s).ltProp C t E ↔ s.ltProp C t E := by
  constructor
  · rintro (hE | ⟨F, hF, hlt⟩)
    · exact Or.inl hE
    · exact Or.inr ⟨HNFiltration.ofVendor C F, hF, hlt⟩
  · rintro (hE | ⟨F, hF, hlt⟩)
    · exact Or.inl hE
    · exact Or.inr ⟨HNFiltration.toVendor C F, hF, hlt⟩

/-- Owner and retained non-strict lower phase cuts agree. -/
theorem toVendor_geProp_iff (s : Foundation.Slicing C) (t : ℝ) (E : C) :
    (toVendor C s).geProp C t E ↔ s.geProp C t E := by
  constructor
  · rintro (hE | ⟨F, hF, hge⟩)
    · exact Or.inl hE
    · exact Or.inr ⟨HNFiltration.ofVendor C F, hF, hge⟩
  · rintro (hE | ⟨F, hF, hge⟩)
    · exact Or.inl hE
    · exact Or.inr ⟨HNFiltration.toVendor C F, hF, hge⟩

/-- The owner and retained thin interval categories are canonically
equivalent: they have the same objects and morphisms after translating HN
filtration witnesses. -/
def intervalEquiv (s : Foundation.Slicing C) (a b : ℝ) :
    s.IntervalCat C a b ≌ (toVendor C s).IntervalCat C a b where
  functor := ObjectProperty.ιOfLE fun E hE =>
    (toVendor_intervalProp_iff C s a b E).2 hE
  inverse := ObjectProperty.ιOfLE fun E hE =>
    (toVendor_intervalProp_iff C s a b E).1 hE
  unitIso := NatIso.ofComponents
    (fun X => @ObjectProperty.isoMk C _ _ _ _ (Iso.refl X.obj))
    (fun f => by
      ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  counitIso := NatIso.ofComponents
    (fun X => @ObjectProperty.isoMk C _ _ _ _ (Iso.refl X.obj))
    (fun f => by
      ext
      change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
      simp)
  functor_unitIso_comp X := by
    ext
    change 𝟙 X.obj ≫ 𝟙 X.obj = 𝟙 X.obj
    simp

/-- Subobject lattices of corresponding owner and retained interval objects
are order-isomorphic. -/
def intervalSubobjectOrderIso (s : Foundation.Slicing C) (a b : ℝ)
    (E : s.IntervalCat C a b) :
    Subobject E ≃o Subobject ((intervalEquiv C s a b).functor.obj E) :=
  (Subobject.lowerEquivalence (MonoOver.congr E (intervalEquiv C s a b))).toOrderIso

theorem intervalSubobjectOrderIso_wellFoundedLT_iff (s : Foundation.Slicing C)
    (a b : ℝ) (E : s.IntervalCat C a b) :
    WellFoundedLT (Subobject E) ↔
      WellFoundedLT (Subobject ((intervalEquiv C s a b).functor.obj E)) := by
  constructor
  · intro h
    letI : WellFoundedLT (Subobject E) := h
    exact (intervalSubobjectOrderIso C s a b E).symm.toOrderEmbedding.wellFoundedLT
  · intro h
    letI : WellFoundedLT (Subobject ((intervalEquiv C s a b).functor.obj E)) := h
    exact (intervalSubobjectOrderIso C s a b E).toOrderEmbedding.wellFoundedLT

theorem intervalSubobjectOrderIso_wellFoundedGT_iff (s : Foundation.Slicing C)
    (a b : ℝ) (E : s.IntervalCat C a b) :
    WellFoundedGT (Subobject E) ↔
      WellFoundedGT (Subobject ((intervalEquiv C s a b).functor.obj E)) := by
  rw [← wellFoundedLT_dual_iff, ← wellFoundedLT_dual_iff]
  constructor
  · intro h
    letI : WellFoundedLT (Subobject E)ᵒᵈ := h
    exact ((intervalSubobjectOrderIso C s a b E).symm.dual).toOrderEmbedding.wellFoundedLT
  · intro h
    letI : WellFoundedLT
        (Subobject ((intervalEquiv C s a b).functor.obj E))ᵒᵈ := h
    exact ((intervalSubobjectOrderIso C s a b E).dual).toOrderEmbedding.wellFoundedLT

variable [IsTriangulated C]

private theorem map_isStrictMono_of_distinguished (s : Foundation.Slicing C)
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X E Q : s.IntervalCat C a b} (i : X ⟶ E) (q : E ⟶ Q)
    (δ : Q.obj ⟶ X.obj⟦(1 : ℤ)⟧)
    (hT : Triangle.mk i.hom q.hom δ ∈ distTriang C) :
    IsStrictMono ((intervalEquiv C s a b).functor.map i) := by
  let e := intervalEquiv C s a b
  let S : ShortComplex ((toVendor C s).IntervalCat C a b) :=
    ShortComplex.mk (e.functor.map i) (e.functor.map q) (by
      apply ((toVendor C s).intervalProp C a b).ι.map_injective
      exact comp_distTriang_mor_zero₁₂ _ hT)
  have hS : StrictShortExact S :=
    CategoryTheory.Triangulated.Slicing.IntervalCat.strictShortExact_of_distTriang
      C (toVendor C s) hT
  exact ⟨hS.shortExact.mono_f, hS.strict_f⟩

private theorem mk_arrow_isStrictMono {s : Foundation.Slicing C}
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X E : s.IntervalCat C a b} (i : X ⟶ E) [Mono i]
    (hi : IsStrictMono ((intervalEquiv C s a b).functor.map i)) :
    letI : Mono ((intervalEquiv C s a b).functor.map i) := hi.mono
    IsStrictMono (Subobject.mk ((intervalEquiv C s a b).functor.map i)).arrow := by
  let f := (intervalEquiv C s a b).functor.map i
  letI : Mono f := hi.mono
  let e := Subobject.underlyingIso f
  have he : IsStrictMono e.hom := isStrictMono_of_isIso
  have hcomp : IsStrictMono (e.hom ≫ f) :=
    CategoryTheory.Triangulated.Slicing.IntervalCat.comp_strictMono
      C (toVendor C s) e.hom f he hi
  have harr : e.hom ≫ f =
      (Subobject.mk ((intervalEquiv C s a b).functor.map i)).arrow :=
    Subobject.underlyingIso_hom_comp_eq_mk f
  rw [← harr]
  exact hcomp

theorem intervalSubobjectOrderIso_isStrict_of_isAdmissible
    (s : Foundation.Slicing C) {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    (E : s.IntervalCat C a b) (A : Subobject E)
    (hA : s.IsAdmissibleSubobject C A) :
    Subobject.IsStrict (intervalSubobjectOrderIso C s a b E A) := by
  rcases hA with ⟨X, Q, i, hi, q, hAi, δ, hT⟩
  subst A
  change IsStrictMono
    (intervalSubobjectOrderIso C s a b E (Subobject.mk i)).arrow
  exact mk_arrow_isStrictMono C i
    (map_isStrictMono_of_distinguished C s i q δ hT)

private theorem strictShortExact_of_isStrictMono {s : Foundation.Slicing C}
    {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    {X E : (toVendor C s).IntervalCat C a b} (i : X ⟶ E)
    (hi : IsStrictMono i) :
    StrictShortExact (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)) := by
  let S : ShortComplex ((toVendor C s).IntervalCat C a b) :=
    ShortComplex.mk i (cokernel.π i) (cokernel.condition i)
  let t := ((toVendor C s).phaseShift C a).toTStructure
  letI := t.hasHeartFullSubcategory
  letI : Abelian t.heart.FullSubcategory := t.heartFullSubcategoryAbelian
  let FL := CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart
    (C := C) (s := toVendor C s) a b (Fact.out : b - a ≤ 1)
  have hKerBase : IsLimit (KernelFork.ofι S.f S.zero) := by
    simpa [S, KernelFork.ofι] using hi.isLimitKernelFork
  have hEpi : Epi ((S.map FL).g) := by
    change Epi (FL.map (cokernel.π i))
    exact CategoryTheory.Triangulated.Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
      C (toVendor C s) (cokernel.π i) (isStrictEpi_cokernel i)
  have hKer : IsLimit (KernelFork.ofι ((S.map FL).f) (S.map FL).zero) :=
    isLimitForkMapOfIsLimit' FL S.zero hKerBase
  letI : (S.map FL).HasHomology :=
    ShortComplex.HasHomology.mk' (ShortComplex.HomologyData.ofAbelian (S := S.map FL))
  have hExact : (S.map FL).Exact :=
    ShortComplex.exact_of_f_is_kernel (S := S.map FL) hKer
  have hL : (S.map FL).ShortExact :=
    ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKer) hEpi
  obtain ⟨δ, hT⟩ :=
    CategoryTheory.Triangulated.Slicing.IntervalCat.exists_distTriang_of_shortExact_toLeftHeart
      C (toVendor C s) hL
  exact CategoryTheory.Triangulated.Slicing.IntervalCat.strictShortExact_of_distTriang
    C (toVendor C s) hT

theorem isAdmissible_of_intervalSubobjectOrderIso_isStrict
    (s : Foundation.Slicing C) {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    (E : s.IntervalCat C a b) (A : Subobject E)
    (hA : Subobject.IsStrict (intervalSubobjectOrderIso C s a b E A)) :
    s.IsAdmissibleSubobject C A := by
  let A' := intervalSubobjectOrderIso C s a b E A
  let i' := A'.arrow
  have hi' : IsStrictMono i' := hA
  letI : Mono i' := hi'.mono
  let S : ShortComplex ((toVendor C s).IntervalCat C a b) :=
    ShortComplex.mk i' (cokernel.π i') (cokernel.condition i')
  have hS : StrictShortExact S := strictShortExact_of_isStrictMono C i' hi'
  obtain ⟨δ', hT'⟩ :=
    CategoryTheory.Triangulated.Slicing.IntervalCat.exists_distTriang_of_strictShortExact
      C (toVendor C s) hS
  let X : s.IntervalCat C a b :=
    ⟨(Subobject.underlying.obj A').obj,
      (toVendor_intervalProp_iff C s a b _).1 (Subobject.underlying.obj A').property⟩
  let Q : s.IntervalCat C a b :=
    ⟨(cokernel i').obj,
      (toVendor_intervalProp_iff C s a b _).1 (cokernel i').property⟩
  let i : X ⟶ E := ⟨i'.hom⟩
  let q : E ⟶ Q := ⟨(cokernel.π i').hom⟩
  have hi : Mono i := by
    apply (intervalEquiv C s a b).functor.mono_of_mono_map
    change Mono i'
    exact hi'.mono
  refine ⟨X, Q, i, hi, q, ?_, δ', ?_⟩
  refine (intervalSubobjectOrderIso C s a b E).injective ?_
  change Subobject.mk i' = A'
  exact Subobject.mk_arrow A'
  change Triangle.mk i'.hom (cokernel.π i').hom δ' ∈ distTriang C
  exact hT'

/-- Under the canonical interval equivalence, owner-admissible subobjects are
exactly retained strict subobjects. -/
theorem intervalSubobjectOrderIso_isAdmissible_iff_isStrict
    (s : Foundation.Slicing C) {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    (E : s.IntervalCat C a b) (A : Subobject E) :
    s.IsAdmissibleSubobject C A ↔
      Subobject.IsStrict (intervalSubobjectOrderIso C s a b E A) :=
  ⟨intervalSubobjectOrderIso_isStrict_of_isAdmissible C s E A,
    isAdmissible_of_intervalSubobjectOrderIso_isStrict C s E A⟩

/-- Owner admissible subobjects and retained strict subobjects have the same
order. -/
def intervalAdmissibleSubobjectOrderIso
    (s : Foundation.Slicing C) {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    (E : s.IntervalCat C a b) :
    s.AdmissibleSubobject C E ≃o
      StrictSubobject ((intervalEquiv C s a b).functor.obj E) :=
  Foundation.admissibleSubobjectOrderIso
    (intervalSubobjectOrderIso C s a b E)
    (intervalSubobjectOrderIso_isAdmissible_iff_isStrict C s E)

/-- Intrinsic owner finite length agrees with retained quasi-abelian finite
length. -/
theorem isFiniteLength_iff
    (s : Foundation.Slicing C) {a b : ℝ} [Fact (a < b)] [Fact (b - a ≤ 1)]
    (E : s.IntervalCat C a b) :
    s.IsFiniteLength C E ↔
      IsStrictArtinianObject ((intervalEquiv C s a b).functor.obj E) ∧
        IsStrictNoetherianObject ((intervalEquiv C s a b).functor.obj E) := by
  constructor
  · rintro ⟨hArt, hNoeth⟩
    exact ⟨
      ObjectProperty.is_of_prop _
        ((Foundation.admissibleSubobjectOrderIso_wellFoundedLT_iff
          (intervalSubobjectOrderIso C s a b E)
          (intervalSubobjectOrderIso_isAdmissible_iff_isStrict C s E)).1 hArt),
      ObjectProperty.is_of_prop _
        ((Foundation.admissibleSubobjectOrderIso_wellFoundedGT_iff
          (intervalSubobjectOrderIso C s a b E)
          (intervalSubobjectOrderIso_isAdmissible_iff_isStrict C s E)).1 hNoeth)⟩
  · rintro ⟨hArt, hNoeth⟩
    exact ⟨
      (Foundation.admissibleSubobjectOrderIso_wellFoundedLT_iff
        (intervalSubobjectOrderIso C s a b E)
        (intervalSubobjectOrderIso_isAdmissible_iff_isStrict C s E)).2
          (isStrictArtinianObject.prop_of_is _),
      (Foundation.admissibleSubobjectOrderIso_wellFoundedGT_iff
        (intervalSubobjectOrderIso C s a b E)
        (intervalSubobjectOrderIso_isAdmissible_iff_isStrict C s E)).2
          (isStrictNoetherianObject.prop_of_is _)⟩

/-- Owner and retained local-finiteness witnesses are definitionally the same
after converting the slicing. -/
theorem isLocallyFinite_iff (s : Foundation.Slicing C) :
    s.IsLocallyFinite C ↔ (toVendor C s).IsLocallyFinite C := by
  constructor
  · rintro ⟨η, hη, hη2, hfinite⟩
    refine ⟨η, hη, hη2, ?_⟩
    intro t
    letI : Fact (t - η < t + η) := ⟨by linarith⟩
    letI : Fact ((t + η) - (t - η) ≤ 1) := ⟨by linarith⟩
    show ∀ E : (toVendor C s).IntervalCat C (t - η) (t + η),
      IsStrictArtinianObject E ∧ IsStrictNoetherianObject E
    intro E
    let E' : s.IntervalCat C (t - η) (t + η) :=
      ⟨E.obj, (toVendor_intervalProp_iff C s _ _ _).1 E.property⟩
    exact (isFiniteLength_iff C s E').1 (hfinite t E')
  · rintro ⟨η, hη, hη2, hfinite⟩
    refine ⟨η, hη, hη2, ?_⟩
    intro t
    letI : Fact (t - η < t + η) := ⟨by linarith⟩
    letI : Fact ((t + η) - (t - η) ≤ 1) := ⟨by linarith⟩
    intro E
    exact (isFiniteLength_iff C s E).2 (hfinite t ((intervalEquiv C s _ _).functor.obj E))

end Slicing

namespace PreStabilityCondition

variable {Λ : Type*} [AddCommGroup Λ]

/-- Convert an owner pre-stability condition to the retained representation.
The retained class map is obtained by precomposing with the canonical map from
the retained Grothendieck quotient to the owner quotient. -/
def toVendor {v : Foundation.K₀ C →+ Λ}
    (σ : Foundation.PreStabilityCondition.WithClassMap C v) :
    CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap C
      (v.comp (GrothendieckGroup.ofVendor C)) where
  slicing := Slicing.toVendor C σ.slicing
  Z := σ.Z
  compat' φ E hP hE := by
    simpa [Foundation.PreStabilityCondition.WithClassMap.charge_def] using
      σ.compat φ E hP hE

/-- Convert a retained pre-stability condition whose class map comes from the
owner quotient back to the owner representation. -/
def ofVendor {v : Foundation.K₀ C →+ Λ}
    (σ : CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap C
      (v.comp (GrothendieckGroup.ofVendor C))) :
    Foundation.PreStabilityCondition.WithClassMap C v where
  slicing := Slicing.ofVendor C σ.slicing
  Z := σ.Z
  compatible φ E hP hE := by
    simpa [CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge_def,
      CategoryTheory.Triangulated.cl] using
      σ.compat φ E hP hE

private theorem vendor_ext {v : CategoryTheory.Triangulated.K₀ C →+ Λ}
    {σ τ : CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap C v}
    (hslicing : σ.slicing = τ.slicing) (hZ : σ.Z = τ.Z) : σ = τ := by
  rcases σ with ⟨sσ, Zσ, cσ⟩
  rcases τ with ⟨sτ, Zτ, cτ⟩
  simp at hslicing hZ
  cases hslicing
  cases hZ
  cases Subsingleton.elim cσ cτ
  rfl

@[simp]
theorem ofVendor_toVendor {v : Foundation.K₀ C →+ Λ}
    (σ : Foundation.PreStabilityCondition.WithClassMap C v) :
    ofVendor C (toVendor C σ) = σ :=
  Foundation.PreStabilityCondition.WithClassMap.ext rfl rfl

@[simp]
theorem toVendor_ofVendor {v : Foundation.K₀ C →+ Λ}
    (σ : CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap C
      (v.comp (GrothendieckGroup.ofVendor C))) :
    toVendor C (ofVendor C σ) = σ :=
  vendor_ext (C := C) (CategoryTheory.Triangulated.Slicing.ext C rfl) rfl

/-- Owner and retained pre-stability conditions are equivalent after the class
map is transported across the canonical Grothendieck-group equivalence. -/
def equiv (v : Foundation.K₀ C →+ Λ) :
    Foundation.PreStabilityCondition.WithClassMap C v ≃
      CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap C
        (v.comp (GrothendieckGroup.ofVendor C)) where
  toFun := toVendor C
  invFun := ofVendor C
  left_inv := ofVendor_toVendor C
  right_inv := toVendor_ofVendor C

end PreStabilityCondition

namespace StabilityCondition

variable {Λ : Type*} [AddCommGroup Λ]
variable [IsTriangulated C]

/-- Convert an owner stability condition to the retained representation. -/
def toVendor {v : Foundation.K₀ C →+ Λ}
    (σ : Foundation.StabilityCondition.WithClassMap C v) :
    CategoryTheory.Triangulated.StabilityCondition.WithClassMap C
      (v.comp (GrothendieckGroup.ofVendor C)) where
  toWithClassMap := PreStabilityCondition.toVendor C σ.toWithClassMap
  locallyFinite := (Slicing.isLocallyFinite_iff C σ.slicing).1 σ.locallyFinite

/-- Convert a retained stability condition back to the owner representation. -/
def ofVendor {v : Foundation.K₀ C →+ Λ}
    (σ : CategoryTheory.Triangulated.StabilityCondition.WithClassMap C
      (v.comp (GrothendieckGroup.ofVendor C))) :
    Foundation.StabilityCondition.WithClassMap C v where
  toWithClassMap := PreStabilityCondition.ofVendor C σ.toWithClassMap
  locallyFinite := (Slicing.isLocallyFinite_iff C
    (PreStabilityCondition.ofVendor C σ.toWithClassMap).slicing).2 σ.locallyFinite

private theorem vendor_ext {v : CategoryTheory.Triangulated.K₀ C →+ Λ}
    {σ τ : CategoryTheory.Triangulated.StabilityCondition.WithClassMap C v}
    (hslicing : σ.slicing = τ.slicing) (hZ : σ.Z = τ.Z) : σ = τ := by
  rcases σ with ⟨σpre, hlfσ⟩
  rcases τ with ⟨τpre, hlfτ⟩
  have hpre : σpre = τpre :=
    PreStabilityCondition.vendor_ext (C := C) hslicing hZ
  cases hpre
  cases Subsingleton.elim hlfσ hlfτ
  rfl

@[simp]
theorem ofVendor_toVendor {v : Foundation.K₀ C →+ Λ}
    (σ : Foundation.StabilityCondition.WithClassMap C v) :
    ofVendor C (toVendor C σ) = σ := by
  apply Foundation.StabilityCondition.WithClassMap.ext
  · exact Slicing.ofVendor_toVendor C σ.slicing
  · rfl

@[simp]
theorem toVendor_ofVendor {v : Foundation.K₀ C →+ Λ}
    (σ : CategoryTheory.Triangulated.StabilityCondition.WithClassMap C
      (v.comp (GrothendieckGroup.ofVendor C))) :
    toVendor C (ofVendor C σ) = σ :=
  vendor_ext (C := C) (CategoryTheory.Triangulated.Slicing.ext C rfl) rfl

/-- Owner and retained stability conditions are equivalent after transporting
the Grothendieck class map. -/
def equiv (v : Foundation.K₀ C →+ Λ) :
    Foundation.StabilityCondition.WithClassMap C v ≃
      CategoryTheory.Triangulated.StabilityCondition.WithClassMap C
        (v.comp (GrothendieckGroup.ofVendor C)) where
  toFun := toVendor C
  invFun := ofVendor C
  left_inv := ofVendor_toVendor C
  right_inv := toVendor_ofVendor C

end StabilityCondition

end BridgelandStabLean.Compatibility.BridgelandStability
