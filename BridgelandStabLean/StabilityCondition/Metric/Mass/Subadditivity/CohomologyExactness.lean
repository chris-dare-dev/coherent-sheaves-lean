/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import BridgelandStabLean.StabilityCondition.Weak.Tilting.Cohomology.Homological
import BridgelandStability.HeartEquivalence.EulerLift
import Mathlib.CategoryTheory.Abelian.Exact

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Cohomological exactness for heart-source triangles

For a distinguished triangle `A ⟶ X₂ ⟶ X₃ ⟶ A[1]` with `A` in the
heart, applying `H⁰` gives a short complex in the heart.  Exactness at
`H⁰(X₂)` is not the assertion that the first map is a kernel: the incoming
map from `H⁻¹(X₃)` may be nonzero.  The correct obstruction is instead the
monicity of the canonical map

`coker(A ⟶ H⁰(X₂)) ⟶ H⁰(X₃)`.

This file records that exact equivalence and connects it to Mathlib's
`Functor.IsHomological` interface.  It is deliberately a bridge, not an
assumption or a global instance.  For a distinguished heart-source triangle,
the canonical cokernel comparison is ultimately an isomorphism: the rotated
triangle makes it epic because `H⁰'(A[1])` vanishes, while exactness makes it
monic.  This does not make the displayed three-term complex short exact; its
first map can still have a nonzero incoming `H⁻¹(X₃)` term.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory.Triangulated

noncomputable section

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

open BridgelandStabLean.Tilting

/-- The foundational degree-zero cohomology functor is definitionally the
generic t-structure cohomology functor used by the tilting subsystem. -/
noncomputable def HeartStabilityData.H0FunctorIsoOriginalHeartCohFunctor
    (h : HeartStabilityData C) :
    h.H0Functor (C := C) ≅ originalHeartCohFunctor h.t 0 :=
  Iso.refl _

/-- The `H⁰` short complex attached to a distinguished heart-source
triangle.  This abbreviation fixes the proof of the zero composite to the
canonical distinguished-triangle proof. -/
noncomputable abbrev HeartStabilityData.heartSourceH0Complex
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    ShortComplex h.t.heart.FullSubcategory :=
  h.heartSourceH0primeShortComplex (C := C) A f g
    (comp_distTriang_mor_zero₁₂ _ hT)

/-- Exactness of the heart-source `H⁰` complex is precisely monicity of its
canonical cokernel comparison into `H⁰(X₃)`. -/
theorem HeartStabilityData.heartSourceH0Complex_exact_iff_mono_cokernelDesc
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    (h.heartSourceH0Complex (C := C) A hT).Exact ↔
      Mono (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
        (comp_distTriang_mor_zero₁₂ _ hT)) := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  exact (h.heartSourceH0Complex (C := C) A hT).exact_iff_mono_cokernel_desc

/-! ## The nonpositive case

When `X ∈ D^{≤ 0}`, maps from `H⁰'(X)` to an object of the heart are the
same as maps from `X`: first project to `τ≥0 X`, then use that
`τ≤0(τ≥0 X) ⟶ τ≥0 X` is an isomorphism.  This is the universal property
needed to show that the last map in the `H⁰'` image of a nonpositive
distinguished triangle is a cokernel.
-/

/-- For a nonpositive object, the defining inclusion of `H⁰'` into its
nonnegative truncation is an isomorphism. -/
noncomputable def HeartStabilityData.H0primeObjIsoTruncGEOfIsLE
    (h : HeartStabilityData C) (X : C) [h.t.IsLE X 0] :
    (h.H0prime (C := C) X).obj ≅ (h.t.truncGE 0).obj X := by
  have hLE : h.t.IsLE ((h.t.truncGE 0).obj X) 0 := by infer_instance
  exact @asIso _ _ _ _ ((h.t.truncLEι 0).app ((h.t.truncGE 0).obj X))
    ((h.t.isLE_iff_isIso_truncLEι_app 0 ((h.t.truncGE 0).obj X)).mp hLE)

/-- Read a morphism from `H⁰'(X)` to a heart object as a morphism from a
nonpositive object `X`. -/
@[nolint defsWithUnderscore]
noncomputable def HeartStabilityData.fromH0primeHom_of_isLE
    (h : HeartStabilityData C) {X : C} [h.t.IsLE X 0]
    (E : h.t.heart.FullSubcategory) (f : h.H0prime (C := C) X ⟶ E) :
    X ⟶ E.obj :=
  (h.t.truncGEπ 0).app X ≫
    (h.H0primeObjIsoTruncGEOfIsLE (C := C) X).inv ≫ f.hom

/-- Construct a morphism `H⁰'(X) ⟶ E` from a morphism `X ⟶ E` when
`X` is nonpositive. -/
@[nolint defsWithUnderscore]
noncomputable def HeartStabilityData.toH0primeHom_of_isLE
    (h : HeartStabilityData C) {X : C} [h.t.IsLE X 0]
    (E : h.t.heart.FullSubcategory) (f : X ⟶ E.obj) :
    h.H0prime (C := C) X ⟶ E :=
  letI : h.t.IsGE E.obj 0 := (h.t.mem_heart_iff E.obj).mp E.property |>.2
  ObjectProperty.homMk
    ((h.H0primeObjIsoTruncGEOfIsLE (C := C) X).hom ≫ h.t.descTruncGE f 0)

@[simp]
theorem HeartStabilityData.fromH0primeHom_of_isLE_toH0primeHom_of_isLE
    (h : HeartStabilityData C) {X : C} [h.t.IsLE X 0]
    (E : h.t.heart.FullSubcategory) (f : X ⟶ E.obj) :
    h.fromH0primeHom_of_isLE (C := C) E
      (h.toH0primeHom_of_isLE (C := C) E f) = f := by
  letI : h.t.IsGE E.obj 0 := (h.t.mem_heart_iff E.obj).mp E.property |>.2
  simp only [HeartStabilityData.fromH0primeHom_of_isLE,
    HeartStabilityData.toH0primeHom_of_isLE, ObjectProperty.homMk_hom,
    Iso.inv_hom_id_assoc]
  exact h.t.π_descTruncGE f 0

@[simp]
theorem HeartStabilityData.toH0primeHom_of_isLE_fromH0primeHom_of_isLE
    (h : HeartStabilityData C) {X : C} [h.t.IsLE X 0]
    (E : h.t.heart.FullSubcategory) (f : h.H0prime (C := C) X ⟶ E) :
    h.toH0primeHom_of_isLE (C := C) E
      (h.fromH0primeHom_of_isLE (C := C) E f) = f := by
  letI : h.t.IsGE E.obj 0 := (h.t.mem_heart_iff E.obj).mp E.property |>.2
  apply ObjectProperty.hom_ext
  change
    (h.H0primeObjIsoTruncGEOfIsLE (C := C) X).hom ≫
        h.t.descTruncGE
          ((h.t.truncGEπ 0).app X ≫
            (h.H0primeObjIsoTruncGEOfIsLE (C := C) X).inv ≫ f.hom) 0 =
      f.hom
  calc
    _ = (h.H0primeObjIsoTruncGEOfIsLE (C := C) X).hom ≫
        ((h.H0primeObjIsoTruncGEOfIsLE (C := C) X).inv ≫ f.hom) := by
      congr 1
      apply h.t.from_truncGE_obj_ext
      rw [h.t.π_descTruncGE]
      rfl
    _ = f.hom := by simp

@[simp]
theorem HeartStabilityData.fromH0primeHom_of_isLE_zero
    (h : HeartStabilityData C) {X : C} [h.t.IsLE X 0]
    (E : h.t.heart.FullSubcategory) :
    h.fromH0primeHom_of_isLE (C := C) E
      (0 : h.H0prime (C := C) X ⟶ E) = 0 := by
  simp [HeartStabilityData.fromH0primeHom_of_isLE]

@[reassoc]
theorem HeartStabilityData.toH0primeHom_of_isLE_comp
    (h : HeartStabilityData C) {X Y : C} [h.t.IsLE X 0] [h.t.IsLE Y 0]
    (E : h.t.heart.FullSubcategory) (f : X ⟶ Y) (g : Y ⟶ E.obj) :
    h.toH0primeHom_of_isLE (C := C) E (f ≫ g) =
      (h.H0primeFunctor (C := C)).map f ≫
        h.toH0primeHom_of_isLE (C := C) E g := by
  letI : h.t.IsGE E.obj 0 := (h.t.mem_heart_iff E.obj).mp E.property |>.2
  apply ObjectProperty.hom_ext
  change
    (h.H0primeObjIsoTruncGEOfIsLE (C := C) X).hom ≫
        h.t.descTruncGE (f ≫ g) 0 =
      (h.t.truncLE 0).map ((h.t.truncGE 0).map f) ≫
        (h.H0primeObjIsoTruncGEOfIsLE (C := C) Y).hom ≫
          h.t.descTruncGE g 0
  rw [← h.t.truncGE_map_comp_descTruncGE (C := C) f g 0]
  simpa [HeartStabilityData.H0primeObjIsoTruncGEOfIsLE, Category.assoc] using
    congrArg (fun k ↦ k ≫ h.t.descTruncGE g 0)
      ((h.t.truncLEι 0).naturality ((h.t.truncGE 0).map f)).symm

@[reassoc]
theorem HeartStabilityData.fromH0primeHom_of_isLE_naturality
    (h : HeartStabilityData C) {X Y : C} [h.t.IsLE X 0] [h.t.IsLE Y 0]
    (E : h.t.heart.FullSubcategory) (f : X ⟶ Y)
    (g : h.H0prime (C := C) Y ⟶ E) :
    h.fromH0primeHom_of_isLE (C := C) E
        ((h.H0primeFunctor (C := C)).map f ≫ g) =
      f ≫ h.fromH0primeHom_of_isLE (C := C) E g := by
  have hEq := h.toH0primeHom_of_isLE_comp (C := C) E f
    (h.fromH0primeHom_of_isLE (C := C) E g)
  rw [h.toH0primeHom_of_isLE_fromH0primeHom_of_isLE] at hEq
  have hEq' := congrArg (h.fromH0primeHom_of_isLE (C := C) E) hEq
  simpa using hEq'.symm

/-- Applying `H⁰'` to a distinguished triangle entirely contained in
`D^{≤0}` produces a short complex whose second map is a cokernel, hence an
exact short complex. -/
theorem HeartStabilityData.H0primeFunctor_map_distinguished_exact_of_isLE
    (h : HeartStabilityData C) (T : Triangle C) (hT : T ∈ distTriang C)
    [h.t.IsLE T.obj₁ 0] [h.t.IsLE T.obj₂ 0] [h.t.IsLE T.obj₃ 0] :
    ((shortComplexOfDistTriangle T hT).map
      (h.H0primeFunctor (C := C))).Exact := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  let S := (shortComplexOfDistTriangle T hT).map (h.H0primeFunctor (C := C))
  apply ShortComplex.exact_of_g_is_cokernel
  have kernel_condition {E : h.t.heart.FullSubcategory}
      (k : S.X₂ ⟶ E) (hk : S.f ≫ k = 0) :
      T.mor₁ ≫ h.fromH0primeHom_of_isLE (C := C) (X := T.obj₂) E k = 0 := by
    have hk₀ : (h.H0primeFunctor (C := C)).map T.mor₁ ≫ k = 0 := by
      simpa [S] using hk
    have hnat := h.fromH0primeHom_of_isLE_naturality (C := C)
      (X := T.obj₁) (Y := T.obj₂) E T.mor₁ k
    calc
      T.mor₁ ≫ h.fromH0primeHom_of_isLE (C := C) (X := T.obj₂) E k =
          h.fromH0primeHom_of_isLE (C := C) (X := T.obj₁) E
            ((h.H0primeFunctor (C := C)).map T.mor₁ ≫ k) := hnat.symm
      _ = h.fromH0primeHom_of_isLE (C := C) (X := T.obj₁) E 0 :=
        congrArg
          (fun q : h.H0prime (C := C) T.obj₁ ⟶ E ↦
            h.fromH0primeHom_of_isLE (C := C) (X := T.obj₁) E q) hk₀
      _ = 0 := h.fromH0primeHom_of_isLE_zero (C := C) E
  let desc : ∀ {E : h.t.heart.FullSubcategory} (k : S.X₂ ⟶ E)
      (hk : S.f ≫ k = 0), S.X₃ ⟶ E :=
    fun {E} k hk ↦ h.toH0primeHom_of_isLE (C := C) (X := T.obj₃) E
      ((T.yoneda_exact₂ hT
        (h.fromH0primeHom_of_isLE (C := C) (X := T.obj₂) E k)
        (kernel_condition k hk)).choose)
  refine CokernelCofork.IsColimit.ofπ S.g S.zero desc ?_ ?_
  · intro E k hk
    let k' := h.fromH0primeHom_of_isLE (C := C) (X := T.obj₂) E k
    let l' := (T.yoneda_exact₂ hT k' (kernel_condition k hk)).choose
    have hl' := (T.yoneda_exact₂ hT k' (kernel_condition k hk)).choose_spec
    have hfac :
        h.fromH0primeHom_of_isLE (C := C) (X := T.obj₂) E
            (S.g ≫ desc k hk) =
          h.fromH0primeHom_of_isLE (C := C) (X := T.obj₂) E k := by
      rw [show desc k hk = h.toH0primeHom_of_isLE (C := C) (X := T.obj₃) E l' by rfl]
      rw [show S.g = (h.H0primeFunctor (C := C)).map T.mor₂ by rfl]
      have hnat := h.fromH0primeHom_of_isLE_naturality (C := C)
        (X := T.obj₂) (Y := T.obj₃) E T.mor₂
        (h.toH0primeHom_of_isLE (C := C) (X := T.obj₃) E l')
      calc
        _ = T.mor₂ ≫ h.fromH0primeHom_of_isLE (C := C) (X := T.obj₃) E
              (h.toH0primeHom_of_isLE (C := C) (X := T.obj₃) E l') := hnat
        _ = T.mor₂ ≫ l' := by
          rw [h.fromH0primeHom_of_isLE_toH0primeHom_of_isLE]
        _ = h.fromH0primeHom_of_isLE (C := C) (X := T.obj₂) E k := by
          simpa [k', l'] using hl'.symm
    have hfac' := congrArg
      (h.toH0primeHom_of_isLE (C := C) (X := T.obj₂) E) hfac
    simpa using hfac'
  · intro E k hk m hm
    let k' := h.fromH0primeHom_of_isLE (C := C) (X := T.obj₂) E k
    let l' := (T.yoneda_exact₂ hT k' (kernel_condition k hk)).choose
    have hm₀ : (h.H0primeFunctor (C := C)).map T.mor₂ ≫ m = k := by
      simpa [S] using hm
    have hm' := congrArg
      (h.fromH0primeHom_of_isLE (C := C) (X := T.obj₂) E) hm₀
    have hm'' :
        T.mor₂ ≫ h.fromH0primeHom_of_isLE (C := C) (X := T.obj₃) E m = k' := by
      have hnat := h.fromH0primeHom_of_isLE_naturality (C := C)
        (X := T.obj₂) (Y := T.obj₃) E T.mor₂ m
      exact hnat.symm.trans (by simpa [k'] using hm')
    have hl' := (T.yoneda_exact₂ hT k' (kernel_condition k hk)).choose_spec
    have hzero :
        T.mor₂ ≫
          (h.fromH0primeHom_of_isLE (C := C) (X := T.obj₃) E m - l') = 0 := by
      rw [Preadditive.comp_sub, hm'', ← hl']
      simp
    obtain ⟨q, hq⟩ := T.yoneda_exact₃ hT
      (h.fromH0primeHom_of_isLE (C := C) (X := T.obj₃) E m - l') hzero
    have hqzero : q = 0 := by
      letI : h.t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (-1) :=
        h.t.isLE_shift T.obj₁ 0 1 (-1) (by lia)
      letI : h.t.IsGE E.obj 0 := (h.t.mem_heart_iff E.obj).mp E.property |>.2
      exact h.t.zero q (-1) 0 (by lia)
    have hmEq : h.fromH0primeHom_of_isLE (C := C) (X := T.obj₃) E m = l' := by
      rw [← sub_eq_zero]
      simpa [hqzero] using hq
    have hmEq' := congrArg
      (h.toH0primeHom_of_isLE (C := C) (X := T.obj₃) E) hmEq
    simpa [desc, l'] using hmEq'

/-! ## Removing the nonpositive hypothesis -/

/-- `H⁰'` sends the canonical map `τ≤0 X ⟶ X` to an isomorphism. -/
theorem HeartStabilityData.isIso_H0primeFunctor_map_truncLEι
    (h : HeartStabilityData C) (X : C) :
    IsIso ((h.H0primeFunctor (C := C)).map ((h.t.truncLEι 0).app X)) := by
  haveI hH0 : IsIso
      ((h.H0Functor (C := C)).map ((h.t.truncLEι 0).app X)) := by
    let eH0 :
        (h.H0Functor (C := C)).obj ((h.t.truncLE 0).obj X) ≅
          (h.H0Functor (C := C)).obj X := by
      refine ObjectProperty.isoMk _ ?_
      simpa [HeartStabilityData.H0Functor, HeartStabilityData.heartCohFunctor,
        HeartStabilityData.heartCoh, HeartStabilityData.heartShiftOfPure] using
        (shiftFunctor C (0 : ℤ)).mapIso
          ((h.t.truncGE 0).mapIso
            (asIso ((h.t.truncLE 0).map ((h.t.truncLEι 0).app X))))
    have heH0 :
        (h.H0Functor (C := C)).map ((h.t.truncLEι 0).app X) = eH0.hom := by
      ext
      rfl
    rw [heH0]
    infer_instance
  let e := h.H0FunctorIsoH0primeFunctor (C := C)
  haveI hcomp : IsIso
      (e.hom.app ((h.t.truncLE 0).obj X) ≫
        (h.H0primeFunctor (C := C)).map ((h.t.truncLEι 0).app X)) := by
    rw [← e.hom.naturality ((h.t.truncLEι 0).app X)]
    infer_instance
  exact IsIso.of_isIso_comp_left (e.hom.app ((h.t.truncLE 0).obj X))
    ((h.H0primeFunctor (C := C)).map ((h.t.truncLEι 0).app X))

/-- The canonical `H⁰` complex of a distinguished triangle whose source is
in the heart is exact, without assuming an external homological-functor
instance. -/
theorem HeartStabilityData.heartSourceH0Complex_exact
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    (h.heartSourceH0Complex (C := C) A hT).Exact := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  letI hALE : h.t.IsLE A.obj 0 := (h.t.mem_heart_iff A.obj).mp A.property |>.1
  let a : A.obj ⟶ (h.t.truncLE 0).obj X₂ := h.t.liftTruncLE f 0
  obtain ⟨Q, q, d, hQ⟩ := distinguished_cocone_triangle a
  let oct := Triangulated.someOctahedron (h.t.liftTruncLE_ι f 0)
    hQ (h.t.triangleLEGT_distinguished 0 X₂) hT
  have hQLE : h.t.IsLE Q 0 := by
    letI : h.t.IsLE (A.obj⟦(1 : ℤ)⟧) (-1) :=
      h.t.isLE_shift A.obj 0 1 (-1) (by lia)
    have hAshLE : h.t.IsLE (A.obj⟦(1 : ℤ)⟧) 0 :=
      h.t.isLE_of_le _ (-1) 0
    exact h.t.isLE₂ (Triangle.mk a q d).rotate
      (rot_of_distTriang _ hQ) 0 (by dsimp; infer_instance) (by
        dsimp
        exact hAshLE)
  let TQ := oct.triangle
  let TX₃ := (h.t.triangleLEGT 0).obj X₃
  obtain ⟨e, he⟩ := h.t.triangle_iso_exists oct.mem
    (h.t.triangleLEGT_distinguished 0 X₃) (Iso.refl X₃) 0 1
    (by simpa [TQ] using hQLE)
    (by dsimp [TQ, oct]; exact h.t.isGE_truncGT_obj X₂ 0 1)
    (by dsimp [TX₃]; exact h.t.isLE_truncLE_obj X₃ 0 0)
    (by dsimp [TX₃]; exact h.t.isGE_truncGT_obj X₃ 0 1)
  let eQ : Q ≅ (h.t.truncLE 0).obj X₃ := Triangle.π₁.mapIso e
  have heQ : oct.m₁ = eQ.hom ≫ (h.t.truncLEι 0).app X₃ := by
    have hecomm := e.hom.comm₁
    change oct.m₁ ≫ e.hom.hom₂ = eQ.hom ≫ (h.t.truncLEι 0).app X₃ at hecomm
    rw [he] at hecomm
    simpa using hecomm
  have hq : q ≫ eQ.hom = (h.t.truncLE 0).map g := by
    apply h.t.to_truncLE_obj_ext
    rw [Category.assoc, ← heQ]
    exact oct.comm₁.trans (by
      simpa using ((h.t.truncLEι 0).naturality g).symm)
  let Tle : Triangle C := Triangle.mk a ((h.t.truncLE 0).map g) (eQ.inv ≫ d)
  have hTle : Tle ∈ distTriang C := by
    refine isomorphic_distinguished _ hQ Tle ?_
    exact (Triangle.isoMk (Triangle.mk a q d) Tle
      (Iso.refl _) (Iso.refl _) eQ
      (by simp [Tle])
      (by simpa [Tle] using hq)
      (by simp [Tle])).symm
  letI hTleLE₁ : h.t.IsLE Tle.obj₁ 0 := by
    dsimp [Tle]
    infer_instance
  letI hTleLE₂ : h.t.IsLE Tle.obj₂ 0 := by
    dsimp [Tle]
    infer_instance
  letI hTleLE₃ : h.t.IsLE Tle.obj₃ 0 := by
    dsimp [Tle]
    infer_instance
  have hExactLE :
      ((shortComplexOfDistTriangle Tle hTle).map
        (h.H0primeFunctor (C := C))).Exact := by
    exact h.H0primeFunctor_map_distinguished_exact_of_isLE (C := C) Tle hTle
  let Sle := (shortComplexOfDistTriangle Tle hTle).map
    (h.H0primeFunctor (C := C))
  let S := (shortComplexOfDistTriangle (Triangle.mk f g δ) hT).map
    (h.H0primeFunctor (C := C))
  letI hIso₂ : IsIso ((h.H0primeFunctor (C := C)).map
      ((h.t.truncLEι 0).app X₂)) := h.isIso_H0primeFunctor_map_truncLEι (C := C) X₂
  letI hIso₃ : IsIso ((h.H0primeFunctor (C := C)).map
      ((h.t.truncLEι 0).app X₃)) := h.isIso_H0primeFunctor_map_truncLEι (C := C) X₃
  let e₂ := @asIso _ _ _ _
    ((h.H0primeFunctor (C := C)).map ((h.t.truncLEι 0).app X₂)) hIso₂
  let e₃ := @asIso _ _ _ _
    ((h.H0primeFunctor (C := C)).map ((h.t.truncLEι 0).app X₃)) hIso₃
  let eS : Sle ≅ S := ShortComplex.isoMk
    (Iso.refl _)
    e₂ e₃
    (by
      dsimp [Sle, S, e₂, e₃, Tle]
      simp only [Category.id_comp]
      rw [← Functor.map_comp]
      exact congrArg ((h.H0primeFunctor (C := C)).map)
        (by simpa [a] using (h.t.liftTruncLE_ι f 0).symm))
    (by
      dsimp [Sle, S, e₂, e₃, Tle]
      simp only [← Functor.map_comp]
      simpa using congrArg ((h.H0primeFunctor (C := C)).map)
        ((h.t.truncLEι 0).naturality g).symm)
  have hExact : S.Exact :=
    (ShortComplex.exact_iff_of_iso eS).mp (by simpa [Sle] using hExactLE)
  exact (ShortComplex.exact_iff_of_iso
    (h.heartSourceH0primeShortComplexIso (C := C) A hT)).mpr
      (by simpa [S] using hExact)

/-- More generally, `H⁰'` maps a distinguished triangle with nonpositive
source to an exact short complex.  The proof replaces the other two objects
by their nonpositive truncations; the cone comparison is the same one used
for a source in the heart. -/
theorem HeartStabilityData.H0primeFunctor_map_distinguished_exact_of_obj₁_isLE
    (h : HeartStabilityData C) (T : Triangle C) (hT : T ∈ distTriang C)
    [h.t.IsLE T.obj₁ 0] :
    ((shortComplexOfDistTriangle T hT).map
      (h.H0primeFunctor (C := C))).Exact := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  let a : T.obj₁ ⟶ (h.t.truncLE 0).obj T.obj₂ :=
    h.t.liftTruncLE T.mor₁ 0
  obtain ⟨Q, q, d, hQ⟩ := distinguished_cocone_triangle a
  let oct := Triangulated.someOctahedron (h.t.liftTruncLE_ι T.mor₁ 0)
    hQ (h.t.triangleLEGT_distinguished 0 T.obj₂) hT
  have hQLE : h.t.IsLE Q 0 := by
    letI : h.t.IsLE (T.obj₁⟦(1 : ℤ)⟧) (-1) :=
      h.t.isLE_shift T.obj₁ 0 1 (-1) (by lia)
    have hAshLE : h.t.IsLE (T.obj₁⟦(1 : ℤ)⟧) 0 :=
      h.t.isLE_of_le _ (-1) 0
    exact h.t.isLE₂ (Triangle.mk a q d).rotate
      (rot_of_distTriang _ hQ) 0 (by dsimp; infer_instance) (by
        dsimp
        exact hAshLE)
  let TQ := oct.triangle
  let TX₃ := (h.t.triangleLEGT 0).obj T.obj₃
  obtain ⟨e, he⟩ := h.t.triangle_iso_exists oct.mem
    (h.t.triangleLEGT_distinguished 0 T.obj₃) (Iso.refl T.obj₃) 0 1
    (by simpa [TQ] using hQLE)
    (by dsimp [TQ, oct]; exact h.t.isGE_truncGT_obj T.obj₂ 0 1)
    (by dsimp [TX₃]; exact h.t.isLE_truncLE_obj T.obj₃ 0 0)
    (by dsimp [TX₃]; exact h.t.isGE_truncGT_obj T.obj₃ 0 1)
  let eQ : Q ≅ (h.t.truncLE 0).obj T.obj₃ := Triangle.π₁.mapIso e
  have heQ : oct.m₁ = eQ.hom ≫ (h.t.truncLEι 0).app T.obj₃ := by
    have hecomm := e.hom.comm₁
    change oct.m₁ ≫ e.hom.hom₂ =
      eQ.hom ≫ (h.t.truncLEι 0).app T.obj₃ at hecomm
    rw [he] at hecomm
    simpa using hecomm
  have hq : q ≫ eQ.hom = (h.t.truncLE 0).map T.mor₂ := by
    apply h.t.to_truncLE_obj_ext
    rw [Category.assoc, ← heQ]
    exact oct.comm₁.trans (by
      simpa using ((h.t.truncLEι 0).naturality T.mor₂).symm)
  let Tle : Triangle C :=
    Triangle.mk a ((h.t.truncLE 0).map T.mor₂) (eQ.inv ≫ d)
  have hTle : Tle ∈ distTriang C := by
    refine isomorphic_distinguished _ hQ Tle ?_
    exact (Triangle.isoMk (Triangle.mk a q d) Tle
      (Iso.refl _) (Iso.refl _) eQ
      (by simp [Tle])
      (by simpa [Tle] using hq)
      (by simp [Tle])).symm
  letI hTleLE₁ : h.t.IsLE Tle.obj₁ 0 := by
    dsimp [Tle]
    infer_instance
  letI hTleLE₂ : h.t.IsLE Tle.obj₂ 0 := by
    dsimp [Tle]
    infer_instance
  letI hTleLE₃ : h.t.IsLE Tle.obj₃ 0 := by
    dsimp [Tle]
    infer_instance
  have hExactLE :
      ((shortComplexOfDistTriangle Tle hTle).map
        (h.H0primeFunctor (C := C))).Exact :=
    h.H0primeFunctor_map_distinguished_exact_of_isLE (C := C) Tle hTle
  let Sle := (shortComplexOfDistTriangle Tle hTle).map
    (h.H0primeFunctor (C := C))
  let S := (shortComplexOfDistTriangle T hT).map
    (h.H0primeFunctor (C := C))
  letI hIso₂ : IsIso ((h.H0primeFunctor (C := C)).map
      ((h.t.truncLEι 0).app T.obj₂)) :=
    h.isIso_H0primeFunctor_map_truncLEι (C := C) T.obj₂
  letI hIso₃ : IsIso ((h.H0primeFunctor (C := C)).map
      ((h.t.truncLEι 0).app T.obj₃)) :=
    h.isIso_H0primeFunctor_map_truncLEι (C := C) T.obj₃
  let e₂ := @asIso _ _ _ _
    ((h.H0primeFunctor (C := C)).map ((h.t.truncLEι 0).app T.obj₂)) hIso₂
  let e₃ := @asIso _ _ _ _
    ((h.H0primeFunctor (C := C)).map ((h.t.truncLEι 0).app T.obj₃)) hIso₃
  let eS : Sle ≅ S := ShortComplex.isoMk
    (Iso.refl _) e₂ e₃
    (by
      dsimp [Sle, S, e₂, e₃, Tle]
      simp only [Category.id_comp]
      rw [← Functor.map_comp]
      exact congrArg ((h.H0primeFunctor (C := C)).map)
        (by simpa [a] using (h.t.liftTruncLE_ι T.mor₁ 0).symm))
    (by
      dsimp [Sle, S, e₂, e₃, Tle]
      simp only [← Functor.map_comp]
      simpa using congrArg ((h.H0primeFunctor (C := C)).map)
        ((h.t.truncLEι 0).naturality T.mor₂).symm)
  exact (ShortComplex.exact_iff_of_iso eS).mp
    (by simpa [Sle] using hExactLE)

/-- If the source of a distinguished triangle is strictly positive, the
induced map from the middle to the final `H⁰'` object is monic. -/
theorem HeartStabilityData.mono_H0primeFunctor_map_mor₂_of_obj₁_isGE_one
    (h : HeartStabilityData C) (T : Triangle C) (hT : T ∈ distTriang C)
    [h.t.IsGE T.obj₁ 1] :
    Mono ((h.H0primeFunctor (C := C)).map T.mor₂) := by
  constructor
  intro E u v huv
  let F := preadditiveCoyoneda.obj (Opposite.op E)
  let S := (shortComplexOfDistTriangle T hT).map
    (h.H0primeFunctor (C := C) ⋙ F)
  letI : h.t.IsGE (shortComplexOfDistTriangle T hT).X₁ 1 := by
    dsimp
    infer_instance
  have hTriangle : Triangle.mk T.mor₁ T.mor₂ T.mor₃ = T := by
    cases T
    rfl
  have hExact : S.Exact := by
    simpa [S, F, hTriangle] using
      h.H0primeFunctor_preadditiveCoyoneda_exact_of_isGE_one
        (C := C) (A := T.obj₁) (Z := T.obj₂) (X₃ := T.obj₃) hT E
  have hzeroObj : IsZero S.X₁ := by
    exact F.map_isZero h.isZero_H0prime_of_isGE_one
  have hzero : S.f = 0 := hzeroObj.eq_of_src _ _
  letI : Mono S.g := hExact.mono_g hzero
  exact (AddCommGrpCat.mono_iff_injective S.g).mp inferInstance
    (by simpa [S, F] using huv)

/-- The canonical `H⁰'` functor of a bounded t-structure is homological.
This construction is unconditional: truncate the source of an arbitrary
triangle at degree zero, use exactness for the nonpositive-source triangle,
and compare it to the original complex through a morphism that is an
isomorphism on the first two terms and monic on the third. -/
theorem HeartStabilityData.H0primeFunctor_isHomological_unconditional
    (h : HeartStabilityData C) :
    Functor.IsHomological (h.H0primeFunctor (C := C)) := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  refine ⟨fun T hT ↦ ?_⟩
  obtain ⟨Z, v, w, m₁, m₃, h13, h23, _hm₁, _hmw, hm₃⟩ :=
    h.t.exists_truncLT_octahedral_split (C := C) hT 1
  let Tle : Triangle C :=
    Triangle.mk ((h.t.truncLTι 1).app T.obj₁ ≫ T.mor₁) v w
  let Tge : Triangle C := Triangle.mk m₁ m₃
    (T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map
      ((h.t.truncGEπ 1).app T.obj₁))
  letI : h.t.IsLE Tle.obj₁ 0 := by
    dsimp [Tle]
    exact h.t.isLE_truncLT_obj T.obj₁ 1 0 (by lia)
  have hExactLE :
      ((shortComplexOfDistTriangle Tle h13).map
        (h.H0primeFunctor (C := C))).Exact :=
    h.H0primeFunctor_map_distinguished_exact_of_obj₁_isLE
      (C := C) Tle h13
  letI : h.t.IsGE Tge.obj₁ 1 := by
    dsimp [Tge]
    exact h.t.isGE_truncGE_obj T.obj₁ 1 1
  letI hmono₃ : Mono ((h.H0primeFunctor (C := C)).map m₃) :=
    h.mono_H0primeFunctor_map_mor₂_of_obj₁_isGE_one
      (C := C) Tge h23
  let Sle := (shortComplexOfDistTriangle Tle h13).map
    (h.H0primeFunctor (C := C))
  let S := (shortComplexOfDistTriangle T hT).map
    (h.H0primeFunctor (C := C))
  haveI hIso₁ : IsIso ((h.H0primeFunctor (C := C)).map
      ((h.t.truncLTι 1).app T.obj₁)) := by
    have hIso := h.isIso_H0primeFunctor_map_truncLEι (C := C) T.obj₁
    norm_num [TStructure.truncLE, TStructure.truncLEι] at hIso
    exact hIso
  let α : Sle ⟶ S :=
    { τ₁ := (h.H0primeFunctor (C := C)).map
        ((h.t.truncLTι 1).app T.obj₁)
      τ₂ := 𝟙 _
      τ₃ := (h.H0primeFunctor (C := C)).map m₃
      comm₁₂ := by
        dsimp [Sle, S, Tle]
        simp only [Category.comp_id, ← Functor.map_comp]
      comm₂₃ := by
        dsimp [Sle, S, Tle]
        simp only [Category.id_comp, ← Functor.map_comp]
        exact congrArg ((h.H0primeFunctor (C := C)).map) hm₃.symm }
  haveI : IsIso α.τ₁ := by
    dsimp [α]
    exact hIso₁
  haveI : Epi α.τ₁ := by
    infer_instance
  haveI : IsIso α.τ₂ := by
    dsimp [α]
    exact Iso.isIso_hom (Iso.refl _)
  haveI : Mono α.τ₃ := by
    dsimp [α]
    exact hmono₃
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono α).mp
    (by simpa [Sle] using hExactLE)

/-- Unconditional homologicality transported across the canonical natural
isomorphism from `H⁰'` to the heart-valued `H⁰` functor. -/
theorem HeartStabilityData.H0Functor_isHomological_unconditional
    (h : HeartStabilityData C) :
    Functor.IsHomological (h.H0Functor (C := C)) := by
  letI : Functor.IsHomological (h.H0primeFunctor (C := C)) :=
    h.H0primeFunctor_isHomological_unconditional (C := C)
  exact h.H0Functor_isHomological_of_H0primeFunctor (C := C)

/-- A homological `H⁰'` functor supplies the correct heart-source exact
complex.  This theorem is useful both as a regression test for a future global
instance and as the forward half of the exactness bridge. -/
theorem HeartStabilityData.heartSourceH0Complex_exact_of_isHomological
    (h : HeartStabilityData C)
    [Functor.IsHomological (h.H0primeFunctor (C := C))]
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    (h.heartSourceH0Complex (C := C) A hT).Exact := by
  let hmap := Functor.map_distinguished_exact
    (F := h.H0primeFunctor (C := C)) (Triangle.mk f g δ) hT
  exact (ShortComplex.exact_iff_of_iso
    (h.heartSourceH0primeShortComplexIso (C := C) A hT)).2 hmap

/-- The same bridge stated using the foundational library's primary `H⁰` functor.  The
homological structure is transported across the canonical natural
isomorphism `H⁰ ≅ H⁰'`; no global instance is installed. -/
theorem HeartStabilityData.heartSourceH0Complex_exact_of_H0Functor_isHomological
    (h : HeartStabilityData C)
    [Functor.IsHomological (h.H0Functor (C := C))]
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    (h.heartSourceH0Complex (C := C) A hT).Exact := by
  letI : Functor.IsHomological (h.H0primeFunctor (C := C)) :=
    Functor.IsHomological.of_iso (h.H0FunctorIsoH0primeFunctor (C := C))
  exact h.heartSourceH0Complex_exact_of_isHomological (C := C) A hT

/-- Consequently a homological `H⁰'` functor makes the canonical cokernel
comparison monic. -/
theorem HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc
    (h : HeartStabilityData C)
    [Functor.IsHomological (h.H0primeFunctor (C := C))]
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    Mono (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
      (comp_distTriang_mor_zero₁₂ _ hT)) :=
  (h.heartSourceH0Complex_exact_iff_mono_cokernelDesc (C := C) A hT).mp
    (h.heartSourceH0Complex_exact_of_isHomological (C := C) A hT)

/-- Unconditional form of the heart-source obstruction theorem: the canonical
map from the cokernel of `A ⟶ H⁰'(X₂)` into `H⁰'(X₃)` is monic for
every distinguished heart-source triangle. -/
theorem HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    Mono (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
      (comp_distTriang_mor_zero₁₂ _ hT)) :=
  (h.heartSourceH0Complex_exact_iff_mono_cokernelDesc (C := C) A hT).mp
    (h.heartSourceH0Complex_exact (C := C) A hT)

/-- The canonical cokernel comparison for a distinguished heart-source
triangle is an isomorphism.  Epicity comes from applying homological `H⁰'` to
the rotated triangle: its last term is `H⁰'(A[1]) = 0`.  Monicity is the
existing heart-source exactness theorem. -/
theorem HeartStabilityData.isIso_heartSourceH0primeShortComplex_cokernelDesc_unconditional
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    IsIso (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
      (comp_distTriang_mor_zero₁₂ _ hT)) := by
  letI := h.t.hasHeartFullSubcategory
  letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
  letI : Functor.IsHomological (h.H0primeFunctor (C := C)) :=
    h.H0primeFunctor_isHomological_unconditional (C := C)
  let T : Triangle C := Triangle.mk f g δ
  have hTrot : T.rotate ∈ distTriang C := rot_of_distTriang T hT
  let Srot := (shortComplexOfDistTriangle T.rotate hTrot).map
    (h.H0primeFunctor (C := C))
  have hExact : Srot.Exact :=
    Functor.map_distinguished_exact (h.H0primeFunctor (C := C)) T.rotate hTrot
  letI : h.t.IsLE A.obj 0 := (h.t.mem_heart_iff A.obj).mp A.property |>.1
  letI : h.t.IsLE (A.obj⟦(1 : ℤ)⟧) (-1) :=
    h.t.isLE_shift A.obj 0 1 (-1)
  have hH0shift : IsZero (h.H0prime (C := C) (A.obj⟦(1 : ℤ)⟧)) := by
    refine ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
    simpa [HeartStabilityData.H0prime, TStructure.truncLEGE] using
      (h.t.truncLE 0).map_isZero
        (h.t.isZero_truncGE_obj_of_isLE (-1) 0 (by lia)
          (A.obj⟦(1 : ℤ)⟧))
  have hzero : Srot.g = 0 := hH0shift.eq_of_tgt _ _
  letI : Epi Srot.f := hExact.epi_f hzero
  haveI hEpiMap : Epi ((h.H0primeFunctor (C := C)).map g) := by
    change Epi Srot.f
    infer_instance
  let hfg := comp_distTriang_mor_zero₁₂ (Triangle.mk f g δ) hT
  let d := h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g hfg
  haveI hEpiShortG :
      Epi (h.heartSourceH0primeShortComplex (C := C) A f g hfg).g := by
    change Epi ((h.H0primeFunctor (C := C)).map g)
    infer_instance
  haveI hEpiDesc : Epi d := by
    haveI : Epi
        (cokernel.π
            (h.heartSourceH0primeShortComplex (C := C) A f g hfg).f ≫ d) := by
      rw [h.heartSourceH0primeShortComplex_cokernelπ_comp_cokernelDesc
        (C := C) A f g hfg]
      exact hEpiShortG
    exact epi_of_epi
      (cokernel.π (h.heartSourceH0primeShortComplex (C := C) A f g hfg).f) d
  haveI hMonoDesc : Mono d :=
    h.mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional
      (C := C) A hT
  exact isIso_of_mono_of_epi d

/-- With homological `H⁰`, the exact obstruction is therefore discharged: the
canonical cokernel comparison is monic. -/
theorem HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc_of_H0Functor
    (h : HeartStabilityData C)
    [Functor.IsHomological (h.H0Functor (C := C))]
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    Mono (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
      (comp_distTriang_mor_zero₁₂ _ hT)) :=
  (h.heartSourceH0Complex_exact_iff_mono_cokernelDesc (C := C) A hT).mp
    (h.heartSourceH0Complex_exact_of_H0Functor_isHomological (C := C) A hT)

end

end CategoryTheory.Triangulated
