/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# The pretriangulated axioms, with rotation only forward

`Pretriangulated` states TR2 as an `↔`: a triangle is distinguished exactly
when its rotation is. Only the forward half is ever proved by a construction.
The reverse half is a *theorem* about the other four axioms, and this file
proves it, so a category that supplies the forward half supplies the class.

## The redundancy

`Axioms` bundles the five things a construction actually establishes:
isomorphism-closure, the contractible triangles, a cone on every morphism, the
forward rotation, and the completion of a square. `Axioms.mem_of_rotate_mem`
derives the reverse rotation from them, and `Axioms.pretriangulated` assembles
the class.

The proof is the classical one. Given `T.rotate` distinguished, take a cone
triangle `S` on `T.mor₁`; the completion axiom against `mor₂` -- itself the
completion axiom applied to rotations -- produces `φ : T.obj₃ ⟶ S.obj₃`
commuting with both remaining maps. `Hom(U, -)` is exact at the second vertex
of a distinguished triangle (`Axioms.coyoneda_exact₂`), and applying that to
the rotations of `T.rotate` and of `S` makes post-composition with `φ`
injective and surjective on every `Hom(U, -)`. So `φ` is an isomorphism,
`T ≅ S`, and `T` is distinguished.

Nothing here is circular: every exactness fact used is read off a triangle
already known to be distinguished -- `T.rotate` and its further rotations, or
`S` and its rotations -- never off `T` itself.

## Placement

Generic triangulated vocabulary. This file imports Mathlib alone, mentions no
dg category and no stability condition, and lives in Mathlib's
`CategoryTheory.Pretriangulated` namespace because everything it says is about
Mathlib's `Triangle` and `Pretriangulated`.

## The `backward` options

Mathlib sets both of these on the same lemmas (`comp_distTriang_mor_zero₁₂`,
`complete_distinguished_triangle_morphism₁`, the `coyoneda_exact` family). The
projections `(contractibleTriangle X).obj₂` and `T.rotate.mor₂` are definitional
but not reducible, so a hypothesis stated through them will not unify with the
same statement written directly without them. They are set for the file rather
than per declaration because every proof below is of that kind.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v u

namespace CategoryTheory

open Category Limits Preadditive Pretriangulated

namespace Pretriangulated

section Transport

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]

/-- **The lifting axiom transports along isomorphisms of triangles.**

A class of distinguished triangles is an isomorphism-closure, so the completion
axiom only ever has to be proved for the triangles that generate the class.
This is what moves it to the closure: `a` and `b` are conjugated into the
generators, the lift is conjugated back, and each of the two squares is the
corresponding square of the generators with four `Iso.hom_inv_id` cancellations
around it.

It asks for no more than a shift, so a construction can use it before it knows
its class satisfies `Axioms`. -/
lemma exists_lift_of_iso {T₁ T₂ S₁ S₂ : Triangle D} (e₁ : T₁ ≅ S₁) (e₂ : T₂ ≅ S₂)
    (H : ∀ (a' : S₁.obj₁ ⟶ S₂.obj₁) (b' : S₁.obj₂ ⟶ S₂.obj₂),
      S₁.mor₁ ≫ b' = a' ≫ S₂.mor₁ →
        ∃ c', S₁.mor₂ ≫ c' = b' ≫ S₂.mor₂ ∧
          S₁.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map a' = c' ≫ S₂.mor₃)
    (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂)
    (comm : T₁.mor₁ ≫ b = a ≫ T₂.mor₁) :
    ∃ c, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
      T₁.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map a = c ≫ T₂.mor₃ := by
  obtain ⟨c, hc₂, hc₃⟩ :=
    H (e₁.inv.hom₁ ≫ a ≫ e₂.hom.hom₁) (e₁.inv.hom₂ ≫ b ≫ e₂.hom.hom₂) (by
      simp only [Category.assoc, TriangleMorphism.comm₁_assoc]
      rw [← Category.assoc T₁.mor₁ b, comm, Category.assoc, e₂.hom.comm₁])
  refine ⟨e₁.hom.hom₃ ≫ c ≫ e₂.inv.hom₃, ?_, ?_⟩
  · simp only [TriangleMorphism.comm₂_assoc]
    rw [← Category.assoc S₁.mor₂ c, hc₂]
    simp
  · simp only [Category.assoc]
    rw [← TriangleMorphism.comm₃, ← Category.assoc c S₂.mor₃, ← hc₃]
    simp only [Category.assoc, ← Functor.map_comp]
    simp

end Transport

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive]

/-- The `Pretriangulated` axioms, with the rotation axiom weakened to its
forward direction only. -/
structure Axioms (triangles : Set (Triangle D)) : Prop where
  /-- a triangle isomorphic to a distinguished one is distinguished -/
  isomorphic : ∀ T₁ ∈ triangles, ∀ T₂ : Triangle D, (T₂ ≅ T₁) → T₂ ∈ triangles
  /-- the contractible triangles are distinguished -/
  contractible : ∀ X : D, contractibleTriangle X ∈ triangles
  /-- every morphism fits into a distinguished triangle -/
  cocone : ∀ {X Y : D} (f : X ⟶ Y),
    ∃ (Z : D) (g : Y ⟶ Z) (h : Z ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ triangles
  /-- the rotation of a distinguished triangle is distinguished -/
  rotate : ∀ T ∈ triangles, T.rotate ∈ triangles
  /-- a commuting square between the first two vertices extends to the third -/
  complete : ∀ (T₁ T₂ : Triangle D), T₁ ∈ triangles → T₂ ∈ triangles →
    ∀ (a : T₁.obj₁ ⟶ T₂.obj₁) (b : T₁.obj₂ ⟶ T₂.obj₂), T₁.mor₁ ≫ b = a ≫ T₂.mor₁ →
      ∃ c : T₁.obj₃ ⟶ T₂.obj₃, T₁.mor₂ ≫ c = b ≫ T₂.mor₂ ∧
        T₁.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map a = c ≫ T₂.mor₃

namespace Axioms

variable {triangles : Set (Triangle D)} (h : Axioms triangles)
include h

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- Consecutive morphisms of a distinguished triangle compose to zero. -/
lemma comp_eq_zero₁₂ (T : Triangle D) (hT : T ∈ triangles) : T.mor₁ ≫ T.mor₂ = 0 := by
  obtain ⟨c, hc, -⟩ := h.complete _ _ (h.contractible T.obj₁) hT (𝟙 T.obj₁) T.mor₁ rfl
  simpa only [contractibleTriangle_mor₂, zero_comp] using hc.symm

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- The completion axiom against `mor₂`: a square between the second and third
vertices extends backwards to the first. -/
lemma exists_lift₁ (T₁ T₂ : Triangle D) (hT₁ : T₁ ∈ triangles) (hT₂ : T₂ ∈ triangles)
    (b : T₁.obj₂ ⟶ T₂.obj₂) (c : T₁.obj₃ ⟶ T₂.obj₃) (comm : T₁.mor₂ ≫ c = b ≫ T₂.mor₂) :
    ∃ a : T₁.obj₁ ⟶ T₂.obj₁, T₁.mor₁ ≫ b = a ≫ T₂.mor₁ ∧
      T₁.mor₃ ≫ (CategoryTheory.shiftFunctor D (1 : ℤ)).map a = c ≫ T₂.mor₃ := by
  obtain ⟨a, ha₁, ha₂⟩ := h.complete _ _ (h.rotate _ hT₁) (h.rotate _ hT₂) b c comm
  refine ⟨(CategoryTheory.shiftFunctor D (1 : ℤ)).preimage a, ?_, ?_⟩
  · apply (CategoryTheory.shiftFunctor D (1 : ℤ)).map_injective
    dsimp at ha₂
    rw [neg_comp, comp_neg, neg_inj] at ha₂
    simpa only [Functor.map_comp, Functor.map_preimage] using! ha₂
  · simpa only [Functor.map_preimage] using! ha₁

omit [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] in
/-- `Hom(U, -)` is exact at the second vertex of a distinguished triangle. -/
lemma coyoneda_exact₂ (T : Triangle D) (hT : T ∈ triangles) {U : D} (u : U ⟶ T.obj₂)
    (hu : u ≫ T.mor₂ = 0) : ∃ v : U ⟶ T.obj₁, u = v ≫ T.mor₁ := by
  obtain ⟨a, ha₁, -⟩ := h.exists_lift₁ (contractibleTriangle U) T (h.contractible U) hT u 0
    (by simpa only [comp_zero] using hu.symm)
  have ha₁' : (𝟙 U : U ⟶ U) ≫ u = a ≫ T.mor₁ := ha₁
  rw [id_comp] at ha₁'
  exact ⟨a, ha₁'⟩

/-- **The reverse direction of the rotation axiom is redundant.** -/
theorem mem_of_rotate_mem (T : Triangle D) (hT : T.rotate ∈ triangles) : T ∈ triangles := by
  obtain ⟨W, g₀, δ, hS⟩ := h.cocone T.mor₁
  have hT2 : T.rotate.rotate ∈ triangles := h.rotate _ hT
  have hT3 : T.rotate.rotate.rotate ∈ triangles := h.rotate _ hT2
  have hS1 : (Triangle.mk T.mor₁ g₀ δ).rotate ∈ triangles := h.rotate _ hS
  have hS2 : (Triangle.mk T.mor₁ g₀ δ).rotate.rotate ∈ triangles := h.rotate _ hS1
  -- the comparison `φ : T.obj₃ ⟶ W`, from the completion axiom against `mor₂`
  obtain ⟨φ, hφ₁, hφ₂⟩ :
      ∃ φ : T.obj₃ ⟶ W, T.mor₃ ≫ 𝟙 (T.obj₁⟦(1 : ℤ)⟧) = φ ≫ δ ∧
        (-(T.mor₂⟦(1 : ℤ)⟧')) ≫ (φ⟦(1 : ℤ)⟧') = 𝟙 (T.obj₂⟦(1 : ℤ)⟧) ≫ (-(g₀⟦(1 : ℤ)⟧')) :=
    h.exists_lift₁ T.rotate.rotate (Triangle.mk T.mor₁ g₀ δ).rotate.rotate
      hT2 hS2 (𝟙 _) (𝟙 _) (by rw [comp_id, id_comp]; rfl)
  have hsq₃ : T.mor₃ = φ ≫ δ := by rw [← hφ₁, comp_id]
  have hsq₂ : T.mor₂ ≫ φ = g₀ := by
    apply (CategoryTheory.shiftFunctor D (1 : ℤ)).map_injective
    rw [neg_comp, id_comp, neg_inj] at hφ₂
    simpa only [Functor.map_comp] using hφ₂
  -- the zero compositions
  have hTz : T.mor₁ ≫ T.mor₂ = 0 := by
    apply (CategoryTheory.shiftFunctor D (1 : ℤ)).map_injective
    have hz := h.comp_eq_zero₁₂ _ hT3
    dsimp at hz
    rw [neg_comp, comp_neg, neg_neg] at hz
    simpa only [Functor.map_comp, Functor.map_zero] using! hz
  have hSz₂ : δ ≫ (-(T.mor₁⟦(1 : ℤ)⟧')) = 0 := h.comp_eq_zero₁₂ _ hS2
  -- the four exactness facts the chase uses
  have exT₃ : ∀ {U : D} (u : U ⟶ T.obj₃), u ≫ T.mor₃ = 0 → ∃ v : U ⟶ T.obj₂, u = v ≫ T.mor₂ :=
    fun u hu => h.coyoneda_exact₂ T.rotate hT u hu
  have exT₁ : ∀ {U : D} (u : U ⟶ T.obj₁⟦(1 : ℤ)⟧), u ≫ (-(T.mor₁⟦(1 : ℤ)⟧')) = 0 →
      ∃ v : U ⟶ T.obj₃, u = v ≫ T.mor₃ :=
    fun u hu => h.coyoneda_exact₂ T.rotate.rotate hT2 u hu
  have exS₂ : ∀ {U : D} (u : U ⟶ T.obj₂), u ≫ g₀ = 0 → ∃ v : U ⟶ T.obj₁, u = v ≫ T.mor₁ :=
    fun u hu => h.coyoneda_exact₂ (Triangle.mk T.mor₁ g₀ δ) hS u hu
  have exS₃ : ∀ {U : D} (u : U ⟶ W), u ≫ δ = 0 → ∃ v : U ⟶ T.obj₂, u = v ≫ g₀ :=
    fun u hu => h.coyoneda_exact₂ (Triangle.mk T.mor₁ g₀ δ).rotate hS1 u hu
  -- `φ` is injective and surjective on `Hom(U, -)`, hence an isomorphism
  have hinj : ∀ {U : D} (u : U ⟶ T.obj₃), u ≫ φ = 0 → u = 0 := by
    intro U u hu
    obtain ⟨v, hv⟩ := exT₃ u (by rw [hsq₃, ← assoc, hu, zero_comp])
    obtain ⟨w, hw⟩ := exS₂ v (by rw [← hsq₂, ← assoc, ← hv, hu])
    rw [hv, hw, assoc, hTz, comp_zero]
  have hsurj : ∀ {U : D} (u : U ⟶ W), ∃ v : U ⟶ T.obj₃, u = v ≫ φ := by
    intro U u
    obtain ⟨v, hv⟩ := exT₁ (u ≫ δ) (by rw [assoc, hSz₂, comp_zero])
    obtain ⟨w, hw⟩ := exS₃ (u - v ≫ φ) (by rw [sub_comp, assoc, ← hsq₃, ← hv, sub_self])
    refine ⟨v + w ≫ T.mor₂, ?_⟩
    rw [add_comp, assoc, hsq₂, ← hw]
    abel
  have : IsIso φ := by
    obtain ⟨ψ, hψ⟩ := hsurj (𝟙 W)
    refine ⟨ψ, ?_, hψ.symm⟩
    have hker := hinj (φ ≫ ψ - 𝟙 _) (by rw [sub_comp, assoc, ← hψ, comp_id, id_comp, sub_self])
    rwa [sub_eq_zero] at hker
  exact h.isomorphic _ hS _
    (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso φ) (by simp) (by simpa using hsq₂)
      (by simpa using hsq₃))

/-- **The `Pretriangulated` structure carried by a class of triangles satisfying
`Axioms`.** The rotation axiom's reverse direction is supplied by
`mem_of_rotate_mem`, so nothing beyond the forward one has to be proved. -/
@[reducible] def pretriangulated : Pretriangulated D where
  distinguishedTriangles := triangles
  isomorphic_distinguished := h.isomorphic
  contractible_distinguished := h.contractible
  distinguished_cocone_triangle := h.cocone
  rotate_distinguished_triangle T := ⟨h.rotate T, h.mem_of_rotate_mem T⟩
  complete_distinguished_triangle_morphism := h.complete

end Axioms

end Pretriangulated

end CategoryTheory
