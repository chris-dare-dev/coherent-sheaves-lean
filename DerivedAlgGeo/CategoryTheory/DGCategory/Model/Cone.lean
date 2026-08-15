/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.DGCategory.IsCone
import DerivedAlgGeo.CategoryTheory.DGCategory.Model.Complexes

/-!
# `C^dg` has cones

`IsCone` is a structure with eleven fields, and — as `Instances.lean` says
about `DGCategory` itself — a structure with axioms is worth nothing until
something satisfies them. This file inhabits it: every cocycle in `C^dg A` has
a cone, namely Mathlib's `CochainComplex.mappingCone`.

The transcription is deliberate. `IsCone`'s relations were written by reading
Mathlib's `mappingCone` lemmas, so each field here is one of those lemmas and
nothing is re-derived. What the file has to supply is only the translation
between a closed degree-zero *cochain*, which is what a dg category's `cocycles`
gives, and the chain *map* that `mappingCone` takes as input — that is
`Cocycle.homOf`, and `Cocycle.cochain_ofHom_homOf_eq_coe` is what says the round
trip is the identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct Limits CochainComplex CochainComplex.HomComplex

namespace Cdg

variable {A : Type u} [Category.{v} A] [Preadditive A]

variable {K L : Cdg A} {f : (dgHom K L).X 0} (hf : f ∈ cocycles K L)

/-- The chain map a closed degree-zero cochain presents. -/
noncomputable def homOfCocycle : of A K ⟶ of A L :=
  Cocycle.homOf (Cocycle.mk f 1 (zero_add 1) hf)

/-- The round trip cochain to chain map and back is the identity, which is what
lets each field below be a Mathlib lemma with `f` in place of `ofHom (homOf f)`. -/
lemma ofHom_homOfCocycle : Cochain.ofHom (homOfCocycle hf) = f :=
  Cocycle.cochain_ofHom_homOf_eq_coe _

variable [HasBinaryBiproducts A]

/-- The mapping cone of `f`, as an object of `C^dg A`. -/
noncomputable def coneObj : Cdg A := mappingCone (homOfCocycle hf)

/-- **`C^dg` has cones.** Each field is the correspondingly named Mathlib lemma
about `mappingCone`; the only work is rewriting `Cochain.ofHom (homOf ⟨f, _⟩)`
back to `f`. -/
noncomputable def isCone : DGCategory.IsCone hf (coneObj hf) where
  inl := mappingCone.inl (homOfCocycle hf)
  inr := Cochain.ofHom (mappingCone.inr (homOfCocycle hf))
  fst := (mappingCone.fst (homOfCocycle hf)).1
  snd := mappingCone.snd (homOfCocycle hf)
  inl_fst := mappingCone.inl_fst _
  inl_snd := mappingCone.inl_snd _
  inr_fst := mappingCone.inr_fst _
  inr_snd := mappingCone.inr_snd _
  fst_inl_add_snd_inr := mappingCone.id _
  inr_cocycle := by
    change δ 0 1 (Cochain.ofHom (mappingCone.inr (homOfCocycle hf))) = 0
    simp
  fst_cocycle := by
    change δ 1 2 (mappingCone.fst (homOfCocycle hf)).1 = 0
    exact (mappingCone.fst (homOfCocycle hf)).2
  d_inl := by
    change δ (-1) 0 (mappingCone.inl (homOfCocycle hf)) = _
    rw [mappingCone.δ_inl, Cochain.ofHom_comp, ofHom_homOfCocycle]
    rfl
  d_snd := by
    change δ 0 1 (mappingCone.snd (homOfCocycle hf)) = _
    rw [mappingCone.δ_snd, ofHom_homOfCocycle]
    rfl

end Cdg

end CategoryTheory
