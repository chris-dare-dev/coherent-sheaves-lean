/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.DGCategory.Cone

/-!
# When an object is a cone

`dg-enhancements-e5` (#376), third piece. `IsCone hf Z` says that `Z` is a cone
of the cocycle `f : X ⟶ Y` inside a dg category.

## Why this shape and not a natural isomorphism

The obvious definition is that `dgHom W Z ≅ coneHom hf W` naturally in `W`.
Naturality there means compatibility with pre-composition by an element of
`dgHom W' W` — and pre-composition by an element of degree `q` is a degree-`q`
map, not a map of complexes, so the condition has to be stated through
`shiftComp` and the functoriality of `coneHom` in a shifted variable. That is a
lot of machinery to express something the four structure maps already say.

So `IsCone` bundles `inl`, `inr`, `fst`, `snd` and their relations instead —
the one-sided twisted complex presentation. The relations are not invented
here: they are exactly the identities Mathlib proves about
`CochainComplex.mappingCone`, transcribed, so the model instance is obliged to
be a transcription rather than a re-derivation.

| here | Mathlib |
| --- | --- |
| `inl` | `mappingCone.inl : Cochain F (mappingCone φ) (-1)` |
| `inr` | `mappingCone.inr : G ⟶ mappingCone φ` |
| `fst` | `mappingCone.fst : Cocycle (mappingCone φ) F 1` |
| `snd` | `mappingCone.snd : Cochain (mappingCone φ) G 0` |
| `inl_fst`, `inl_snd`, `inr_fst`, `inr_snd` | the four lemmas of the same name |
| `fst_inl_add_snd_inr` | `mappingCone.id` |
| `d_inl` | `mappingCone.δ_inl` |
| `d_snd` | `mappingCone.δ_snd` |
| `fst_cocycle` | `fst` being a `Cocycle` |

Composition is diagrammatic on both sides, so no side of the table needs its
signs flipped. The one sign that is not `+1` is in `d_snd`, and it is Mathlib's.

## What this is for

`IsCone` is data, not a `Prop`: the four maps are structure. Uniqueness up to
canonical isomorphism is true and is not proved here — nothing downstream in
DG2 needs it yet, and asserting it in a docstring without a proof is the habit
this repository is trying not to have.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open DGCategoryStruct

namespace DGCategory

variable {C : Type u} [DGCategory.{v} C]

/-- `Z` is a cone of the cocycle `f : X ⟶ Y`: the four structure maps of a
mapping cone, together with the identities Mathlib proves for
`CochainComplex.mappingCone`. -/
structure IsCone {X Y : C} {f : (dgHom X Y).X 0} (_hf : f ∈ cocycles X Y) (Z : C) where
  /-- The degree `-1` inclusion of `X`. It is not closed; `d_inl` says what its
  differential is, and that is what makes the cone a *twisted* sum. -/
  inl : (dgHom X Z).X (-1)
  /-- The inclusion of `Y`, a closed degree-zero map. -/
  inr : (dgHom Y Z).X 0
  /-- The degree `1` projection to `X`, closed. -/
  fst : (dgHom Z X).X 1
  /-- The degree-zero projection to `Y`. Not closed; see `d_snd`. -/
  snd : (dgHom Z Y).X 0
  /-- `inl` followed by `fst` is the identity of `X`. -/
  inl_fst : dgComp (-1) 1 0 (by omega) inl fst = dgId X
  /-- `inl` followed by `snd` vanishes. -/
  inl_snd : dgComp (-1) 0 (-1) (by omega) inl snd = 0
  /-- `inr` followed by `fst` vanishes. -/
  inr_fst : dgComp 0 1 1 (by omega) inr fst = 0
  /-- `inr` followed by `snd` is the identity of `Y`. -/
  inr_snd : dgComp 0 0 0 (by omega) inr snd = dgId Y
  /-- The two projections and two inclusions decompose the identity of `Z`.
  This is what says `Z` is the sum and not merely a receptacle. -/
  fst_inl_add_snd_inr :
    dgComp 1 (-1) 0 (by omega) fst inl + dgComp 0 0 0 (by omega) snd inr = dgId Z
  /-- `inr` is closed. -/
  inr_cocycle : ((dgHom Y Z).d 0 1).hom inr = 0
  /-- `fst` is closed. -/
  fst_cocycle : ((dgHom Z X).d 1 2).hom fst = 0
  /-- **The twist.** `inl` is not closed: its differential is `f` followed by
  `inr`. Every difference between a cone and a direct sum is in this line. -/
  d_inl : ((dgHom X Z).d (-1) 0).hom inl = dgComp 0 0 0 (by omega) f inr
  /-- `snd` is not closed either, and this is the one relation carrying a sign.
  It is Mathlib's sign, from `mappingCone.δ_snd`. -/
  d_snd : ((dgHom Z Y).d 0 1).hom snd = -dgComp 1 0 1 (by omega) fst f

namespace IsCone

variable {X Y Z : C} {f : (dgHom X Y).X 0} {hf : f ∈ cocycles X Y} (hc : IsCone hf Z)

/-- **The composite `X → Y → Cone f` is a coboundary.** In `H⁰` it is therefore
zero, which is the first thing a triangle is required to satisfy. The proof is
`d_inl` read backwards: `inl` is the witness. -/
lemma comp_inr_mem_coboundaries : dgComp 0 0 0 (by omega) f hc.inr ∈ coboundaries X Z :=
  ⟨hc.inl, hc.d_inl⟩

/-- `inr` is a cocycle, in the subgroup form the `H⁰` machinery consumes. -/
lemma inr_mem_cocycles : hc.inr ∈ cocycles Y Z := hc.inr_cocycle

end IsCone

end DGCategory

end CategoryTheory
