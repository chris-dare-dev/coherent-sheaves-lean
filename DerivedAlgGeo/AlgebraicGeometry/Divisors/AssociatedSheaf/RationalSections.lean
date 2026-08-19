/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.PicardGroup
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Cartier
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Module.MinimalAxioms

set_option backward.isDefEq.respectTransparency false

/-!
# The presheaf of rational sections on an integral scheme

This file owns the presheaf of rational functions on an integral scheme, as a
presheaf of modules over the structure presheaf.  Sections on an open are
proof-indexed: the function field on a nonempty open and the zero module on the
empty open, which makes restriction definitional.

Nothing here mentions divisors.  `AssociatedSheaf.Construction` builds the
fractional subpresheaf of a Cartier divisor inside this presheaf.
-/

open CategoryTheory Opposite TopologicalSpace MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- Rational sections on an open. The proof-indexed presentation is the function field on a
nonempty open and the zero module on the empty open. -/
abbrev RationalSections (U : X.Opens) := PLift (Nonempty U) → X.functionField

/-- Rational sections form an additive group pointwise. -/
noncomputable instance rationalSectionsAddCommGroup (U : X.Opens) :
    AddCommGroup (RationalSections X U) := inferInstance

/-- Rational sections carry the pointwise action of the sections of the
structure sheaf. -/
noncomputable instance rationalSectionsSMul (U : X.Opens) :
    SMul Γ(X, U) (RationalSections X U) where
  smul r s h := by
    letI : Nonempty U := h.down
    exact X.germToFunctionField U r * s h

/-- The pointwise action makes rational sections a module over the sections of
the structure sheaf. -/
noncomputable instance rationalSectionsModule (U : X.Opens) :
    Module Γ(X, U) (RationalSections X U) :=
  Module.ofMinimalAxioms
    (fun r s t ↦ by
      ext h
      letI : Nonempty U := h.down
      simp)
    (fun r s t ↦ by
      ext h
      letI : Nonempty U := h.down
      simp [Algebra.smul_def, add_mul])
    (fun r s t ↦ by
      ext h
      letI : Nonempty U := h.down
      simp [Algebra.smul_def, mul_assoc])
    (fun s ↦ by
      ext h
      letI : Nonempty U := h.down
      simp)

/-- The module structure on rational sections, stated for the bundled ring of
sections used by the presheaf-of-modules API. -/
noncomputable instance rationalSectionsModuleRingCat (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (RationalSections X U.unop) := by
  change Module Γ(X, U.unop) (RationalSections X U.unop)
  infer_instance

/-- Nonemptiness travels from a smaller open to a larger one. -/
theorem nonemptyOfLE {U V : X.Opens} (h : V ≤ U) : Nonempty V → Nonempty U :=
  fun hV ↦ ⟨⟨hV.some.1, h hV.some.2⟩⟩

/-- Restriction of rational sections. -/
def rationalSectionsRes {U V : X.Opens} (h : V ≤ U) :
    RationalSections X U →+ RationalSections X V where
  toFun s hV := s ⟨nonemptyOfLE X h hV.down⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restriction commutes with the germ map to the function field. -/
lemma germToFunctionField_res {U V : X.Opens} (h : V ≤ U)
    (r : Γ(X, U)) (hV : PLift (Nonempty V)) :
    letI : Nonempty U := nonemptyOfLE X h hV.down
    letI : Nonempty V := hV.down
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op r) =
      X.germToFunctionField U r := by
  letI : Nonempty U := nonemptyOfLE X h hV.down
  letI : Nonempty V := hV.down
  let x : X := hV.down.some.1
  let hxV : x ∈ V := hV.down.some.2
  have hxU : x ∈ U := h hxV
  rw [← X.algebraMap_germ_eq_germToFunctionField hxV,
    ← X.algebraMap_germ_eq_germToFunctionField hxU]
  rw [X.presheaf.germ_res_apply]

/-- Restriction of rational sections is semilinear over restriction of
structure-sheaf sections. -/
lemma rationalSectionsRes_smul {U V : X.Opens} (h : V ≤ U)
    (r : Γ(X, U)) (s : RationalSections X U) :
    rationalSectionsRes X h (r • s) =
      X.presheaf.map (homOfLE h).op r • rationalSectionsRes X h s := by
  ext hV
  letI : Nonempty U := nonemptyOfLE X h hV.down
  letI : Nonempty V := hV.down
  change X.germToFunctionField U r * s ⟨nonemptyOfLE X h hV.down⟩ =
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op r) *
      s ⟨nonemptyOfLE X h hV.down⟩
  rw [germToFunctionField_res X h r hV]

/-- The presheaf of rational functions, as modules over the structure presheaf. -/
noncomputable def rationalPresheaf : X.PresheafOfModules where
  obj U := ModuleCat.of _ (RationalSections X U.unop)
  map {U V} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map f).hom).obj
      (ModuleCat.of _ (RationalSections X V.unop)))
    { toFun := rationalSectionsRes X (leOfHom f.unop)
      map_add' := map_add _
      map_smul' := by
        intro r s
        change rationalSectionsRes X (leOfHom f.unop) (r • s) =
          (X.ringCatSheaf.obj.map f r : X.ringCatSheaf.obj.obj V) •
            rationalSectionsRes X (leOfHom f.unop) s
        rw [show f = (homOfLE (leOfHom f.unop)).op by subsingleton]
        exact rationalSectionsRes_smul X (leOfHom f.unop) r s }
  map_id U := by
    ext s
    rfl
  map_comp f g := by
    ext s
    rfl

end AlgebraicGeometry.Scheme
