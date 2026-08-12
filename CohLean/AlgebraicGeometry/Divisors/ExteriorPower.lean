/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CohLean.AlgebraicGeometry.Divisors.Tensor
import CohLean.AlgebraicGeometry.Modules.ExteriorPower

/-!
# Restriction and exterior powers

This file compares restriction of a sheaf exterior power with the sheafification of the
objectwise exterior power on the restricted site.
-/

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

local instance exteriorPowerRestrictionCategory : Category X.Modules :=
  inferInstanceAs (Category (SheafOfModules X.ringCatSheaf))

private abbrev overPresheafFunctor (X : Scheme.{u}) (U : X.Opens) :=
  PresheafOfModules.pushforward (𝟙 (X.ringCatSheaf.over U).obj)

/-- On an open slice, sheafify the objectwise exterior power of the restricted sheaf. -/
noncomputable def exteriorPowerOver (E : X.Modules) (U : X.Opens) (n : ℕ) :
    SheafOfModules (X.ringCatSheaf.over U) :=
  (PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)).obj
      (PresheafOfModules.exteriorPower (X.sheaf.over U).obj
        ((SheafOfModules.forget (X.ringCatSheaf.over U)).obj (E.over U)) n)

set_option maxHeartbeats 6400000 in
/-- Restricting an objectwise exterior-power presheaf is the objectwise exterior power of the
restricted presheaf. -/
noncomputable def overExteriorPowerPresheafIso
    (P : X.PresheafOfModules) (U : X.Opens) (n : ℕ) :
    (overPresheafFunctor X U).obj
        (PresheafOfModules.exteriorPower X.presheaf P n) ≅
      PresheafOfModules.exteriorPower (X.sheaf.over U).obj
        ((overPresheafFunctor X U).obj P) n :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _) (by
    intro V W f
    rfl)

/-- Restriction of a sheaf exterior power agrees with the exterior power formed on the open
slice. -/
noncomputable def exteriorPowerOverIso (E : X.Modules) (U : X.Opens) (n : ℕ) :
    (exteriorPower E n).over U ≅ exteriorPowerOver E U n := by
  let P := (SheafOfModules.forget X.ringCatSheaf).obj E
  let aU := PresheafOfModules.sheafification
    (𝟙 (X.ringCatSheaf.over U).obj)
  let c := overSheafificationComparison
    (PresheafOfModules.exteriorPower X.presheaf P n) U
  exact (@asIso _ _ _ _ c (isIso_overSheafificationComparison _ _)).symm ≪≫
    aU.mapIso (overExteriorPowerPresheafIso P U n)

end

end AlgebraicGeometry.Scheme.Modules
