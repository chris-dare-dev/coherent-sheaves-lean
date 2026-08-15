/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Determinant
import DerivedAlgGeo.AlgebraicGeometry.Divisors.Dual

/-!
# Line-bundle data from an intrinsically invertible sheaf

`LineBundleData` (in `Divisors.Determinant`) packages an invertible sheaf together with an
explicit tensor inverse. `dualLine` (in `Divisors.Dual`) produces such an inverse. This file
is the one place where the two meet.

## Why this is its own file

It is the *only* thing in `Divisors.Dual` that ever needed `Divisors.Determinant`: three names
out of the thirty-seven that file declares, in eleven lines out of seven hundred and forty. That
one edge put `Dual` downstream of `Determinant`, and so downstream of `ExteriorPower`, which is
the single most expensive module in the repository. Lifting the edge into a leaf costs one file
and buys two things:

* the cold-build critical path drops from 1219s to 1041s, because `Dual` no longer waits on
  `ExteriorPower` and the two elaborate in parallel;
* a change to `ExteriorPower` rebuilds 271s of downstream work instead of 507s, and a change to
  `Determinant` 187s instead of 423s.

Keep this file a leaf. Anything added here that does not genuinely need *both* `Determinant` and
`Dual` belongs in whichever of them it actually depends on, or the edge comes back.
-/

universe u

open CategoryTheory TopologicalSpace Opposite MonoidalCategory

-- As in `Divisors.Dual`, from which this declaration came.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

noncomputable section

/-- Upgrade an intrinsically invertible sheaf to line-bundle data with an
explicit sheafified-dual tensor inverse. -/
noncomputable def LineBundleData.ofIsInvertible (L : X.Modules)
    [hL : SheafOfModules.IsInvertible.{u, u, u}
      (show SheafOfModules X.ringCatSheaf from L)] : LineBundleData X where
  line := L
  inverse := dualLine L
  lineIsInvertible := hL
  inverseIsInvertible := dualLine_isInvertible L
  tensorInverseIso := tensorDualIso L

end

end AlgebraicGeometry.Scheme.Modules
