/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.AlgebraicGeometry.Restrict

/-!
# The restriction square, read on opens

`#572` step 2 globalizes `isCoherent_pushforward_of_surjective` along an affine cover, and the
criterion it feeds (`Modules.isCoherent_iff_restrict_affineOpenCover`) asks for
`(ι_* F).restrict (𝒰.f i)` while the affine theorem produces the pushforward along
`ι ∣_ V`. Comparing the two is a base-change statement about the square

```
  f ⁻¹ᵁ U  ──(f ⁻¹ᵁ U).ι──>  X
     │                        │
  f ∣_ U                      f
     │                        │
     U   ─────U.ι─────────>   Y
```

This file records the geometric half of that comparison: the two ways round the square agree
as functors on opens.

## Why this is the whole geometric content

Both composites send an open `V` of `U` to the preimage of `V` under `f`, viewed in `X` —
`image_morphismRestrict_preimage` is exactly that equality, and it is at the pin. `Opens` is a
poset, so a natural transformation between functors into it is determined by nothing at all:
agreement on objects *is* the isomorphism, and `NatIso.ofComponents` discharges naturality
because the naturality squares live in a subsingleton.

## What this file does not do

It does not build the comparison of sheaves of modules,
`pushforward f ⋙ restrictFunctor U.ι ≅ restrictFunctor (f ⁻¹ᵁ U).ι ⋙ pushforward (f ∣_ U)`.
That construction sits on top of this one via `SheafOfModules.pushforwardNatIso` and
`pushforwardCongr`, and it is not claimed here: its remaining obligation is an equality of
sheaf-of-rings data that has not been proved. Nothing below depends on it.
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

/-- **The restriction square commutes on opens.** Going round by `U.ι` and then taking the
preimage under `f` is going round by `f ∣_ U` and then taking the image in `X`.

This is `image_morphismRestrict_preimage` packaged as an isomorphism of the two composite
functors `Opens U ⥤ Opens X`, which is the form the base-change comparison of pushforwards
consumes. -/
noncomputable def restrictSquareOpensIso :
    U.ι.opensFunctor ⋙ Opens.map f.base ≅
      Opens.map (f ∣_ U).base ⋙ (f ⁻¹ᵁ U).ι.opensFunctor :=
  NatIso.ofComponents (fun V ↦ eqToIso (image_morphismRestrict_preimage f U V).symm)

end AlgebraicGeometry
