/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.FlatPullback
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Families.DerivedPullbackCoherence
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Phase.Transfer.InducingBoundary

/-!
# Inducing data for scheme-derived pullback

This file connects the concrete exact derived pullback on scheme fibers to the
honest preimage-slicing boundary.  A `DerivedPullbackInducingData` records a
functor left adjoint to the detecting functor
`SchemeBaseChange.derivedPullback f`, zero reflection, and the phase-monad
condition from `Slicing.LeftAdjointInducingPremise`.

Those bounded categorical premises do not prove the existence of the
preimage slicing by themselves.  The conversion therefore still takes
`HasLeftAdjointInducingTheorem` explicitly; this repository supplies no
inhabitant until the presentable/Ind and boundedness-reflection argument has
been formalized.  Flatness is used only to install exact derived pullback.
It supplies none of the inducing premises.

Once explicit preimage data has been obtained, identity and composition use
the coherence from `Phase.Transfer.Basic` and the exact derived-pullback unit
and compositor.  No geometric slicing, openness, relative HN, bounded
coherent/perfect restriction, or conclusion of Theorem 22.2 is asserted.
-/

namespace CategoryTheory.Triangulated.StabilityCondition.Families

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated AlgebraicGeometry

noncomputable section

universe u

namespace SchemeBaseChange

variable {S : Scheme.{u}}

/-- Explicit preimage-slicing data for the concrete exact derived pullback
along one morphism of scheme base changes. -/
structure DerivedPullbackPreimageData {T U : SchemeBaseChange S}
    (f : T ⟶ U) [IsExactPullback f]
    (s : Slicing T.DerivedFiber) : Prop where
  /-- The two non-formal slicing axioms for detecting phases by derived
  pullback. -/
  preimageData : s.PreimageData (derivedPullback f)

namespace DerivedPullbackPreimageData

variable {T U : SchemeBaseChange S} {f : T ⟶ U} [IsExactPullback f]
  {s : Slicing T.DerivedFiber}

/-- The slicing on the target derived fiber constructed from the explicit
preimage witness. -/
def preimage (h : DerivedPullbackPreimageData f s) : Slicing U.DerivedFiber :=
  s.preimage (derivedPullback f) h.preimageData

/-- Exact derived pullback along an identity carries the canonical identity
preimage witness across the derived unit isomorphism. -/
theorem identity (T : SchemeBaseChange S) (s : Slicing T.DerivedFiber) :
    DerivedPullbackPreimageData (f := 𝟙 T) s where
  preimageData :=
    s.preimageData_id.ofIso (derivedPullbackId T).symm

/-- The slicing induced through exact derived pullback along an identity is
the original slicing. -/
@[simp]
theorem preimage_identity (T : SchemeBaseChange S)
    (s : Slicing T.DerivedFiber) :
    (identity T s).preimage = s := by
  calc
    (identity T s).preimage =
        s.preimage (Functor.id T.DerivedFiber) s.preimageData_id :=
      Slicing.preimage_iso s _ _ s.preimageData_id
        (derivedPullbackId T).symm
    _ = s := s.preimage_id

/-- Explicit derived-pullback preimage witnesses compose and are transported
from the iterated functor to pullback along the composite by the derived
compositor. -/
theorem comp {T U V : SchemeBaseChange S} (f : T ⟶ U) (g : U ⟶ V)
    [IsExactPullback f] [IsExactPullback g]
    {s : Slicing T.DerivedFiber}
    (hf : DerivedPullbackPreimageData f s)
    (hg : DerivedPullbackPreimageData g hf.preimage) :
    DerivedPullbackPreimageData (f ≫ g) s where
  preimageData :=
    (hf.preimageData.comp hg.preimageData).ofIso
      (derivedPullbackComp f g)

/-- The slicing induced along a composite exact derived pullback agrees with
the slicing obtained in two stages. -/
@[simp]
theorem preimage_comp {T U V : SchemeBaseChange S}
    (f : T ⟶ U) (g : U ⟶ V)
    [IsExactPullback f] [IsExactPullback g]
    {s : Slicing T.DerivedFiber}
    (hf : DerivedPullbackPreimageData f s)
    (hg : DerivedPullbackPreimageData g hf.preimage) :
    (hf.comp f g hg).preimage = hg.preimage := by
  calc
    (hf.comp f g hg).preimage =
        s.preimage (derivedPullback g ⋙ derivedPullback f)
          (hf.preimageData.comp hg.preimageData) :=
      Slicing.preimage_iso s _ _
        (hf.preimageData.comp hg.preimageData)
        (derivedPullbackComp f g)
    _ = hg.preimage := Slicing.preimage_comp s _ _ _ _

end DerivedPullbackPreimageData

/-- The bounded left-adjoint inducing premises specialized to the concrete
exact derived pullback functor.

The orientation is part of the type: `leftAdjoint` goes from the source
derived fiber to the target derived fiber and satisfies
`leftAdjoint ⊣ derivedPullback f`.  No existence claim is made. -/
structure DerivedPullbackInducingData {T U : SchemeBaseChange S}
    (f : T ⟶ U) [IsExactPullback f]
    (s : Slicing T.DerivedFiber) where
  /-- A proposed left adjoint to the derived pullback used to detect phases. -/
  leftAdjoint : T.DerivedFiber ⥤ U.DerivedFiber
  /-- Adjunction, zero reflection, and the phase-monad condition in the exact
  functor orientation above. -/
  premise : s.LeftAdjointInducingPremise (derivedPullback f) leftAdjoint

namespace DerivedPullbackInducingData

variable {T U : SchemeBaseChange S} {f : T ⟶ U} [IsExactPullback f]
  {s : Slicing T.DerivedFiber}

/-- Convert the bounded inducing package to explicit preimage-slicing data
only when the still-missing presentable/Ind theorem is supplied. -/
theorem toPreimageData (h : DerivedPullbackInducingData f s)
    (H : HasLeftAdjointInducingTheorem.{u + 1, u + 1, u + 1, u + 1}) :
    DerivedPullbackPreimageData f s where
  preimageData := H s (derivedPullback f) h.leftAdjoint h.premise

/-- For a flat scheme morphism, Mathlib flatness supplies exact derived
pullback and nothing more.  The inducing package and the presentable/Ind
theorem remain explicit inputs. -/
theorem toPreimageData_of_flat {T U : SchemeBaseChange S}
    (f : T ⟶ U) [Flat f.left] (s : Slicing T.DerivedFiber)
    (h : DerivedPullbackInducingData f s)
    (H : HasLeftAdjointInducingTheorem.{u + 1, u + 1, u + 1, u + 1}) :
    DerivedPullbackPreimageData f s :=
  h.toPreimageData H

end DerivedPullbackInducingData

end SchemeBaseChange

end

end CategoryTheory.Triangulated.StabilityCondition.Families
