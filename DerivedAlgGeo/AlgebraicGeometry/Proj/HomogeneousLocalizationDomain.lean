/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.Localization.Defs

/-!
# Homogeneous localizations of a graded domain

`HomogeneousLocalization 𝒜 S` is by construction a subring of the ordinary localization
`Localization S`, through the injective map `HomogeneousLocalization.val`. So when the ambient
ring is a domain and `S` avoids zero, the homogeneous localization is a domain too.

This is the ring-theoretic input to irreducibility and reducedness of `Proj 𝒜`: the standard
affine charts of `Proj` are spectra of the degree-zero homogeneous localizations
`HomogeneousLocalization.Away 𝒜 f`, and those charts are irreducible and reduced exactly because
those rings are domains.
-/

open scoped nonZeroDivisors

namespace HomogeneousLocalization

variable {ι σ A : Type*} [AddCommMonoid ι] [DecidableEq ι] [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- A homogeneous localization at a multiplicative set of nonzerodivisors is a domain, provided
it is nontrivial. -/
theorem isDomain_of_le_nonZeroDivisors [IsDomain A] (S : Submonoid A)
    (hS : S ≤ A⁰) [Nontrivial (HomogeneousLocalization 𝒜 S)] :
    IsDomain (HomogeneousLocalization 𝒜 S) := by
  haveI : IsDomain (Localization S) := IsLocalization.isDomain_localization hS
  exact Function.Injective.isDomain
    (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S)) (val_injective S)

/-- The degree-zero homogeneous localization away from a nonzero element of a graded domain is a
domain, provided it is nontrivial. -/
theorem Away.isDomain [IsDomain A] {f : A} (hf : f ≠ 0)
    [Nontrivial (HomogeneousLocalization.Away 𝒜 f)] :
    IsDomain (HomogeneousLocalization.Away 𝒜 f) := by
  refine isDomain_of_le_nonZeroDivisors 𝒜 (Submonoid.powers f) ?_
  rintro _ ⟨n, rfl⟩
  exact pow_mem (mem_nonZeroDivisors_of_ne_zero hf) n

end HomogeneousLocalization
