/-
Projective-variety slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract.
-/
import DerivedAlgGeo.AlgebraicGeometry.Variety.Projective
open AlgebraicGeometry

-- The base field is the degree-zero part of the standard graded polynomial ring. The
-- identification is constructed from `C` and `constantCoeff`, so `Proj.toSpecZero`'s target can be
-- named as `Spec k` without a defeq coincidence.
#print axioms AlgebraicGeometry.homogeneousZeroRingEquiv
#print axioms AlgebraicGeometry.homogeneousZeroRingEquiv_apply_coe
#print axioms AlgebraicGeometry.isScalarTower_homogeneousZero
#print axioms AlgebraicGeometry.finiteType_homogeneousZero

-- Projective space and its structure morphism to the base field, with properness derived from
-- Mathlib's `IsProper (Proj.toSpecZero 𝒜)` rather than assumed.
#print axioms AlgebraicGeometry.projectiveSpace
#print axioms AlgebraicGeometry.projectiveSpaceToSpec
#print axioms AlgebraicGeometry.isProper_projectiveSpaceToSpec

-- The projective bundle `Variety/Basic.lean` said was missing: genuine projective data, not
-- properness renamed. Properness, noetherianity and separatedness are consequences here.
#print axioms AlgebraicGeometry.ProjectiveVariety
#print axioms AlgebraicGeometry.ProjectiveVariety.instFiniteIndex
#print axioms AlgebraicGeometry.ProjectiveVariety.instIsClosedImmersionEmbedding
#print axioms AlgebraicGeometry.ProjectiveVariety.isProper_structureMorphism
#print axioms AlgebraicGeometry.ProjectiveVariety.isNoetherian
#print axioms AlgebraicGeometry.ProjectiveVariety.isSeparated

-- The structure's own fields and elaborator artifacts. Listed rather than left to the ceiling:
-- the fields *are* the trust boundary here — `embedding`, `isClosedImmersion` and `overBase` are
-- what "projective" means in this repository — so they should be visible in the audit alongside
-- the theorems that consume them.
#print axioms AlgebraicGeometry.ProjectiveVariety.toVariety
#print axioms AlgebraicGeometry.ProjectiveVariety.index
#print axioms AlgebraicGeometry.ProjectiveVariety.finiteIndex
#print axioms AlgebraicGeometry.ProjectiveVariety.embedding
#print axioms AlgebraicGeometry.ProjectiveVariety.isClosedImmersion
#print axioms AlgebraicGeometry.ProjectiveVariety.overBase
#print axioms AlgebraicGeometry.ProjectiveVariety.mk.inj
#print axioms AlgebraicGeometry.ProjectiveVariety.mk.sizeOf_spec
