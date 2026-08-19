/-
Projective-variety slice of the AlgebraicGeometry audit, split out so concurrent
branches append to different files (#480). See the umbrella file for the contract.
-/
import DerivedAlgGeo.AlgebraicGeometry.CoherentSheaf.Pushforward
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

-- A presentation is genuine projective data on one fixed variety; projectivity forgets the
-- chosen embedding, and properness follows from the resulting proposition.
#print axioms AlgebraicGeometry.ProjectivePresentation
#print axioms AlgebraicGeometry.ProjectivePresentation.instFiniteIndex
#print axioms AlgebraicGeometry.ProjectivePresentation.instIsClosedImmersionEmbedding
#print axioms AlgebraicGeometry.ProjectivePresentation.isProper_structureMorphism
#print axioms AlgebraicGeometry.Variety.IsProjective
#print axioms AlgebraicGeometry.Variety.IsProjective.ofPresentation
#print axioms AlgebraicGeometry.Variety.isProper_of_isProjective
#print axioms AlgebraicGeometry.ProjectiveVariety
#print axioms AlgebraicGeometry.ProjectiveVariety.toVariety
#print axioms AlgebraicGeometry.ProjectiveVariety.instIsProjective
#print axioms AlgebraicGeometry.ProjectiveVariety.ofPresentation

-- The presentation's fields and elaborator artifacts. Listed rather than left to the ceiling:
-- the fields *are* the trust boundary here — `embedding`, `isClosedImmersion` and `overBase` are
-- what "projective" means in this repository — so they should be visible in the audit alongside
-- the theorems that consume them.
#print axioms AlgebraicGeometry.ProjectivePresentation.index
#print axioms AlgebraicGeometry.ProjectivePresentation.finiteIndex
#print axioms AlgebraicGeometry.ProjectivePresentation.embedding
#print axioms AlgebraicGeometry.ProjectivePresentation.isClosedImmersion
#print axioms AlgebraicGeometry.ProjectivePresentation.overBase
#print axioms AlgebraicGeometry.ProjectivePresentation.mk.inj
#print axioms AlgebraicGeometry.ProjectivePresentation.mk.sizeOf_spec
#print axioms AlgebraicGeometry.Variety.IsProjective.presentation

-- Step 2 of #572, affine case: coherence survives pushforward along `Spec.map` of a surjection.
-- The tilde identification is the content; the finiteness is a tower argument.
#print axioms AlgebraicGeometry.gammaPushforwardIso
#print axioms AlgebraicGeometry.moduleFinite_gammaPushforward
#print axioms AlgebraicGeometry.isCoherent_pushforward_of_surjective

-- The restriction square on opens (#572 step 2, base-change half).
#print axioms AlgebraicGeometry.restrictSquareOpensIso
