# S4 — `ProjectiveVariety` landed; the cohomology invariance measured, 2026-08-17 (UTC)

For #572 (S4, split from #332). This note records what the first slice proves, and what the
remaining two steps actually cost, measured against the pin rather than estimated.

## What landed

`DerivedAlgGeo/AlgebraicGeometry/Variety/Projective.lean` — step 1 of the issue, complete:

* `ProjectiveVariety k` extends `Variety k` with an index type, `Finite`, a morphism to
  `Proj (MvPolynomial.homogeneousSubmodule index k)`, `IsClosedImmersion`, and the compatibility
  `embedding ≫ projectiveSpaceToSpec = structureMorphism`.
* `homogeneousZeroRingEquiv : R ≃+* ↥(𝒜 0)` — the identification of the base ring with the
  degree-zero part, so `Proj.toSpecZero`'s target can be named `Spec k`.
* `projectiveSpaceToSpec`, with `IsProper` for finite index sets.
* `IsProper X.structureMorphism`, `IsNoetherian X.toScheme`, `X.toScheme.IsSeparated` — all
  **derived**, none of them fields.

The properness chain is the point. `SmoothProperVariety` takes properness as a field because
nothing produced it; here `Proj.toSpecZero` is proper at the pin given
`Algebra.FiniteType (𝒜 0) A` (`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:368`), a
closed immersion is finite hence proper, and `overBase` says the structure morphism is their
composite. A projective variety is proper *because* it is projective.

## Two things the pin did not supply, and what they cost

**`Algebra.FiniteType ↥(𝒜 0) (MvPolynomial ι k)` is not an instance.** It is derivable —
`Algebra.FiniteType.of_restrictScalars_finiteType` along `k → 𝒜₀ → k[ι]` — but the scalar tower
`IsScalarTower R ↥(𝒜 0) (MvPolynomial ι R)` is *also* not registered, even though both algebra
structures are Mathlib's own (`SetLike.GradeZero.instAlgebra` and the subobject coercion) and the
tower is `rfl`. Both are in the file, the tower as a local instance. The general form —
`IsScalarTower S (𝒜 0) A` for any internally graded algebra — is `upstream-candidate` material and
is not claimed here.

A dead end worth recording: defining `Algebra R ↥(𝒜 0)` by hand from the ring equiv looks natural
and is wrong. `𝒜 0` is a `Submodule R A` and already carries an `R`-action; a second one built
from `RingHom.toAlgebra` produces a `SMul` diamond, and the tower then fails to typecheck against
the expected `Submodule.smul`. Use Mathlib's instance.

**Steps 2 and 3 of #572 are not started, and should not be folded into this PR.**

* *Step 2, `ι_* F` coherent.* `Scheme.Modules.pushforward` exists at the pin
  (`Mathlib/AlgebraicGeometry/Modules/Tilde.lean:529` uses it), so there is a functor to state the
  claim about. Coherence of the pushforward is not there and is an affine-local finite-generation
  argument over the closed immersion's `Spec` charts.
* *Step 3, `Hⁱ(X, F) ≅ Hⁱ(Pⁿ, ι_* F)`.* Neither exactness nor acyclicity of a closed-immersion
  pushforward is in the tree or at the pin, and the comparison has to be stated against the small
  site's `Sheaf.H` with the `HasExt` universe kept a parameter — the same convention hazard #569
  records for the Čech side. This is the real content of the issue and it is a lane of its own.

## Placement

The module imports Mathlib only, not `Proj/Modules/Finiteness.lean`, so the variety layer stays
independent of the Proj Čech-comparison stack (CLAUDE.md: *keep generic layers independent of
specialized geometric applications*). The grading is spelled `MvPolynomial.homogeneousSubmodule`,
which is by definition `AlgebraicGeometry.Proj.polynomialGrading`; statements in either spelling
compose.

The audit records went to a new slice, `scripts/AlgebraicGeometryAudit/Projective.lean`, rather
than into `Core.lean` — #480's reason exactly: `Core.lean` is being appended by #567 and #574 at
the same time. The structure's fields are listed individually, since the fields are the trust
boundary.
