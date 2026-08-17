# SF7.4 inducing-boundary cutover review

Date: 2026-08-17

Source boundary: arXiv:2607.28411v1, Theorem A.17 and Corollary A.23.

## Cutover

- The former global inducing-theorem proposition is deleted.
- Its bounded left-adjoint/zero-reflection/monad shadow is also deleted; those
  fields were not the hypotheses of the large-category theorem.
- `DerivedPullbackInducingData` and
  `BoundedCoherentPullbackInducingData` now contain
  `Slicing.InducedTStructures`, the phase-indexed t-structures and A.8
  recognition formulas produced by A.17.
- `Slicing.InducedTStructures.preimageData` supplies the Corollary-A.23 finite
  truncation argument and constructs the non-formal slicing witness.
- Natural-isomorphism transport of `InducedTStructures` supplies concrete
  unbounded and bounded-coherent inducing data for scheme identity pullback.
- The abstract bounded-coherent realization transports that constructed
  witness through its fiber equivalences. No family-level caller supplies a
  `Slicing.PreimageData` conclusion.

## Preserved consumers

- Concrete and bounded-coherent identity/composition laws are unchanged.
- `GeometricPreStabilityBaseChangeData` still exports the ordinary categorical
  base-change witness.
- Finite-type semistable openness, generic openness, and objectwise relative
  HN existence are rebuilt from that export without a global theorem
  parameter.

## Remaining geometric boundary

This cutover does not claim that flatness alone constructs the phase-indexed
A.17 output. The honest general-scheme Dqc realization, inherited
triangulated/coproduct structure, bounded-coherent equivalence,
compact-equals-perfect theorem, and generator-closure equality remain tracked
in #476.

## Validation

- focused inducing, geometric base-change, and finite-type modules build;
- the stability-condition axiom audit elaborates;
- the census reports zero unaudited public non-projection declarations.
