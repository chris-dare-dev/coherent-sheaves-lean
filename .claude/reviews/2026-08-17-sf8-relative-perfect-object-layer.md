# SF8.1 relative-perfect object-layer review

Date: 2026-08-17

Source boundary: arXiv:2607.28411v1, Definitions 8.2, 8.4, and 8.5.

## Implemented boundary

- Total objects lie in the honest quasi-coherent-cohomology locus constructed
  in SF7; the ambient all-module-sheaf derived category is not renamed.
- Pseudo-coherence is the locally Noetherian cohomological criterion: bounded
  above with finitely presented cohomology in every degree.
- Local finite Tor amplitude is witnessed at every point by an actual open
  neighbourhood and a bounded complex whose terms are stalkwise flat over
  the base.  The chart includes the isomorphism to exact derived restriction.
- Relative-perfect and relative-perfect universally-gluable objects are full
  subcategories and both predicates are invariant under isomorphism.
- A geometric fiber is computed from an explicit global flat model.  Negative
  self-Ext vanishing is quantified in every integer degree below zero.
- The zero coherent complex supplies a nonempty relative-perfect and
  universally-gluable model.

## Deliberate limitations

- No general nonexact left-derived pullback is installed.
- The flat-model fiber is kept in the ambient derived category; this file does
  not claim that the entire ambient category is `Dqc` or manufacture the
  missing general pullback comparison.
- No pullback-preservation, openness, algebraicity, boundedness, or stack
  theorem is inferred from the object definitions.
- The general inherited `Dqc` structure, compact-equals-perfect theorem, and
  bounded-coherent equivalence continue in #528.
