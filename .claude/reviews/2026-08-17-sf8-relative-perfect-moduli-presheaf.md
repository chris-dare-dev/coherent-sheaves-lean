# SF8.2 relative-perfect moduli-presheaf review

Date: 2026-08-17

Issue boundary: #518, after the SF8.1 object layer in #521.

## Implemented boundary

- A fiber over an actual scheme base change is the core of the
  universally-gluable relative-perfect category, so every arrow is an
  isomorphism.
- A relative-perfect moduli problem contains a Mathlib `Pseudofunctor` on a
  contravariant diagram of scheme base changes. The pseudofunctor, rather than
  ad hoc equations, owns the unit, compositor, triangle, and pentagon laws.
- Every pseudofunctor fiber is equivalent to the concrete relative-perfect
  core. Every transition comes with a natural isomorphism to the repository's
  exact derived pullback after forgetting to the ambient derived categories;
  this comparison covers objects and morphisms.
- Isomorphism classes and geometric-point fibers are exposed directly.
- The zero complex gives concrete objects in locally Noetherian fibers. The
  constant identity diagram supplies a nonempty coherent moduli problem and
  uses the proved derived-pullback identity comparison.

## Deliberate limitations

- The interface accepts only transition data whose exactness and ambient
  comparison have been proved. It does not manufacture preservation of
  pseudo-coherence, finite Tor amplitude, or negative Ext along an arbitrary
  scheme morphism.
- The identity model proves nonvacuity but makes no claim about nonidentity
  geometric pullback.
- Descent, algebraicity, boundedness, Quot representability, and good-moduli
  statements are not part of this file.
- The remaining general-scheme Dqc identifications continue in #528. Stack
  descent starts in SF9 issue #523.
