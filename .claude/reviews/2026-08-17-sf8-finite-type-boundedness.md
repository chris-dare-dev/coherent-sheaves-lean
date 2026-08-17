# SF8.3 finite-type boundedness review

Date: 2026-08-17

Issue boundary: #519, after the relative-perfect object and pseudofunctor
layers from #521 and #518.

## Implemented boundary

- `RelativePerfectModuliSubproblem` separates admissible total families from
  the geometric objects that must be covered. Both predicates are invariant
  under actual isomorphisms in the relative-perfect moduli groupoids.
- `FiniteTypeBoundednessWitness` stores an actual object of `Over S`; its
  structure morphism is locally of finite type and quasi-compact. It also
  stores a universally-gluable relative-perfect universal family, membership
  in the selected family subfunctor, explicit residue-field fibers, and
  geometric coverage up to isomorphism.
- Coverage transports objects only after an equality of the actual
  residue-field base changes. It does not identify unrelated fiber
  categories or postulate a general derived-pullback theorem.
- Boundedness is monotone when admitted total families are enlarged and the
  requested geometric locus is restricted.
- `relativePerfectGeometricBoundednessProblem` is the direct adapter to the
  existing Definition 21.15(5) API. Its predicate is `Nonempty` finite-type
  witness data, not a caller-selected proposition.
- The identity scheme over a locally Noetherian base, carrying the zero
  universally-gluable relative-perfect complex, gives a concrete witness.
  The same construction is available after every base change with locally
  Noetherian source.

## Deliberate limitations

- General derived restriction of a nonzero universal family to arbitrary
  residue-field morphisms is not yet constructed. The witness therefore
  records supported geometric fibers explicitly.
- The zero model proves the interface nonvacuous but does not establish
  boundedness of a nonzero semistable locus.
- No Quot scheme, parameter space for nonzero bounded complexes, atlas,
  diagonal, algebraic-stack, semistable-reduction, or good-moduli result is
  claimed. The first nonzero parameter realization is SF8.4 #520.
