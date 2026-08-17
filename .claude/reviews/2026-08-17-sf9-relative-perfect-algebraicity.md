# SF9 relative-perfect algebraicity review

Issue: #522 (partial; remains open)

## Delivered

- A selected relative-perfect moduli fiber is now the actual full subgroupoid
  cut out by the SF8 family predicate.
- `RelativePerfectAlgebraicPresentation` pairs an actual algebraic stack over
  the base with equivalences from its supported locally Noetherian fibers to
  those selected relative-perfect groupoids.
- `BoundedRelativePerfectAlgebraicPresentation` links the same presentation
  to an actual SF8 finite-type boundedness witness. Its universal family is
  lifted to an object of the corresponding stack fiber, and the counit gives
  the comparison isomorphism back to the original family.
- Open relative-perfect presentations contain an actual representable open
  immersion and a pointwise commuting structural triangle over the base.
- The zero selected subproblem is proved contractible and presented by the
  identity algebraic stack. Its finite-type boundedness witness is attached,
  and `Spec ℤ` supplies a concrete positive-dimensional supported case.

## Deliberate boundary

The construction does not identify the full relative-perfect moduli problem
with an algebraic stack. SF8 still supplies pullback only on explicit exact
base-change diagrams; arbitrary big-Zariski pullback and descent are needed
before constructing the full stack, its diagonal, and its atlas. The open
presentation interface likewise does not assert that a semistable predicate
is open until its actual open immersion is constructed.

## Verification

- `lake build DerivedAlgGeo`
- `lake build runLinter`
- `lake build AlgebraicGeometryAudit`
- declaration-enumeration completeness audit
- `scripts/gates.sh full`
