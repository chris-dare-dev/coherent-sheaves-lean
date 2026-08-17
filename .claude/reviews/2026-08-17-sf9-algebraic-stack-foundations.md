# SF9 algebraic-stack foundations review

Issue: #522 (partial; remains open)

## Delivered

- Every scheme morphism now induces a pullback-compatible morphism between
  representable big-Zariski stacks.
- Its stack-theoretic fibers are represented by the actual scheme fiber
  products, with a proved Yoneda equivalence.
- Representable geometric properties are checked on the structure morphisms
  of the representing schemes and are preserved under base change.
- Representable diagonals are modeled by actual scheme equalizers.
- `AlgebraicStack` records an effective stack, representable diagonal, actual
  atlas scheme, atlas morphism, and smooth-surjectivity on every represented
  fiber.
- Representable stacks and locally finitely presented representable stacks
  over a base inhabit the interface. The affine line supplies a concrete
  positive-dimensional example.

## Deliberate boundary

This change does not yet construct the relative-perfect moduli stack required
to close #522. In particular, arbitrary base-change compatibility and descent
for relative-perfect objects, its representable diagonal and atlas, the
semistable open substack, and compatibility with the SF8 boundedness parameter
space remain future work. No opaque proposition is used as a substitute for
those geometric constructions.

## Verification

- `lake build DerivedAlgGeo`
- `lake build runLinter`
- `lake build AlgebraicGeometryAudit`
- declaration-enumeration completeness audit
- `scripts/gates.sh full`
