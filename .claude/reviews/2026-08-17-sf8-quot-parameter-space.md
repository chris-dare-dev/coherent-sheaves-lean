# SF8.4 Quot parameter-space review

Date: 2026-08-17

Issue boundary: #520, after the finite-type boundedness witness from #519.

## Implemented boundary

- `ModuleQuotient F` is an actual epimorphism `F ⟶ Q` of module sheaves.
  Its morphisms are commuting maps of quotient targets, and its target
  projection is a functor.
- Pullback of module sheaves sends quotient presentations to quotient
  presentations. The epimorphism proof is derived from finite-colimit
  preservation, and the construction is functorial on quotient categories.
- Identity and zero quotient presentations are concrete, with canonical
  pullback comparison isomorphisms.
- `RepresentableQuotientProblem` requires an isomorphism from the Yoneda
  functor of its parameter scheme to the quotient functor. The universal
  element is obtained from the identity morphism under that isomorphism.
- `FiniteTypeQuotientParameterSpace` additionally requires the actual
  parameter structure morphism to be locally of finite type and
  quasi-compact.
- The zero quotient functor has one object over each test scheme. It is
  represented by the terminal identity object `S ⟶ S`, whose structure
  morphism is finite type.
- The zero quotient maps to the concrete zero relative-perfect object and
  identity moduli problem, and its parameter scheme supplies the SF8.3
  finite-type boundedness witness with geometric coverage.

## Deliberate limitations

- Mathlib at the current pin contains no general Quot-scheme or Grassmannian
  representability theorem. No generic `QuotScheme` type is introduced.
- The represented case is nonempty but is the zero quotient. It proves the
  interfaces compose without claiming a nonzero bounded-complex parameter
  theorem.
- A nonzero Quot construction will require finite-presentation, flatness,
  Hilbert-polynomial, and representability infrastructure not yet present in
  Mathlib or this repository.
- No atlas, diagonal, algebraic-stack, semistable-reduction, or good-moduli
  conclusion is asserted.
