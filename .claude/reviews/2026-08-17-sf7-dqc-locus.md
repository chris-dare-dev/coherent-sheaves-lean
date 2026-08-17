# SF7.3 honest `Dqc` locus review

Date: 2026-08-17

Source boundary: arXiv:2607.28411v1, Appendix A.2, especially Lemma A.14
and Theorem A.17.

## What is proved

- `SchemeDerivedCategory X` remains the derived category of all
  `𝒪_X`-module sheaves.
- `SchemeQuasicoherentDerivedCategory X` is a distinct full subcategory,
  defined by quasi-coherence of every canonical cohomology sheaf.
- An explicit representative-complex isomorphism proves that an exact
  functor commutes with derived homology.
- The exact inclusion `Coh X ⥤ X.Modules` therefore induces a concrete
  functor `D(Coh X) ⥤ Dqc(X)`.
- Its bounded restriction lands in the intrinsic locus defined by ambient
  boundedness plus finite presentation of every cohomology sheaf.
- The repository's perfect thick envelope maps through that bounded coherent
  locus.

## What is deliberately not claimed

At the pinned Mathlib version there is no general abelian/derived realization
of quasi-coherent sheaves on an arbitrary scheme from which the inherited
triangulated and coproduct structures can simply be inferred. This slice does
not install such instances by fiat.

Likewise, it does not assert either of the two geometric theorems needed to
finish the scheme-level A.14 seam:

1. the concrete bounded coherent functor is an equivalence onto the intrinsic
   bounded coherent cohomology locus; or
2. the finite-locally-free perfect envelope is exactly the compact-object
   property of the large `Dqc` category.

Those obligations are named by `HasBoundedCoherentDqcIdentification` and
`PerfectObjectsAreCompactInDqc`. Neither is registered as an instance or
inhabited for an unsupported geometric case.

## Validation

- the focused `Dqc` module builds;
- the public families umbrella builds;
- the complete stability-condition axiom audit elaborates;
- the environment census reports zero unaudited public non-projection
  declarations.
