# SF7.2 compact generation and Polishchuk core review

## Scope

This slice implements the reusable categorical part of issue #477 against
Appendix A.2 of arXiv:2607.28411v1. It deliberately stops before claiming the
Brown-representability construction of A.13, Neeman's geometric A.14
existence, or S-locality.

## Source correspondence

- A.9 is represented by `IsCompactObject`: `Hom(K, -)` preserves every
  coproduct indexed in the chosen small universe.
- A.11's `Coprod(G)` is an inductive least closure under isomorphisms, small
  coproducts, and distinguished-triangle extensions.
- The compactness observation used in A.16/A.17 is proved from the adjunction
  and coproduct preservation, not stored as a field.
- A.17 Step 1 is `Adjunction.isTExact_of_compactlyGenerated`; it derives both
  halves of t-exactness from generated aisles and the right-t-exact monad.
- Steps 2 and 3 use proved truncation comparison isomorphisms and construct the
  restricted t-structure with the A.3/A.4 recognition equivalences.
- Step 4's boundedness follows from those recognition equivalences and target
  boundedness.

## Trust boundary

`TStructure.IndExtensionData` only names the output of A.14. There is no
inhabitant-producing theorem, global proposition, typeclass, axiom, or sorry
that turns the A.13/A.14 hypotheses into their conclusion. The assembled
Polishchuk theorem requires an actual source `TStructure` with a proved
compact-generation equality. This prevents the former
`HasLeftAdjointInducingTheorem` pattern from being reproduced under a new
name.

## Remaining work

1. Prove the A.13 compact-generator t-structure constructor.
2. Construct A.14 in the large scheme-derived category and identify its
   bounded coherent restriction.
3. Prove S-locality and bind the categorical result to the phase-indexed
   slicings used by Corollary A.23.
4. Remove the legacy global theorem parameter after the scheme callers are
   migrated.
