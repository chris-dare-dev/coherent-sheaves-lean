# SF7.2 A.13 constructor review

## Scope

This slice formalizes the assembly step of Theorem A.13 in Appendix A.2 of
arXiv:2607.28411v1. It starts from the approximation triangles produced by
Brown representability and constructs the compactly generated t-structure.

## Source correspondence

- `TStructure.AisleData` is the shift-stable aisle plus the approximation
  triangle for every object.
- `AisleData.tStructure` uses the aisle as degree zero and its right orthogonal
  as degree one, proving all shift, orthogonality, and triangle axioms.
- `ObjectProperty.coprodClosure_le_shift` proves that the paper's
  `G[1] ⊆ G` hypothesis propagates through `Coprod(G)`.
- `CompactGeneratorApproximation.tStructure` gives `D≤0 = Coprod(G)` and
  `D≥1 = Coprod(G)⊥`, the latter being formula (A.2).
- `isCompactlyGeneratedBy` packages the resulting t-structure with the proved
  compactness of the generators.
- `Polishchuk.induceOfApproximation` feeds that constructed source
  t-structure directly into categorical A.17 and derives source-generator
  compactness from the adjunction.

## Trust boundary

There is no theorem or instance constructing
`CompactGeneratorApproximation G` from compactness alone. That implication is
the Brown-representability content of A.13 and remains open. Thus the new API
removes the formal t-structure assembly from the boundary without hiding the
deep existence theorem in a proposition, typeclass, axiom, or `sorry`.

## Remaining work

1. Formalize the Brown-representability approximation construction.
2. Use it for the A.14 Ind-extension and prove restriction to the bounded
   coherent subcategory.
3. Instantiate the construction on scheme-derived categories and prove
   S-locality.
