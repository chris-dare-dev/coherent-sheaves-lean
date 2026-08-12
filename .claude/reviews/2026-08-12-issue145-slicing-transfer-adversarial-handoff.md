# Destination issue #215 (source issue #145) adversarial review handoff

Branch: `agent/issue-145-adjoint-slicing-transfer`

Base: destination issue #211 / migration PR #222 (source issue #141 / PR #153)

Scope: the sound categorical boundary for pullback and pushforward of slicings.

## Source correction that reviewers must preserve

Source issue #145's original wording suggests that adjunction plus conservativity
constructs a slicing.  That is false according to the pinned source
arXiv:2607.28411v1:

- Definition 3.1 defines `f^sharp P(phi)` by membership of `f_* F` in `P(phi)`.
- Remark 3.2 says this raw collection need not be a slicing; conservativity is
  necessary, not sufficient.
- Proposition 3.3 adds the finite-morphism phase condition before applying the
  Appendix-A inducing theorem.
- Definition 3.6 and Remark 3.7 say the same for pushforward via `f^*`.
- Proposition 3.8 adds the faithfully-flat/perfect-dualizing hypotheses and a
  phase condition.
- Corollary A.23 depends on Theorem A.17's presentable/Ind, boundedness, and
  t-exactness hypotheses.

The implementation therefore exposes raw phase collections separately and
requires `Slicing.PreimageData` before constructing a genuine slicing.

## Files and claims

- `Symmetry/Autoequivalence/Slicing/Transport.lean`
  generalizes `PostnikovTower.mapF` and `HNFiltration.mapF` from endofunctors to
  functors between two pretriangulated categories.
- `Phase/Transfer/Basic.lean`
  defines raw pullback/pushforward phase collections, the two-field lifting
  criterion (Hom-vanishing and HN existence), genuine preimage slicing, a
  faithful-functor constructor, and phase-shifted lifting data.
- `Phase/Transfer/Phase.lean`
  maps HN filtrations, proves exact `phiPlus` and `phiMinus` identities under
  zero-object reflection, reflects strict/weak phase windows, and instantiates
  destination issue #211's slicing-order interface.
- `Phase/Transfer/Equivariance.lean`
  proves phase-translation and compatible-autoequivalence commutation,
  including a representative-level `AutPair` wrapper.
- `Phase/Transfer/InducingBoundary.lean`
  records the adjunction, zero-reflection, and monad phase premise visible in
  the bounded API, plus a named but deliberately uninhabited Appendix-A
  theorem boundary.

## Adversarial questions

1. Does any declaration accidentally derive a slicing from conservativity or
   adjunction alone?
2. Are `PreimageData.hom_vanishing` and `.hn_exists` exactly sufficient for the
   remaining `Slicing` fields once shift compatibility is assumed?
3. Does the generalized `HNFiltration.mapF` preserve every tower field across
   universe/category changes?
4. Do both extreme-phase proofs correctly use zero reflection on the mapped
   first/last factors?
5. Are the strict and weak phase-window equivalences valid on zero objects in
   both directions?
6. Does `preimageOrderData` really instantiate the destination #211 interface with the
   correct category orientation?
7. Is the natural-isomorphism orientation in `preimage_mapEquiv` correct for
   the inverse representatives used by `Slicing.mapEquiv`?
8. Is `LeftAdjointInducingPremise.monad_ge` the correct `(v')` orientation
   (`L ⋙ F` on the category carrying the original slicing)?
9. Does the uninhabited `HasLeftAdjointInducingTheorem` make the remaining gap
   explicit without being mistaken for a proved result?
10. Are the pullback/pushforward source-facing aliases clear that both are
    instances of the same abstract preimage construction along different
    geometric functors?

## Expected non-claims

- No finite-morphism or faithfully-flat geometric instance exists yet.
- No presentable/Ind-completion theorem is proved.
- No quotient-level descent for paired autoequivalences is claimed without
  representative-independence data.
- Destination issue #215 should not be closed as fully complete merely because this
  bounded categorical foundation lands.
