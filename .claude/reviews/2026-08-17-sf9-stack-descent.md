# SF9.1 stack-descent review

Date: 2026-08-17

Issue boundary: #523, after the SF8.2 relative-perfect moduli presheaf.

## Implemented boundary

- `StackInGroupoids` combines a groupoid-valued pseudofunctor with Mathlib's
  `Pseudofunctor.IsStack` for a chosen Grothendieck topology. The definition
  contains no algebraicity or finiteness field.
- Covers are explicit families whose arrows generate a covering sieve. Čech
  descent is Mathlib's existing `Pseudofunctor.DescentData`, rather than a
  duplicate repository-local encoding.
- The stack condition gives a concrete equivalence from each fiber to its
  Čech descent category. Morphism descent is fully faithful and object descent
  is essentially surjective.
- `StackEquivalence` records fiber equivalences, descent-category
  equivalences, and the comparison square required to transport the stack
  condition in both directions. This is explicit because Mathlib currently
  has no general pseudonatural-equivalence API for these pseudofunctors.
- A sheaf of types produces a stack in discrete groupoids. The proof derives
  full faithfulness from separatedness and essential surjectivity from
  amalgamation.
- For every scheme `X`, Yoneda subcanonicity constructs the nonconstant
  big-Zariski stack represented by `X`; its fiber over `T` consists of actual
  morphisms `T ⟶ X`, and every Zariski cover has an effective descent
  equivalence.
- Pullback-compatible stack maps and pointwise Yoneda fiber representations
  provide the interface required by later moduli representability work.

## Deliberate limitations

- The pullback-compatible map interface does not yet construct a bicategory
  of stacks or composition coherence for stack maps. Later consumers must not
  infer those results from the current structure.
- A fiber representation requires an equivalence for every test object, but
  this milestone does not turn that interface into an algebraicity theorem.
- No smooth atlas, diagonal representability, Artin criterion, boundedness,
  semistable reduction, quasi-properness, or good-moduli result is claimed.
- Applying stack descent to the relative-perfect moduli problem still requires
  proved pullback preservation and descent for those complexes; the identity
  model from SF8.2 alone does not supply it.
