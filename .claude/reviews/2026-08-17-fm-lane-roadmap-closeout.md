# FM lane — roadmap closeout record

**Scope:** the continuation session that executed the ranked next-work list of
`2026-08-17-fm-lane-menu-execution.md`: #543's witness stage, kernel-level
associativity on the quadruple product, the unit laws for convolution, and
the `DualKernel` scoping. Read that record and the two before it first.

## What landed

| PR | |
|---|---|
| #552 | `HomotopyCategory.Bounded C` (ForMathlib; Mathlib has `Plus`, no bounded analogue) + `HomFiniteBounded k (Kᵇ C)` for Hom-finite linear `C`; `Kᵇ(FGModuleCat k)` the named witness. #543's satisfiability stage; the issue stays open for the `Dᵇ` route only |
| #556 | `geometricConvolutionAssoc` — kernel-level `(P∗Q)∗R ≅ P∗(Q∗R)` derived through a supplied `QuadrupleProductGeometry`; `ConvolutionAssocData` assembled with zero supplied fields; new `HasPullbackFactorization`/`HasPushforwardFactorization` |
| #560 | Unit laws, both levels: transform-level theorems + kernel-level structures abstractly; both kernel-level laws derived geometrically with `diagonalKernel`; new `HasUnitPullbackLeftUnitor`/`RightUnitor` |

Filed, deliberately code-free: **#559** — `DualKernel` substrate. The
consumable first stage is an abstract adjunction layer (`AdjointKernelData`),
from which `DualKernel` becomes *derived*; geometric layers follow each with
a consumer in place. Writing ledger classes before that layer exists would be
supplied data nothing discharges and nothing consumes.

## Decisions worth keeping

- **The witness lives on `Kᵇ`, not `Dᵇ`, and says so.** Every finiteness
  statement on `Kᵇ` is componentwise; the `Dᵇ` route needs localization Homs
  via semisimplicity or Ext-finiteness that nothing has. The equivalence
  `Kᵇ ≃ Dᵇ` over a field is neither used nor claimed — do not let a later
  reader "upgrade" the witness by citing it.
- **Object-level chains beat functor-level chains.** #556 and #560 evaluate
  the class isomorphisms at objects and transport with `mapIso` — no
  whiskering, no associators, and every file compiled on its first or second
  build. Prefer this shape whenever the statement is about objects; the
  functor-level machinery of #540 is only needed when the *statement* is a
  functor isomorphism.
- **The two projection formulas now have four distinct consumption sites**
  (`πXW`, `δ`, `σ₁₃₄`/`σ₁₂₄`, `τ`-left/`τ`-right), always split by slot.
  The slot separation is load-bearing vocabulary; cite the count when the
  duplication is attacked. Same pattern now for the two pulled-unit unitors.
- **Factorization ≠ route.** One-step-vs-two-step (`HasPullbackFactorization`)
  and two-step-vs-two-step (`HasCommonPullbackRoute`) are separate classes;
  degenerating either into the other drags identity-pullback inputs or
  `eqToHom` transport into every use.
- **`FullSubcategory` homs are wrapped** (`InducedCategory.Hom`, `.hom` /
  `homMk`) — *not* defeq to ambient homs. `InducedCategory.homLinearEquiv`
  is the bridge; budget for it in anything that computes with subcategory
  hom-spaces. This cost a debugging cycle in #552.
- **`runLinter`'s `unusedArguments` is an enforced gate.** It caught two
  genuinely unused hypotheses in #552 (the witness instance needs neither
  zero objects nor biproducts — `HomFiniteBounded`'s own context stops at
  the shift). Name every instance; unnamed instances are unaudited public
  declarations.

## State of the lane

The convolution story is structurally complete conditional on named inputs:
`conv` constructed, Prop. 5.10 derived, associativity derived at both
levels, unit object and both unit laws derived at both levels. Not stated
anywhere: the pentagon, unit/associativity coherence (triangle identities),
`DualKernel` (route in #559), and any instance of any supplied class. The
#546 audit split has now carried four consecutive lane PRs with zero
audit-file conflicts.

## Next, in rough order

1. **#559 stage 1** — the abstract adjunction layer (`AdjointKernelData`),
   the first non-toy `DualKernel` constructor.
2. **#543 remainder** — `Dᵇ` Hom-finiteness via Ext-finiteness over
   `FGModuleCat`, upstreamable pieces first.
3. **Coherence layer** — pentagon and triangle identities for the derived
   associativity/unit isomorphisms, if anything downstream ever consumes
   them; do not state them before a consumer exists.
