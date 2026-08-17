# FM lane — §8 menu execution record

**Scope:** the continuation session that worked through the post-`compIso`
menu of `2026-08-17-fm-lane-euler-and-geometric-ledgers.md` §8, immediately
after `2026-08-17-compiso-derivation-closeout.md`. Baseline moved
`c6d9f9a → …` across five PRs.

## What landed, in order

| PR | |
|---|---|
| #540 | `geometricCompIso` — Prop. 5.10 derived; `HasConvolutionComparison` deleted (see the closeout record) |
| #542 | Associativity of convolution **split**: `convolutionTransformAssoc` a theorem (free from four `compIso`s), `ConvolutionAssocData` the kernel-level supplied layer; the gap between them is Orlov uniqueness, stated |
| #544 | #508 closed: `EnumDecls` emits an `Unclassified` sentinel for source modules `libraryOf` does not claim; `check_audit_complete.py` fails naming them. Regression-tested both directions |
| #545 | The third ledger: `diagonalKernel` (a definition), `geometricUnitIso` (derived from `HasProjectionFormulaRight` at `δ`, `HasTensorUnit`, two retraction classes with guard `comm`s), `geometricUnitKernelData` with zero supplied fields |
| this PR | #480: audit files split per area behind imports-only umbrellas |

Filed, not started: **#543** — `HomFiniteBounded` for a concrete category,
scoped to the Ext-finiteness route over `FGModuleCat k`; multi-session.

## Decisions worth keeping

- **Associativity's data/theorem boundary is Orlov uniqueness.** The
  transform-level statement costs nothing; do not let a future session
  "supply" it. The kernel-level statement cannot be derived without a kernel
  being determined by its transform; do not let a future session claim it.
- **`HasProjectionFormulaRight` is consumed at two unrelated sites** (`πXW`
  in the convolution derivation, `δ` in the unit derivation) — evidence the
  class was the right abstraction. Cite this if its existence is attacked.
- **`DualKernel` stays a named absence, not a ledger.** Its classical formula
  needs derived duals and a dualizing complex; a ledger for it today would be
  classes nothing discharges and nothing consumes — the exact shape the
  review rounds attack.
- **The unit derivation's retraction classes carry guards, like the route
  classes of #540.** Triangle identities `δ ≫ p = 𝟙 = δ ≫ q` are data the
  derivation deliberately does not consume.

## Mechanics learned this round

- **`#print axioms` output does not replay across the import boundary.**
  An imports-only audit umbrella elaborates to an *empty* output — the
  vacuous pass. The split therefore runs each area file directly in both
  `gates.sh` and CI; `check_audit.py` counts commanded records across the
  umbrella's sibling directory. Any future audit reorganization must keep
  this invariant.
- **The #508 sentinel is scoped to the `DerivedAlgGeo` module root**, which
  is also why the audit split's new `StabilityConditionAudit.*` modules do
  not trip it.
- **Elaboration-order nondeterminism in stuck unifications**: the same
  `pairCongr` application failed at different steps on consecutive compiles
  of the same file while the real bug (over-constrained middle category) was
  present. Do not read "the error moved" as "progress".
- **A `lake env lean`-based sweep reads oleans**: after editing an umbrella
  (`DerivedAlgGeo.lean`), `lake build` the umbrella before trusting the
  sweep — the probe module was invisible until the umbrella olean was
  rebuilt. Same stale-olean hazard as the prior session, one level up.

## State of the lane after this session

Both `ConvolutionData` fields and `UnitKernelData` are constructed,
conditional on named inputs. The supplied surface on the geometric side:
`HasDerivedTensor`, `HasDerivedPushforward`, `HasCoherentPullback`,
`TripleProductGeometry`, the seven convolution inputs, the three unit inputs
(`HasTensorUnit`, two retractions), `KernelAutoequivalence`, `DualKernel`,
`NumericalRealization`/`Descends`/`PreservesEuler`, `HomFiniteBounded`,
`IsRiemannRoch`, and the kernel-level `ConvolutionAssocData`. Nothing
constructs any of them; there is still not one Fourier–Mukai transform in
the geometric sense in the repository.

## Next work, in rough order

1. **#543** — `HomFiniteBounded` for `Dᵇ(FGModuleCat k)`; staged route in
   the issue.
2. **Geometric kernel-level associativity** — derive `ConvolutionAssocData`'s
   iso for `convKernel` on a quadruple product; same toolkit as #540, one
   more product layer.
3. **Unit-for-convolution** — compare `convKernel` with `diagonalKernel`
   through a `ConvolutionData` for the self-correspondence.
4. **`DualKernel` substrate** — derived duals; far.
