# compIso derivation — closeout record

**Scope:** the continuation session that closed §7 of
`2026-08-17-fm-lane-euler-and-geometric-ledgers.md`. Baseline `f4996a2`;
branch `agent/compiso-derivation`. One file of mathematics
(`Families/KernelConvolution.lean`) plus its audit lines.

## What landed

`geometricCompIso` — Prop. 5.10 derived from the seven inputs, exactly per the
validated design in the prior handoff's §7: same seven classes, same
eight-stage skeleton, same step-to-input table. `HasConvolutionComparison`
deleted; `geometricConvolutionData` now has zero supplied fields.

## The actual blocker, for the record

The prior handoff attributed the failed first attempt to *"section-variable
ordering across the stage definitions, on top of whiskering depth."* That was
real but secondary. After the restructure removed it, the derivation still
failed, and the surviving error exposed the primary cause:

**The pair-rewrite combinator was over-constrained.** The natural signature

```
{F F' : A₁ ⥤ A₂} {G G' : A₂ ⥤ A₃} (e : F ⋙ G ≅ F' ⋙ G') :
    F ⋙ G ⋙ R ≅ F' ⋙ G' ⋙ R
```

forces both pairs through the **same middle category** — and every pair
rewrite in this chain changes it. Flat base change replaces `q₁_* ⋙ p₂^*`
(through `Dᵇ(Y)`) with `πXY^* ⋙ πYW_*` (through `Dᵇ(triple)`); pullback
monoidality, the reversed projection formula, and the pullback-route swap all
do the analogue. The combinator needs `A₂` and `A₂'` as separate universes/
types. This is invisible in the informal skeleton, where the eight stages are
written only as endpoint-to-endpoint composites — the middle categories never
appear on the page. When a whiskering proof fails opaquely, check the middle
categories of the rewritten pair *first*; it is the analogue of the earlier
"give a second category its own universes" hazard, one level down.

## What made the elaboration tractable

- **One definition, `let`-ascribed stages.** Every intermediate functor
  `E₀…E₇` and every step `s₀…s₈` is a `let` with a fully ascribed type inside
  `geometricCompIso` itself. No stage abbrevs, no section variables, so no
  inclusion-order ambiguity and no positional-application guessing — the
  first attempt's recorded failure mode is structurally impossible here.
- **Seams as `Iso.refl _`.** Step 0 (transform-composite → six-factor chain)
  and step 8 (chain end → transform of `convKernel`) are `Iso.refl _` lets:
  each isolates one defeq check (associativity + delta) at a named line. Both
  elaborated instantly; no `backward.isDefEq.respectTransparency` needed
  anywhere in the file.
- **Explicit tails.** The combinators take the tail functor `R` explicitly;
  the one residual stuck-unification (step 6, whose `pairCongr` is the head
  of the term rather than under an `isoWhiskerLeft`) was resolved by
  pre-ascribing the route isomorphism in its own `let` and pinning the four
  functor implicits by name. Elaboration order around instance-implicit
  metavariables differs between head position and whiskered position; when a
  step fails with unassigned `?m` functors, pin, don't reorder.

## Trust boundary after this PR

Categorical side unchanged from the prior handoff. Geometric side: the seven
input classes (two pre-existing, five new in this PR), plus
`HasDerivedTensor`/`HasDerivedPushforward`/`HasCoherentPullback`/
`TripleProductGeometry` from the ledgers. Nothing constructs any of them;
nothing constructs a `Correspondence`; there is still not one Fourier–Mukai
transform in the geometric sense in the repository.

## Next (unchanged from prior handoff §8)

1. `HomFiniteBounded` for a concrete category.
2. Associativity of convolution (second comparison layer).
3. `UnitKernelData` geometrically (`𝒪_Δ`); `DualKernel`.
4. #508 (audit `libraryOf` sentinel), #480 (split audit files).
