# ADR-0010 — How a dg category is encoded, and where the H⁰ seam lives

- **Status:** accepted for Question 1; Question 2 narrowed and still open
- **Date:** 2026-08-13 (UTC)
- **Decider:** Chris Dare
- **Decision (Question 1, 2026-08-13):** **Option B — a bespoke `DGCategory`
  structure.** Taken on the measurement in
  `.claude/notes/2026-08-13-dg-surface-reconnaissance.md`, which showed the
  enriching category of Option A does not exist at the pin. Option A′ stays
  live as a separate `upstream-candidate` slice and is not a prerequisite of
  anything in DG1.
- **Still open (Question 2):** the root name is provisionally `DGLean` and is
  not needed until `dg-enhancements-e4` creates the root; the DG4 dependency
  direction is not needed until DG4. Neither blocks DG1.
- **Related:** ARCHITECTURE.md growth rule 1 and its taxonomy line *"Future
  derived-category and Fourier–Mukai libraries get dedicated roots with their
  first real theorem"*; `.claude/roadmap/dg-enhancements.yaml` (m0, e1)

## Context

The `dg-enhancements` track needs a dg category before it needs anything else.
Mathlib has no such object at `mathlib_rev` — a search for
`DifferentialGraded`, `DGCategory`, or a quasi-equivalence returns nothing —
but it has two different sets of parts from which one can be assembled, and
they lead to different long-run costs. The choice is not reversible cheaply:
every later definition in the track, and every transport lemma across the H⁰
seam, is stated against whichever encoding is chosen here.

What the pin does supply, and which both routes consume:

- `Algebra/Homology/HomotopyCategory/HomComplex` and its `Shift`,
  `Cohomology`, `Single`, and `Induction` companions — the Hom cochain complex
  between two cochain complexes, with `Cochain`, the differential `δ`, and the
  cohomological identification of its degree-zero classes. This is already the
  dg structure on complexes; neither route may re-derive it.
- `Algebra/Homology/Monoidal` — the monoidal structure on homological
  complexes, which is what an enrichment would enrich over.
- `CategoryTheory/Enriched/{Basic, EnrichedCat, Ordinary/Basic}` — enriched
  categories, and `EnrichedOrdinaryCategory`, whose shape ("an ordinary
  category together with an enrichment agreeing with its Homs") is exactly the
  shape a dg category has.
- `Algebra/Homology/HomotopyCategory/{Pretriangulated, Triangulated}`,
  `KInjective`, `KProjective`, and `Algebra/Homology/DerivedCategory/*` — the
  classical side of the seam, which this track compares against and does not
  fork.

**Measured 2026-08-13** against `mathlib_rev` exactly — see
`.claude/notes/2026-08-13-dg-surface-reconnaissance.md` for the commands, the
raw output, and the elaboration probes. Two results change this ADR:

1. **`CochainComplex (ModuleCat k) ℤ` is not monoidal at the pin.**
   `HomologicalComplex.HasTensor` does not synthesize for the ℤ-indexed shape,
   because the degree-`n` tensor is a coproduct over the infinite set
   `{(i,j) : i+j = n}` and Mathlib supplies only the finite-fibre instances.
   `ChainComplex (ModuleCat k) ℕ` *is* monoidal, which localizes the gap
   precisely. It is an instance/API gap, not a mathematical obstruction.
2. **The H⁰ seam is largely already proved.**
   `CochainComplex.HomComplex.CohomologyClass.homAddEquiv` gives
   Hⁿ(Hom•(K,L)) ≅ Hom_{K(C)}(K, L⟦n⟧) as an `AddEquiv`.

The first result invalidates Option A as originally written. The options below
are revised accordingly.

## Question 1 — the encoding

### Option A: enriched over cochain complexes

Define a dg category as an `EnrichedOrdinaryCategory (CochainComplex (ModuleCat k) ℤ) C`,
using the monoidal structure Mathlib already builds.

- Inherits enriched functors, enriched Yoneda, opposite and functor-category
  constructions as Mathlib grows them, rather than re-deriving each one.
- Makes "the underlying ordinary category" a projection rather than a
  construction, which is half of the H⁰ seam for free.
- Depends on the monoidal instance on `CochainComplex (ModuleCat k) ℤ` being
  usable at the pin — the load-bearing unknown, and the reason e1 exists.
- Universe and instance-resolution behaviour of the enriched API under a
  concrete monoidal category is unmeasured here.

### Option B: a bespoke `DGCategory` structure

Carry `Hom : C → C → CochainComplex (ModuleCat k) ℤ` with composition chain
maps and the associativity and unit axioms written out.

- No dependency on the enriched API elaborating well over this particular
  monoidal category.
- Every companion construction (opposite, product, functor dg category,
  Yoneda) is owner-authored and owner-maintained.
- Diverges from Mathlib's own vocabulary, which makes upstreaming any part of
  this track harder later — `upstream-candidate` becomes mostly unavailable.

### Option A′: build the ℤ-graded monoidal structure first, then enrich

Supply the missing `HasTensor` / `HasGoodTensor₁₂` / `HasGoodTensor₂₃`
instances for `HomologicalComplex C (ComplexShape.up ℤ)` under small-coproduct
hypotheses, in `ForMathlib`, then take Option A on top.

- The only route that ends with the track's declarations shaped like Mathlib's
  and genuinely upstreamable — the missing instances are themselves a clean
  `upstream-candidate`, useful to Mathlib independently of this repository.
- Pays a prerequisite before the first dg definition is written. The size of
  that prerequisite is not yet measured; measuring it is a spike, not a guess.
- Risks the track's first milestone becoming a homological-algebra milestone
  with no dg content, which is how a track loses its thread.

### Recommendation, not a decision

**Option B now, Option A′ as a separately scheduled `upstream-candidate` slice.**

The measurement inverted the original recommendation. Option A was recommended
on the argument that it spends the budget on the seam rather than on categorical
plumbing — but at this pin, Option A *is* plumbing: it requires building the
ℤ-graded monoidal structure before a single dg definition can be written.
Option B needs no monoidal structure at all, because `Cochain.comp` already
supplies the graded composition law directly.

The second measurement reinforces this. With `homAddEquiv` in hand, DG1's
headline theorem is close, and the fastest route to it does not pass through a
monoidal category.

**What changes either way.** Under B, `dg-enhancements-e2` carries the
structure and its companions (opposite, product, functor dg categories) are
owner-authored; the track should be assumed to stay in-repository, and
`upstream-candidate` mostly does not apply to it. Under A′, e2 stays small and
Mathlib-shaped, but DG1 acquires an unmeasured prerequisite ahead of its first
theorem. Choosing B does not foreclose A′: the ℤ-graded instances remain worth
building, and a later `EnrichedOrdinaryCategory` instance for a bespoke
`DGCategory` is an ordinary refactor rather than a rewrite.

## Question 2 — the root and the namespace

The repository has two owner-authored roots, `CohLean` and `BridgelandStabLean`,
and ARCHITECTURE.md's growth rule says a new subject gets its own root **with
its first real theorem**, not with its first definition.

- **Proposed root:** `DGLean`, matching `CohLean`'s naming, with subsystems
  `DGLean/Category` (dg categories, dg functors, H⁰), `DGLean/Enhancement`
  (the enhancement structure and transport), and `DGLean/Model` (C^dg, K^dg,
  D^dg).
- **Proposed trigger:** the root is created by the PR that proves
  `H⁰(C^dg A) ≌ HomotopyCategory A` (`dg-enhancements-e4`) — the first
  statement in the track that is a theorem about existing objects rather than
  a definition about new ones. Until then the work lives on a branch.
- **Rejected:** placing dg material under `BridgelandStabLean/`. The dg track
  is not about stability, and DG1–DG3 have no stability content at all. Only
  DG4 touches `BridgelandStabLean`, and it touches it as a consumer.
- **Also rejected:** a `Development/`-style holding pen as the permanent home.
  `Development/` is for compile-only API reconnaissance, and this is a
  library.

**Open sub-question for the decider:** whether the transport lemmas of DG4 live
in `DGLean/Enhancement/Transport` (dg-side, importing `BridgelandStabLean`) or
in `BridgelandStabLean/` (stability-side, importing `DGLean`). The dependency
direction is a one-way door once either root imports the other; the roadmap
assumes the former and does not depend on it.

## Consequences if this ADR stays open

`dg-enhancements-m0` may still complete: reconnaissance, coverage maps,
labels, milestones, and views need neither answer. `dg-enhancements-m1` cannot
start — e2 is the encoding, and writing it before the decision is how a
repository ends up with two.
