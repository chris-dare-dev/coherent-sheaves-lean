# ADR-0010 — How a dg category is encoded, and where the H⁰ seam lives

- **Status:** open
- **Date:** 2026-08-13 (UTC)
- **Decider:** Chris Dare. Two questions, below, must be answered before any
  Lean lands for the `dg-enhancements` track.
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

The measurements above were taken by inspection of a Mathlib checkout that is
**not** the pinned revision. `dg-enhancements-e1` must re-run them against
`mathlib_rev` in `pins.json` exactly, record the commands and their output, and
correct anything here that does not survive. Nothing in this ADR may be cited
as a pin-accurate fact until that has happened.

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

### Recommendation, not a decision

**Option A, contingent on e1's elaboration evidence.** The deciding argument is
not elegance but maintenance: the track's value is the seam, and Option A
spends its budget on the seam instead of on re-deriving categorical
plumbing. Option B is the fallback and must be taken without reluctance if the
monoidal instance does not carry its weight at the pin — a bespoke structure
that elaborates beats an enriched one that fights the elaborator for a year.

**What changes either way:** under A, `dg-enhancements-e2` is small and the
track's declarations are shaped like Mathlib's, so individual results stay
`upstream-candidate`-eligible. Under B, e2 grows by roughly the content of the
enriched-category files, e5 (opposite/product/functor dg categories) grows
similarly, and the track should be assumed to stay in-repository permanently.

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
