# ADR-0008 — `@[cites]` ships as a shared Lake dependency, not vendored

- **Status:** accepted
- **Date:** 2026-08-04 (UTC)
- **Deciders:** Chris Dare
- **Amends:** `CLAUDE.md` §1, which forbids a second pin. This is a **named
  exception**, recorded there rather than taken silently.
- **Related:** ADR-0007 (where the *contract* package lives — a different
  artifact with a different answer)

## Context

The `@[cites]` attribute binds a Lean declaration to a registry key, and
`MathFormalContract.Emit` sweeps `Environment.constants` to produce the
evidence (ADR-0003). Both are Lean. Every topic repo needs them.

`CLAUDE.md` §1 says: *"Do not add a direct Mathlib `require`. A second pin is a
second thing to drift, and the point of this repo is a citable, reproducible
environment."* Vendoring the package would honour that literally.

**Vendoring is not available.** `@[cites]` is a `SimplePersistentEnvExtension`,
and **duplicate attribute registration is an import-time error**. Two vendored
topic repos could therefore never coexist in one Lean environment — not a merge
conflict, a hard failure at import. Vendoring also turns every schema bump into
a `copier update` 3-way merge over ~200 lines of Lean, and forces the emitter's
toolchain compatibility to be re-tested per topic instead of once.

## Decision

**A shared Lake dependency, pinned at an exact commit**, recorded as a named
exception to §1.

The exception is defensible on §1's own terms rather than despite them. §1's
worry is drift. This package is a **leaf with zero transitive dependencies** —
core Lean only, no Mathlib, no anchor — so it cannot drag anything else with
it, cannot disagree with the anchor about a Mathlib revision, and is the
least drift-prone pin the tree can hold. It is a second pin whose whole risk
surface is "did the emitter change", which is precisely what its own CI matrix
tests.

### Where it does *not* live: `arXMCP/contract/lean/`

This was the obvious placement given ADR-0007, and it is wrong, for a reason
established the same day:

`arXMCP/CLAUDE.md` §4.10, written under GitHub #15, says of the topic repo:
**"Sibling, never a subdirectory, never a dependency."** A
`[[require]] git = ".../arXMCP"` in a topic repo's lakefile makes that sentence
false. Secondary but real: Lake clones the whole dependency repo, so every
topic repo would clone a large Python server repo to obtain one attribute and
one emitter, and the topic repo's *build* would become sensitive to arXMCP's
git history.

### Where it lives

**Its own minimal Lean-only repository** — a lakefile, the attribute, the
emitter, a toolchain CI matrix. Nothing else. No `.claude/` world, no
constitution, no roadmap.

**This does not relitigate ADR-0007.** That decision rejected
`math-formal-contract` as the home for schemas + fixtures + the Python CLI +
the copier template — a "third constitution and a third `.claude/` world",
which is what the recorded verdict priced. A leaf Lean package is not a
constitution: it has one consumer class (Lean topic repos), one toolchain, and
no governance surface. And §5.4 rule 7's ban is specifically *"no shared Python
package imported by both repos"* — it does not reach a Lean package, which
arXMCP cannot import in any case.

## Consequences

**Good.** Two topic repos can share a Lean environment. `copier update` never
3-way-merges Lean. Emitter/toolchain compatibility is CI-matrixed once rather
than N times. The contract's Python half and Lean half are versioned
independently, which they should be — they change for different reasons.

**Costs.**

- **A second pin in every topic repo's lakefile**, which is exactly what §1
  warns about. Mitigated by the leaf property, and by holding the package to
  §1's own discipline: exact commit, never a branch, bumped deliberately with a
  `formalization.yaml` update in the same commit.
- **Two homes for one contract** — schemas and fixtures in `arXMCP/contract/`,
  the Lean package in its own repo. A topic repo pins both. Acceptable because
  the two move on different clocks; recorded here so nobody "tidies" them
  together later without reading ADR-0007 and this.
- **The package must be public**, or a topic repo cannot fetch it. This repo is
  private and arXMCP is public today; the Lean package follows arXMCP.

**When the third repo arrives.** ADR-0007's trigger 3 creates
`math-research-orchestrator` and gives it contracts custody. At that point the
Lean package can either move under it or stay standalone — a path change
either way, and not a decision to pre-make here.
