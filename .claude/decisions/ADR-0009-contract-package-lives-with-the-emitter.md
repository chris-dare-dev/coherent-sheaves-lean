# ADR-0009 — The contract package lives with the emitter

- **Status:** accepted
- **Date:** 2026-08-04 (UTC)
- **Deciders:** Chris Dare
- **Replaces:** [`ADR-0007`](ADR-0007-contract-package-location.md), withdrawn
  the same day when the verdict its every positive argument cited was found not
  to exist. Read that amendment before this one.

## Decision

The contract's **schemas, fixtures, and the `mfc` CLI live in
`math-formal-contract-lean`**, alongside the `@[cites]` attribute and the
emitter they describe.

`mfc` is a **shared** tool again, not an arXMCP-side-only CLI. The rule that
forbade that — "§5.4 rule 7, no shared Python package imported by both repos" —
was sourced entirely from the missing document and does not survive.

## Why here

**1. It is the only location whose justification survives contact with the
disk.** ADR-0007's case for `arXMCP/contract/` rested on a bridge-contract
system that is absent from both repos said to implement it. ADR-0008's case for
this repo did not: it rests on `@[cites]` being a
`SimplePersistentEnvExtension` whose duplicate registration is an import-time
error — checkable, and checked.

**2. arXMCP's own constitution points away from it.** `CLAUDE.md` §4.10 is
binding there and says in as many words that **arXMCP does not host
formalization work**, and that a topic repo is *"Sibling, never a subdirectory,
never a dependency."* ADR-0008 already declined to put the Lake package in
`arXMCP/contract/` for exactly that reason. Putting the schemas that describe
formalization artifacts there strains the same sentence.

**3. The question's premise expired.** Q2 asked "third repo, or
`arXMCP/contract/`?" while no third repo existed. One does — this one, created
hours later, already carrying CI, a released attribute, an emitter and a
zero-dependency invariant. The choice is no longer "create a third
constitution": it is "use the repo already named `math-formal-contract`".

**4. The contract and the thing it describes stop being separated.** The
emitter produces `emission/1.0`; the schema for `emission/1.0` now lives beside
it. A change to one is a diff that can touch the other. Under ADR-0007 those
were two repos with a vendoring dance between them.

## What this costs, stated plainly

- **The repo becomes polyglot.** A Lean project gains a `contract/` tree of
  JSON and Python, and a second CI job. That is a real cost and the main
  argument against.
- **The name is now slightly wrong.** `math-formal-contract-lean` will hold
  material that is not Lean. Renaming to `math-formal-contract` is the obvious
  follow-up; it is an owner action and is not done here.
- **The zero-dependency invariant is NOT weakened, and must not be read as
  weakened.** That invariant is about the **Lake package**: `lakefile.toml`
  carries no `[[require]]`, and CI enforces it by grepping that file. JSON
  schemas and a Python CLI do not appear in `lakefile.toml` and cannot make the
  named exception in `bridgeland-stab-lean` `CLAUDE.md` §1 lapse. **If anyone
  ever adds a Lake `require` to serve the contract package, the exception
  lapses and the dependency comes out of every topic repo** — unchanged from
  ADR-0008.
- **The fixture corpus still lives inside an implementation it referees.** This
  is not fixed by moving; it was ADR-0007's surviving argument that it cannot
  be fixed by location at all while there is one `mfc`. The mitigation is
  unchanged: hand-computed expected digests checked in as data (red-team gap
  16).

## When this reverses

ADR-0007's exit condition was unusable: its four triggers lived in the file
nobody can read, so the decision could not be reversed on evidence. This one is
checkable, deliberately:

**Reverse when a second topic repo adopts the contract** — i.e. when
`math-formal-contract-lean` has a consumer that is not `bridgeland-stab-lean`.
At that point the contract has consumers outside the pair and belongs in a
neutral repo that neither adopter owns. That is the same event as the M3
generalization gate (GitHub #56), so the sequencing is settled rather than
judged.

The test is one command — `does any repo other than bridgeland-stab-lean vendor
these schemas?` — not a citation.

## Consequences

- Epic `contract-v1-e3` (#19–22) is unblocked, targeting this repo.
- `mfc` may be imported by both sides. The topic repo validates against the
  schemas directly rather than against vendored copies with a drift test; the
  drift problem the vendoring was designed to solve does not arise while the
  schemas and the emitter share a repo and a commit.
- ADR-0001 through ADR-0006 are unaffected. Every one is about *what* the
  contract says; none about where it is committed. ADR-0008 is unaffected and
  is now the load-bearing precedent rather than the exception to ADR-0007.
- Nothing in arXMCP changes. It gains no `contract/` directory, and the
  cross-repo work it does own (#42–45, #47–48, #57–59) is untouched.
