# ADR-0006 — All contract issues are filed on `bridgeland-stab-lean`

- **Status:** accepted (provisional — has an explicit un-park trigger)
- **Date:** 2026-08-04
- **Deciders:** Chris Dare

## Context

The contract spans two repos and will eventually span three (see ADR-0007). Work
items therefore have three plausible homes. The relevant facts:

- `chris-dare-dev/arXMCP` has a mature roadmap machine: 12 milestones, ~300 open
  issues, a `type:milestone` label consumed by a `/milestone-pipeline`, epics
  named `<track>-e<N>` carrying `<!-- roadmap-gh: track/id -->` markers, and
  `plans/*/roadmap.yaml` as the source of truth.
- `chris-dare-dev/bridgeland-stab-lean` had, before this ADR, the nine GitHub
  default labels, zero milestones, and zero issues.
- Roughly 70% of the contract work is owned by this repo; arXMCP's share is
  three offline CLIs, one SQLite migration, two MCP resources, and the
  `lean_verify` repairs.

Filing contract work into arXMCP would bury it under 300 issues and perturb a
pipeline built for a different track structure. Splitting it across both repos
this early means neither milestone shows real progress and every dependency is a
cross-repo link.

## Decision

**All contract work, both repos' worth, is filed on
`chris-dare-dev/bridgeland-stab-lean`.**

- arXMCP's **label taxonomy is mirrored verbatim** onto this repo
  (`type:*`, `sev:*`, `area:*`, `gate:*`, `epic`, `cross-repo`, `blocked`,
  `parked`, `agent-ready`) so issues read the same in both places and can be
  transferred without relabelling.
- Work that lands in **arXMCP's tree** carries the **`cross-repo`** label, and
  its body names the target repo and file paths in the first line.
- Epics follow arXMCP's convention exactly: title `contract-v1-e<N>: <Title>`,
  the `epic` label, a milestone, and a trailing
  `<!-- roadmap-gh: contract-v1/contract-v1-e<N> -->` marker.
- `.claude/roadmap/contract-v1.yaml` is the local source of truth and mirrors
  arXMCP's `plans/*/roadmap.yaml` schema, so one parser reads both.

**Un-park trigger.** Split the tracker when *either* holds:

1. arXMCP's share exceeds ~15 open `cross-repo` issues, or
2. a second topic repo adopts the contract — at which point cross-repo issues
   belong in the contract repo, not in any one topic's tracker.

Until then, one place.

## Consequences

**Good.** One backlog, one milestone burndown, one place to look. arXMCP's
roadmap machinery is untouched, so nothing there needs to learn about a track it
does not own.

**Cost.** `cross-repo` issues are filed where they cannot be closed by a commit —
GitHub will not auto-close them from an arXMCP push, so they must be closed by
hand with the arXMCP commit SHA in the closing comment. Accepted: ~10 issues.

**This ADR does not bind arXMCP.** If the contract work there grows its own
plan track (`arXMCP/plans/formal-contract/`), that track's roadmap is
authoritative for arXMCP's half and this ADR's trigger 1 has fired.
