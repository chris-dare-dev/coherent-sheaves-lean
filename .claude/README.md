# `.claude/` — decision record for the arXMCP ⇄ Lean contract

This directory records **why** the two-repo architecture is shaped the way it is.
It is not documentation of what the code does; `CLAUDE.md` and `README.md` cover
that. Everything here is either a decision that was made, a decision that is
still open, or the evidence a decision rests on.

## Layout

| Path | What it is |
|---|---|
| `decisions/ADR-*.md` | One architectural decision each. Status is `accepted`, `open`, or `superseded`. An `open` ADR names the person who must decide and what changes either way. |
| `roadmap/contract-v1.yaml` | The track registry: milestones, epics, and their GitHub numbers. Schema mirrors arXMCP's `plans/*/roadmap.yaml` so one parser reads both. |
| `notes/2026-08-04-*.md` | The four artifacts the 2026-08-04 workflows produced, verbatim. Dated because they are snapshots, not living docs. |
| `open-questions.md` | The decisions blocking work, each with a GitHub issue. |
| `references/mathlib-style.md` | The Mathlib conventions this repo holds itself to, and the deltas it keeps on purpose. The spec `agents/mathlib-reviewer.md` enforces. |
| `agents/` | Repo-local subagents. One per file. |
| `skills/` | Repo-local skills, one directory each. `formalize-issue` is the unattended iteration. |
| `settings.json` | Hooks. Currently: the Mathlib-convention check on every Lean edit. |

## The artifacts in `notes/`

Produced 2026-08-04 by two multi-agent workflows (34 agents, ~4.2M tokens).
Every claim in the audit was adversarially re-verified against source by a
second agent instructed to default to REFUTED when it could not confirm.

- **`2026-08-04-arxmcp-lean-integration-audit.md`** — what arXMCP and this repo
  actually are today. Eight areas surveyed, each independently re-verified.
- **`2026-08-04-contract-architecture.md`** — the recommended architecture. Four
  designs competed; this is the winner with the runners-up's best ideas grafted in.
- **`2026-08-04-contract-schemas.md`** — the seven contract artifacts as
  copy-pasteable schemas, with a worked end-to-end trace.
- **`2026-08-04-contract-red-team.md`** — 18 ranked gaps in the above. Read this
  before implementing anything in the architecture doc.

### Reading order for an agent picking this up cold

1. `CLAUDE.md` (the working rules — they are load-bearing and override defaults)
2. `decisions/` in numeric order (~10 min, and it is the whole design)
3. `notes/2026-08-04-contract-red-team.md` (what is wrong with the design)
4. Only then the architecture and schema docs, which are long.

## Dates in this directory are UTC

Everything under `.claude/` is dated **UTC**. The rest of the repo —
`formalization.yaml`, git commits, `notes/` at the top level — is dated
**local (America/New_York)**. So an ADR reading `2026-08-04` and a trust-record
field reading `2026-08-03` can describe the same evening. Do not "fix" one to
match the other.

## Line numbers in `notes/` are snapshots

The audit's citations into **this** repo are valid at commit `fb47a38` only —
the repo moved three times during the audit, and has moved further since
(`SlicingAction`, `PreStabilityAction`, and `ShiftAnalysis` did not exist when
the audit ran, so its "lane-1 step 3 NOT FOUND as code" finding is stale).
Citations into arXMCP are valid at that repo's `3a7d626`.

Do not treat a line number here as current. Re-open the file.

## Where the issues live

All of them, both repos' worth, are filed on `chris-dare-dev/bridgeland-stab-lean`
— see `decisions/ADR-0006-issue-localization.md` for why, and for the migration
trigger that would split them.
