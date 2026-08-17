# Contract-v1 owner questions

Q2 and Q3 are answered, Q4 is deliberately deferred and its issue is now
**closed** on that deferral, and Q1 is settled for the formalization but still
open for corpus-version verification. The remaining owner choices stay linked
to `gate:owner` issues and name what changes either way.

Ranked by how much they block.

---

## Q1 — Which arXiv version of `math/0212237` was §8 formalized against? — **ANSWERED FOR THE FORMALIZATION**

`formalization.yaml` pins `math/0212237v3`, confirmed by the owner. This no
longer blocks minting. The remaining gap is narrower: arXMCP's ingested corpus
does not record which version its bytes came from, so corpus grounding cannot
upgrade a probable v3 match to a confirmed versioned match until #171 lands.

**Nothing on this machine knows.** The live `bridgeland-stability` notebook
records `arxiv_version = ''` — and the red team found this is not specific to
this paper: it is `''` for **every row in both live notebooks** (8/8 sampled in
each). The corpus **structurally cannot represent a version**.

This must be **confirmed by reading the abstract page, not inferred**. Every
downstream artifact pins it, and the unversioned form silently resolves to
arXiv's latest — so after the author posts a v3 and the operator re-ingests, the
resolver would match against v3 bytes and write `status: current` for an entry
declaring v2.

**Current consequence:** the formalization remains pinned to v3; the
arXMCP-side `arxiv_version` backfill is tracked by #171.

---

## Q2 — Where does the contract package live? — **ANSWERED (again)**

**Answered 2026-08-04 as `arXMCP/contract/`; WITHDRAWN the same day.** The
answer rested on `_pipeline/stage-1-discovery/synthesis/target-architecture.md`,
which **does not exist** — not in arXMCP, not anywhere under
`~/Personal/SourceCode`, never in arXMCP's git history — and neither do the
things it was cited as specifying (no artifact-type registry, no
`GET /bridge/contracts`, and no `.claude/references/bridge/` in
`personal-website`, the repo named as the vendoring precedent). Independently,
none of the seven filled instances carry the `bridge.*` envelope §5.2 says they
must. Full evidence and a survives/falsified table in the amendment at the foot
of [`decisions/ADR-0007`](decisions/ADR-0007-contract-package-location.md).

**Exactly one of ADR-0007's arguments survives**, and it is negative: with one
`mfc` implementation a fixture corpus cannot referee anything wherever it
lives. Nothing that positively chose `arXMCP/contract/` survives — including
"rule 7", which is the only reason `mfc` was made arXMCP-side rather than
shared.

**Blocks:** historically, the contract package (#146–#149, epic #130). The milestone that would
have created `arXMCP/contract/` stopped at `research-complete` on this finding;
no code was written against the withdrawn decision.

**The question is not the one it was.** Q2 was framed on the premise that no
third repo existed. **One does now** — `math-formal-contract-lean`, created
hours later by ADR-0008 for an adjacent reason, already carrying CI, the
`@[cites]` attribute and the emitter. ADR-0008 also declined to put that
package in `arXMCP/contract/`, because a Lake require on arXMCP would falsify
that repo's `CLAUDE.md` §4.10 *"Sibling, never a subdirectory, never a
dependency"* — and arXMCP's §4.10 also states plainly that **arXMCP does not
host formalization work**.

**Answered 2026-08-04 (later): `math-formal-contract-lean`**, alongside the
emitter. Recorded in
[`decisions/ADR-0009`](decisions/ADR-0009-contract-package-lives-with-the-emitter.md),
which replaces ADR-0007 and — unlike it — carries a reversal condition that can
be checked with a command rather than a citation.

`mfc` is a **shared** tool again: "rule 7", the only thing that made it
arXMCP-side-only, came from the missing document.

The options as they stood when the question was reopened:

1. **`math-formal-contract-lean`** — consolidate the contract in the repo
   already named for it, next to the emitter it describes. Its zero-dependency
   invariant is about the *Lake* package and is enforced by a grep of
   `lakefile.toml`, so JSON schemas and a Python CLI do not touch it; it would
   become polyglot and need a second CI job. `mfc` can then be shared again,
   since rule 7 is gone.
2. **`arXMCP/contract/` anyway** — recording that the envelope premise is
   unverified and the artifacts are flat. Cheapest in motion, but it keeps a
   decision whose stated reasons are gone and sits against §4.10.
3. **Find the missing document** — it may exist on the PC this work started
   on. If it does, ADR-0007 may be reinstated wholesale; if it does not, option
   1 or 2 stands.

**Nothing downstream should assume `arXMCP/contract/`.** Prose that already
does is corrected in the roadmap and in this file.

### The historical note worth keeping

ADR-0007's own closing rule was *"do not override a recorded verdict from a
summary of it."* That rule was right. But the verdict it deferred to could not
be read then either — the ADR quotes it, and the quotes are all anyone has.

Short version: the recorded verdict was read in full rather than in summary,
and it dissolves the case for overriding it. There is only one `mfc`
implementation, so a fixture corpus cannot referee "two implementations"
wherever it lives; the drift problem already has a precedented fix in this
ecosystem (`personal-website` vendors pinned bridge contracts with a
checksum-drift test); and the verdict explicitly rejected "create it now" as to
*timing*, on reasoning that holds exactly at N=1 adopter.

**The "larger finding" that used to sit here — that a versioned
bridge-contract system already exists, with an envelope, an artifact-type
registry and a `GET /bridge/contracts` handshake — is struck.** Every part of
it was sourced from the missing document, and none of it is present in either
repo said to implement it. It is kept in ADR-0007 as part of the withdrawn
record, not repeated here as if it were a finding.

---

## Q3 — Shared Lake dependency for `@[cites]`, or vendored? — **ANSWERED**

**Answered 2026-08-04 (UTC): shared dependency**, recorded as a **named
exception** in `CLAUDE.md` §1 rather than taken silently. Full record in
[`decisions/ADR-0008`](decisions/ADR-0008-cites-is-a-shared-lake-dependency.md).

Vendoring turned out not to be an option rather than a worse option: `@[cites]`
is a `SimplePersistentEnvExtension`, and duplicate attribute registration is an
import-time error, so two vendored topic repos could never coexist in one Lean
environment.

The exception is **bounded and lapses**: it rests on the package being a leaf
with zero transitive dependencies (core Lean only, no Mathlib, no anchor). If
that stops being true, the dependency comes out — it is not grandfathered.

**One consequence worth knowing:** the package does **not** live in
`arXMCP/contract/`, despite ADR-0007 putting the schemas there. A
`[[require]]` on arXMCP would falsify the sentence written into that repo's
`CLAUDE.md` §4.10 the same day — *"Sibling, never a subdirectory, never a
dependency."* So the Lean package gets its own minimal Lean-only repo, and a
topic repo pins two things that move on different clocks. That is deliberate,
not an oversight; see ADR-0008 for why it does not relitigate ADR-0007.

---

## Q4 — What is the registry's size ceiling, and is there a `sketch` lane?

**Blocks:** nothing immediately. **But the red team names this the single
biggest risk to the whole plan.**

The arithmetic: minting an entry is 20–40 min; a faithfulness review is ~2 h.
Ten entries ≈ 5–8 owner-days. The notebook has **146 papers / 15,280 chunks**.
One entry per paper ≈ 36–73 owner-days ≈ 2–4 months full-time for one person.
At ten entries the served surface has a **~0.07% hit rate**, and an LLM that
queries it three times, gets nothing, and stops querying is behaving rationally.

> the plan's most likely six-month state is not a broken contract but an
> immaculate, green, **empty** one: CI passing, digests matching, `caveats[]`
> correctly generated, ten entries, and nothing reading it.

`faithfulness: agent_drafted` was **deliberately rejected** (ADR-0005) — it would
let an LLM verdict occupy the one human axis. That rejection is right, but
rejecting it without a substitute makes volume unreachable by any route.

**The options:**

1. **10 curated entries, permanently.** Honest, and the served resource carries a
   dated coverage census so nobody mistakes it for corpus-wide.
2. **Add a `kind: sketch` lane** — agent-drafted, satisfies **zero** axes,
   excluded from `required_axes` filtering, mandatory caveat. Volume without
   letting an LLM occupy a human axis.
3. **A second reviewer**, which changes the arithmetic but not the shape.

Recommendation: **1 + 2 together.** The census is required by arXMCP `CLAUDE.md`
§4.9 anyway ("novelty claims are dated censuses"), so it is policy-compliant
rather than new.

### Status 2026-08-05 — DEFERRED, and no longer blocking anything

**Decision: defer.** Revisit when there is a real second topic to test
generalization against, rather than deciding the lane question in the abstract
against one repository.

**If a ceiling ships it will be documentary, not structural** — the dated
census carries the honesty, and there will be no `maxProperties` in the schema.
"Permanently ten" is a judgement that will want revisiting, and a validation
error on entry eleven is a bad way to reopen it. This is the one sub-question
that *is* settled.

**What changed, and why deferring is now cheap.** This question used to gate
the registry itself. It no longer does — the decision-independent half is
built and green:

| | state |
|---|---|
| `registry-1.0.schema.json` | **exists**, transcribed from the design note |
| `R-01`..`R-09` + 10 rejection fixtures | **exist**, `mfc registry validate` |
| `mfc registry init` | **exists** — mints the 12-hex id |
| `E-04`, `E-05` registry half, `J-06` | **run today** against a hand-written registry |

The open decision adds a `kind` enum member (a MINOR bump, flowing through
`kind` untouched) and a policy. Neither moves `entries{}` or `frontier[]`, so
nothing above has to be rewritten when it lands.

**Two corrections to this question's own framing**, found while building:

* **Option 3 needs no code.** `mfc join`'s `J-03` already refuses to merge two
  reviews of one statement that disagree — deduping would pick a winner, and
  the point is that a person must. A second reviewer is purely a social step.
* **Options 1 and 2 do not move the human axis at all, by construction.**
  Option 3 is the only one that increases the number of entries carrying a real
  `faithfulness` verdict — the axis ADR-0005 calls the bottleneck and "the only
  one that catches the thing this repo most fears". That is the argument for
  preferring **1 + 3** over the recommended 1 + 2 whenever this is reopened.

**Cross-reference errors in the migrated tracker — checked against the tracker
and now fixed at the source.** Both citing issues pointed at closed Layer-B
mathematics issues, and the two earlier attempts to correct them were each
wrong on one of the pair:

| where | cited | is actually | corrected to |
|---|---|---|---|
| #177 → coverage census | `#41` | B5: Riemann–Roch for line bundles (closed) | **#179** |
| #179 → sketch lane | `#39` | B5: canonical and dualizing sheaves (closed) | **#177**, the decision itself |

No sketch-lane issue exists, and none should be opened while this is deferred —
#179 now cites the decision rather than a lane that has not been chosen. For
the record: #168 is `@[discharges]` and #166 is `external_decls[]`; neither was
ever the census.

### Status 2026-08-17 — CLOSED AS DEFERRED

#177 is closed. The 2026-08-05 verdict stands unchanged and the question is no
longer tracked as an open owner gate, because it gates nothing: the
decision-independent half shipped, and `mfc validate` already puts a `sketch`
lane through `lanes` today via `propertyNames` as a *pattern* rather than an
enum, so even the lane's schema shape is not blocked on choosing it.

**Reopen trigger, and only this one:** a second topic repository mints against
the registry. That is the condition the deferral named, and the abstract
version of the question against one repository should not be reopened without
it.

**What the reopening should decide, ranked.** Option 1 (documentary ceiling) is
settled and needs no reopening. Between the other two, prefer **1 + 3** over
the recommended 1 + 2: Option 3 is the only one that increases the number of
entries carrying a real `faithfulness` verdict, and it needs no code — `J-03`
already refuses to merge two disagreeing reviews of one statement.

---

## Q5 — `quote_mode`: `verbatim` or `digest_only` by default?

**Blocks:** the registry schema (M2). Lowest stakes of the five.

Registry entries inline verbatim statement text. Bridgeland 2007 is arXiv
perpetual-non-exclusive, so this is fine **here**. A future adopter's source may
not be.

`digest_only` weakens offline verification — the topic repo can no longer
recompute its own hash from the inline quote — and degrades resolution to
`printed_number`, which is exactly the field most likely to be **absent** on
textbook and PDF-OCR sources (`_extract_printed_number` lives only in the
ar5iv/LaTeXML chunker; coverage is 36 of 66 chunks even on the flagship paper).

Recommendation: **`quote_mode` required from v1**, so the two grounding
strengths are always distinguishable in the served record, with `verbatim` the
default for arXiv sources.
