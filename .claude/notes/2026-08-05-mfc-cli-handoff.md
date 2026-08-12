# Handoff — the `mfc` CLI is complete; what it found on the way

**Date:** 2026-08-05 · **Repos:** `math-formal-contract-lean` @ `677361e`,
`bridgeland-stab-lean` @ `a4be854`. Both clean, both pushed, both CI green.

Read this if you are picking up the contract work. It is written for a fresh
session with no memory of the one that produced it, and it assumes you will
verify rather than believe — several claims below are corrections of things a
previous session asserted confidently and wrongly.

---

## 1. State in one table

| | |
|---|---|
| `mfc` subcommands | **10 of 10**, all implemented and in CI |
| Schemas | **8** (`registry/1.0` joined the original seven this session) |
| Tests | **287**, `contract/tests`, all passing |
| Rule families | `E-01..E-10` · `C-01..C-12` · `J-01..J-06` · `I-01..I-05` · `R-01..R-09` |
| `bridgeland-stab-lean` | 189 declarations audited, no `sorry`, CI green |

```bash
cd math-formal-contract-lean
export PATH="$HOME/.elan/bin:$PATH"
lake build && python3 -m pytest contract/tests -q && python3 -m contract.mfc.cli lint-schemas
```

The scaffold end-to-end test needs `lake`; it **skips** without it and
`MFC_REQUIRE_LAKE=1` makes that skip fatal. CI sets it in the `emitter` job.
If you run pytest without elan on `PATH` you will see `286 passed, 1 skipped`
and that is the one.

### What each subcommand answers

| subcommand | rules | question |
|---|---|---|
| `lint-schemas` | — | does any schema declare a banned trust-token property? |
| `validate` | — | is one artifact well *formed*? |
| `bundle` | — | build `declarations.json`, recomputing everything |
| `lint` | `E-*` | is what one emission *contains* allowed? |
| `conformance` | `C-*` | do the artifacts describe the same **build**? |
| `join` | `J-*` | do they describe the same **claims**? |
| `check-ilean-coverage` | `I-*` | is anything **missing**? |
| `registry` | `R-*` | is the hand-authored artifact sound? |
| `init` | — | render a topic repo that is green on run one |

---

## 2. The findings that matter

These are the reason this note exists. Most were found by *running the new
check on our own repository*, which is the single highest-yield thing this
session did — every rule family caught something real the first time it ran.

### 2.1 `pp.proofs` was deleting content from a digest input

`E-07` (no elided pretty-printed text) tripped on **13 of 150** constants in
the contract package's own emission. All compiler-generated `def`s
(`.noConfusion`, `.elim`, `._sparseCasesOn_N`).

The defect was in the **emitter**, not the rule. Lean's `pp.proofs` defaults to
`false`, which prints every proof subterm as `⋯`, and `value_pp` is emitted for
`def`/`opaque` — where `statement_digest` **hashes it**. So two defs differing
only inside an elided proof hashed identically.

Probed one option at a time rather than guessing: `pp.deepTerms` and
`pp.maxSteps` change nothing; `pp.proofs` accounts for all of it. Now pinned
`true` in `MathFormalContract/Emit.lean`. 0 elided.

**If you touch `ppOpts`, this is why every option is pinned explicitly.**

### 2.2 Three rules are unreachable through the CLI, and were credited wrongly

`E-08` (the emission is not vacuous), `R-01` (no placeholder version) and
`R-06` (no corpus-shaped key) are all **already enforced by their schemas**:

- `emission-1.0`: `constants: minItems 1`, `counts.total/in_scope: minimum 1`
- `registry-1.0`: `source.version` `pattern: ^v[0-9]+$`; `entries`
  `propertyNames: {$ref: citationKey}`

Every subcommand validates before it reads, so none of the three can ever fire
through `mfc`. Their rejection fixtures are rejected by `mfc validate`.

**This is the right arrangement** — a structural guarantee beats a rule a
caller can skip, same as `additionalProperties: false` gives the trust-token
ban. But the README and `rules.py` had credited the work to `E-08`. All three
are now labelled for what they are, kept as backstops for a library caller, and
the schema constraints are pinned by tests (`SCHEMA_ENFORCED`,
`test_an_empty_emission_is_not_a_representable_artifact`) so relaxing one is a
visible decision rather than a silent handoff to a rule nothing runs.

**Watch for more of these.** The pattern — a rule that duplicates a constraint
the schema already expresses — is easy to introduce and invisible until you run
the fixture through the CLI rather than through `check()`.

### 2.3 A rejection fixture can pass the suite while proving nothing

The registry rejection fixtures originally carried `$comment_fixture`, copying
the convention in `testdata/artifacts/invalid/`. With
`additionalProperties: false`, that key gets the **document** rejected at schema
validation, so the fixture never reaches the rule it was written for.

Caught because **10 of 10 exited 1 while 0 of 10 named a failing rule**. The
registry fixtures now carry no marker; their rationale lives in
`testdata/registries/invalid/README.md`.

`testdata/artifacts/invalid/` is fine — CI strips the key before validating.

### 2.4 The registry accessor was invented, not read

`E-04`, `E-05`'s registry half and `J-06` all read
`registry["statements"]` as a list of `{key, frontier}`. **No released schema
ever had that shape.** It was invented alongside the rules and then tested
against itself, so nothing could catch it.

`registry/1.0` keys `entries` **by citation key**, and `frontier[]` holds
objects whose open state is `discharged_by: null`. Two things the wrong shape
hid:

- `E-05` tested `frontier` for truthiness, so an entry whose items were **all
  discharged** was refused `relation_claimed: exact`. Length was never the
  predicate.
- Reading an unrecognised document as an *empty* registry produces two opposite
  failures from one bad input: `E-04` reports every citation unknown, `J-06`
  reports a clean queue over zero entries. A finding flood **and** a vacuous
  pass. `mfc/registry.py` now raises and callers report `not_run`.

### 2.5 Faithful transcription carries the source's mistakes too

`registry-1.0.schema.json` was **transcribed** from
`.claude/notes/2026-08-04-contract-schemas.md` rather than authored — the right
default, and what `digest.py` does.

But it preserved a defect **#21 had already written down as a defect**:
`mint_resolution` was schema-required and non-empty for every kind but
`obligation`, so no entry could be minted until a resolver existed — while
standing up the resolver is a later migration step. An adopter with no corpus
running could not create their first entry.

Caught by **re-reading the issue before claiming it delivered**, not by a test.
Now optional-with-reason: any kind may carry `mint_resolution: null`, and a null
must carry `mint_unresolved_reason`.

**Lesson to carry:** when transcribing, diff the source against the issues that
discuss it. The design note is a snapshot; the issues are its errata.

### 2.6 CI was reported green when it was red

A previous session reported CI green for `38dadd7` from local checks **before
the run finished**. It had failed — on the `mfc lint` step that same commit
added, with the real `E-07` finding in §2.1.

**Do not report a CI conclusion you have not read.** The pattern that works:

```bash
gh run watch $(gh run list --limit 1 --json databaseId --jq '.[0].databaseId') --exit-status
```

Related: the `test_the_generated_repository_survives_the_whole_chain` skip is
refusable via `MFC_REQUIRE_LAKE=1` for exactly this reason — a skipped check
reads identically to a passing one in a green run. That refusability paid off
one commit later, failing loudly on a missing `pytest` in the `emitter` job.

### 2.7 The Mathlib PR was closed — and it was the second one

**[mathlib4#42449](https://github.com/leanprover-community/mathlib4/pull/42449)**
(`feat(Analysis/Matrix): polar decomposition of an invertible matrix`) was
opened 18:57 UTC and closed 19:33 UTC on 2026-08-04. Not merged.

The reviewer's substantive point: *"this isn't specific to matrices… I already
have code for the more general case, but I haven't had time to clean it up and
upstream it yet."* Our own file conceded it — `polarFactor A` is literally
`CFC.sqrt (Aᴴ * A)` and the proof uses `CFC.sqrt_mul_sqrt_self`.

**The part worth knowing:** the reviewer linked
[mathlib4#33642](https://github.com/leanprover-community/mathlib4/pull/33642) —
a *different* contributor's matrix polar decomposition, closed by a *different*
maintainer in **January 2026**, same reasoning, same offer. Seven months apart,
two people holding unupstreamed general code, nothing landed.

Consequences, both recorded in `bridgeland-stab-lean/CLAUDE.md`:

1. `ForMathlib/PolarDecomposition.lean` **stays**. The deletion condition is now
   a command — `lake build` against the new pin resolves `Matrix.polarFactor`
   from Mathlib — not a citation of someone's intent.
2. Two process lessons: **ask on Zulip before writing an upstream PR** (check
   not only whether Mathlib *has* a result but whether anyone is working on it,
   and whether the generality is right), and **run the environment linters**,
   not just `lake build` and `lake exe lint-style` — CI rejected an `@[simp]`
   via `simpNF` that neither local check runs.

The user has explicitly deferred any Zulip follow-up. Do not open one
unprompted.

---

## 3. Issue state

**#21 (the `mfc` CLI) is CLOSED** — completed, closed at the user's explicit
instruction after the delivery comment was posted. All ten subcommands shipped.

**#50 (registry size ceiling / `sketch` lane) is DEFERRED**, not blocked.
Recorded in `.claude/open-questions.md` Q4 and in a comment on the issue.

- Settled sub-question: if a ceiling ships it is **documentary, not
  structural** — no `maxProperties`, the dated census carries the honesty.
- Deferring is cheap now because the decision-independent half is built: the
  schema, `R-01..R-09`, `mfc registry init/validate`, and `E-04`/`E-05`/`J-06`
  all run today against a hand-written registry. The open decision adds a
  `kind` enum member (MINOR bump) and a policy; neither moves a shape.
- Two corrections to the issue's own framing: **option 3 needs no code**
  (`J-03` already refuses to merge disagreeing reviews), and **options 1 and 2
  do not move the human axis at all by construction** — option 3 is the only
  one that increases entries carrying a real `faithfulness` verdict, which is
  the argument for 1+3 over the issue's recommended 1+2.

### Tracker cross-reference errors — verify any issue number before trusting it

- **#50 cites "#41"** for the coverage census. It is **#52**; #41 is
  `@[discharges]`.
- **#52 cites "#39"** for the sketch lane. That is `external_decls[]`; no
  sketch-lane issue exists.

---

## 4. Where to pick up

Three siblings of #21 under parent **#3** are affected. None were touched
because each carries a judgement call.

### Immediate — audit #20 (the adversarial fixture corpus)

**This is the recommended next action, and the one whose answer is genuinely
unknown without looking.**

#20 names ~15 specific must-reject fixtures. What exists now: 9 emission
(E-rules), 11 registry (R-rules), plus the schema-rejection and
artifact-rejection sets. But several of #20's named cases have not been checked
off against reality — `stale-review`, `foreign-env-attestation` (which must
render `not_applicable`, **not** fail), and `testdata/valid/textbook-source`
(which must **validate**, and arXMCP already ships two textbook notebooks).

Do: take #20's list literally, one name at a time, and report which exist,
which are covered under a different name, and which are genuinely absent. Do
not close it without that.

### Then — close #31, with a correction

`mfc check-ilean-coverage` is fully delivered (I-01..I-05, in CI, 0 missing
across 3 in-scope modules). But **#31's own warning is false** and should be
recorded before closing: it says the guard fires on a new topic repo's empty
first build and would block any adopter reaching green. It cannot — the
emission schema's `minItems: 1` makes an empty emission unrepresentable, so the
case never arises, and `mfc init` ships a real declaration so a scaffold builds
green on run one.

### Then — decide #37 (`attest/workqueue.json`)

Half delivered. `J-06` computes the queue today — partitioned by `kind`,
frontier rolled up, counts **never totalled**. What does not exist is the
**artifact**: nothing writes `attest/workqueue.json`, and it would be a ninth
schema.

The open question is whether to write it now or wait for #50, since the file is
partitioned by the very `kind` set that decision changes. #37 calls it *"the one
thing in this design with a real chance of getting an LLM to use it"*, which
argues for sooner.

**#3** cannot close while #20, #29 and #37 are open.

---

## 5. Standing constraints — do not rediscover these

From the user's own `CLAUDE.md` files. These are not suggestions.

- **`bridgeland-stab-lean` §2: no `sorry`. Absent beats sorry-backed.**
  Unconditional.
- **§4: the geometric lane is closed.** Say so and stop rather than
  axiomatizing the gap.
- **§8: arXMCP is a read-only data plane.** Nothing may ask it to write, run an
  agent, or hold formalization source.
- **Never `mkdir` + `git init` a repository, anywhere.** Hard gate, requires an
  explicit OK for that specific repo. This is why `mfc init` renders files and
  deliberately does *not* create a repository.
- **Push is per-event authorization.** One "yes, push" does not authorize the
  next. Re-ask.
- **Never `--no-gpg-sign`, never `--no-verify`.**
- **Local-LLM policy:** qwen produces, Claude reviews. Claude is always the
  quality gate; qwen is never the reviewer.

## 6. Things a fresh session will want to know about the code

- `contract/mfc/digest.py` is **frozen**. Any change is a MAJOR bump on every
  artifact carrying a digest. `tests/test_digest.py` pins three hand-computed
  values from the real repo at `f166a3d`.
- `lint` and `conformance` share `_report`, so a rule table means the same
  thing everywhere: `ok` / `FAIL` / `not_run`, with `not_run` names printed on
  every invocation and never folded into the count.
- **`not_run` is never `pass`.** This is the animating idea of the whole
  package. If you add a rule, its absent-input branch must say so out loud.
- **No aggregate verdict token, at any level.** `conformance` and `join`
  deliberately write **no artifact** — a file with a top-level verdict *is* the
  `aggregate-verdict` rejection fixture, produced by our own tool. Their output
  is a report plus an exit code.
- Exit codes are the contract with CI: `0` clean, `1` findings, `2` the check
  did not run. The 1-vs-2 distinction is load-bearing.
- The Lake package has **zero dependencies** and that is the named exception to
  a topic repo's one-pin rule. The `no-dependencies` CI job enforces it by
  grepping `lakefile.toml`.
