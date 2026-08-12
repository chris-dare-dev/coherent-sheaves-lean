# Recommended architecture — **Cold Seam + Statement Registry + Attestation Bundle**

## Recommendation in one page

**The two repos never call each other.** The contract is a set of versioned, schema-validated *files*, exchanged at release time via git tags. No port, no auth, no server, no shared toolchain, no version handshake. This is the single most important property, because arXMCP is loopback-only, unauthenticated, default-off for Lean, and skewed two Lean minor versions from the pin — every runtime coupling inherits all of that, and every file-based coupling inherits none of it.

**Three homes.**

- **`math-formal-contract`** (new, data-only, ~800 LOC): JSON Schemas, the language-neutral adversarial fixture corpus, the `mfc` Python CLI, a **zero-dependency Lake package** (`@[cites]` attribute + the emitter library), and the copier template. Both siblings vendor it at an exact 40-hex commit recorded in `contract.lock`.
- **`bridgeland-stab-lean`** (topic repo): Lean source, the **statement registry** (`registry/*.yaml` — hand-minted, git-tracked, versioned alongside the proofs it plans), the generated **attestation bundle** (`attest/`), the human review file, and the only CI job that can fail the contract. It cuts releases: `git tag` is currently empty, which is why "arXMCP pins releases" is presently false.
- **`arXMCP`**: unchanged as a corpus. Gains exactly two offline read-only CLIs (`tools/statement_resolve.py`, `tools/formal_release_pin.py`), one sqlite migration (v5→v6), and two MCP **resources** — never a tool, so `EXPECTED_TOOL_SCHEMA_SHA256` and the BP1 prefix are untouched.

**Identity is minted by a human in the Lean repo and contains zero corpus-derived bytes.** A citation key is `stmt:<registry-id>:<local-label>` — e.g. `stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2`. The paper coordinate (`scheme`/`id`/`version`/`printed_number`/`kind`) rides as **typed fields of the registry entry, not as segments of the key**, which is what makes the scheme work for `textbook:`/`doi:` sources and what removes the colon-tokenization problem all four candidate designs had. arXMCP never issues identity; it answers exactly one question — *does this registry entry's quote still appear in the corpus, and where* — and its answer is a committed file, not a live call.

**Evidence is produced where the environment lives.** `lake exe mfc-emit` sweeps `Environment.constants`, calls `Lean.collectAxioms`, and never parses source — so the fail-open the audit reproduced against arXMCP's `_DECL_SITE_RE` (`set_option maxHeartbeats 400000 in theorem sneaky : False := bad` → `outcome: "clean"`) is structurally impossible on the producing side. arXMCP is **forbidden by construction** from producing elaboration or axiom evidence: it has no Lean at v4.29.0, so any axis record whose `env_digest` differs from the record's environment renders `not_applicable` — never pass, never fail.

**Seven axes, four values (`pass`/`fail`/`not_run`/`not_applicable`), no aggregate token, and every axis carries `self_attested: bool` plus a `caveats[]` block generated mechanically from the axis values.** `relation` is always spelled `relation_claimed` in machine artifacts and only becomes `relation_confirmed` inside a dated, named human review. That naming is the schema-level defence against an LLM reading six greens as "verified".

**Cost:** ~10 evenings to first release; ~4 more to a validated second topic.

---

## Why this and not the others

**ABR — Anchor–Bundle–Rulebook (13/26).** This is the skeleton I kept: the cold seam, the in-toto envelope (one subject, N independently-dated predicates, VSA explicitly rejected because `verificationResult: PASSED|FAILED` is the forbidden token), the language-neutral fixture corpus in a third location, and `git diff --exit-code attest/`. What killed it standing alone was that it put the anchor registry inside **arXMCP** — a repo with zero extension points, no tracked `notebooks/` tree, and `/var/` in `.gitignore` — so every adopter would need commit rights to the shared server; and the bundle crossed the seam unsigned, validated only for self-consistency, so all four of its sorry-gates were producer-side and none survived a file copy. Both are repaired below by moving the registry into the topic repo and making `formal_release_pin.py` re-derive every digest from the git tag object.

**Cairn — the statement graph is the contract (12.5/26).** I took its central architectural claim wholesale: **the graph lives in the Lean repo, because it *is* the formalization plan** and arXMCP's own boundary says arXMCP does not host formalization work. I also took `obligation` nodes, the required `frontier[]`, and the lint `relation: exact ⇒ frontier == []` — the only proposal in the batch that converts CLAUDE.md §3 from a naming convention into a build failure. What killed it standing alone: its `type_digest` hashed only `type_pp`, so editing the body of `abbrev NumLattice : Type := Fin 2 → ℤ` leaves every dependent theorem's digest byte-identical and carries an old human review forward across a meaning change — the exact audit-gap-8 hole it claimed to close, landing in the exact file §3 exists to protect. And its generalization step was #12 of 13 with no forcing function.

**Quote-and-Anchor / FTC v1 (11.5/26).** I took its economy: the resolver output as a **file committed into the producer's repo** with a `registry_sha256` staleness gate (one comparison, no clocks, no broker, no network), and its insistence that the key contain zero corpus-derived bytes. What killed it standing alone: its acceptance test for generalization was "empty second repo, green CI," which is observationally identical to its own worst failure mode (a mis-set `ourPrefix` yields an empty `decls[]` and a vacuous pass); its `authority = arxiv|doi` grammar cannot express the `textbook:<slug>` paper-ids arXMCP already ships; and three of its seven axes (`sorry_free` ⊂ `axioms_within_allowlist` ⊂ `no_local_axiom`) are three views of one closure computed by one program, so four greens were two facts.

**FROZEN WIRE (10/26).** I took its single best idea outright — **`env_digest` on every axis with `not_applicable` as a first-class fourth value for foreign environments**, which converts the v4.31.0-vs-v4.29.0 skew from a silent soundness hole into a value in the type system — plus its insistence that `lean_verify` output be admissible only under a reserved predicate type that satisfies zero axes. What killed it standing alone: its identity authority lived at `var/arxmcp/notebooks/<slug>/statements.jsonl`, and `arXMCP/.gitignore:31` is `/var/`, so every issued id named a row in a permanently untracked file on one workstation, with ~45% of ids being locally-allocated ordinals that a second operator would allocate differently. Its cassette was also double-booked as both provider-verified fixture and consumer gate, which cannot hold.

---

## The role split

| Concern | Owner | Rationale | What would be wrong elsewhere |
|---|---|---|---|
| **Corpus retrieval** (search, chunks, embeddings, `chunk_id`, `corpus_version`) | arXMCP | It is the only thing that owns a parse pipeline. `chunk_id` stays *internal*: it rotates by design (`make ingest-recover-preambles` — "triggers chunk_id rotation"), has no alias table, and `merge_insert` has no delete arm so rotation **doubles** rather than fails. | Duplicating the corpus into the Lean repo is exactly the boundary violation arXMCP's constitution forbids, and it would put 15,280 chunks under a Lean toolchain pin. |
| **Statement grounding** (does this quote still appear, and where) | arXMCP — `tools/statement_resolve.py`, offline, read-only, generic | Only arXMCP can answer it, and it is a pure *read*. This is the one axis with genuinely independent evidence: a different system, a different program. | If the Lean repo answered it, `binding_resolves` would be producer-self-attested like everything else and the seam would have no independent measurement at all. |
| **Statement registry** (`registry/*.yaml` — the durable ids, quotes, frontier, obligations) | **bridgeland-stab-lean** | It *is* the formalization plan; it must be versioned with the proofs it plans; and arXMCP's `/var/` is gitignored while its repo has no extension points (`grep NotebookSpec`/`notebook.yaml` → nothing). Adopter #2 must not need commit rights to a shared server. | In arXMCP it would be either unpublishable (`/var/`) or a per-adopter commit to the shared server repo — and it would be arXMCP hosting formalization work, which the R5 brief forbids. |
| **Lean source** | bridgeland-stab-lean | Obvious. Unproved results stay **undeclared** with a TODO — an undeclared obligation is a first-class registry entry with `decls: []` that appears in the work queue, never a `sorry`. | — |
| **Lean environment definition** (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, `env_digest`) | bridgeland-stab-lean; **published** to arXMCP inside `attest/environment.json` | The environment is a property of the repo that has it. `env_digest = sha256(canonical_json({lean_toolchain, lean_githash, resolved leanOptions, sorted [(name, rev)]}))` — hashing `rev`, never `inputRev` (nine packages carry `inputRev: "main"`), and including `[leanOptions] autoImplicit = false` because it is elaboration-affecting. | arXMCP inferring a pin is audit gap #2. Handing it a pin closes the gap without arXMCP acquiring a Lean toolchain it cannot keep in sync. |
| **Elaboration / axiom checking** | bridgeland-stab-lean **exclusively** | arXMCP's REPL is v4.31.0 from a detached-HEAD directory outside the repo; the pin is v4.29.0. An `ok` from it is not evidence about this environment, and the audit proved its axiom audit fails open. | Any arXMCP-produced elaboration verdict is either meaningless (wrong env) or evadable (regex declaration extraction). Making that structural, not advisory, is the point. |
| **Trust records** (per-statement axes) | Produced by bridgeland-stab-lean CI; **pinned and re-served verbatim** by arXMCP | Per the R5 brief: "the registry only pins releases." arXMCP may **downgrade** an axis from its own fresher resolution; it has no code path that raises one. | If arXMCP could grant an axis it would be asserting things about an environment it does not host. If it could not re-serve, the corpus-side agent would have no path to the record at all. |
| **Agent orchestration loop** | Neither — stays unbuilt, interim home `arXMCP/.claude/` | `arXMCP/CLAUDE.md §4.8` rule 3, and `_pipeline/.../target-architecture.md:113-126`'s "NOT NOW — create on trigger". The work queue here is a static JSON file, so the loop has nothing to hold. | Putting a loop in `server/` violates rule 1 (`anthropic` SDK stays out of `server/`). Putting it in the contract repo makes that repo a fourth constitution. |
| **CI** | One workflow per repo, both generated from the template | Neither repo has any today; `arXMCP/.github/` holds only issue templates and a release-notes config, `bridgeland-stab-lean/.github/` does not exist. Both jobs are hermetic; neither needs the other running. | A shared CI would need auth and a live loopback server, neither of which exists. |
| **Topic template** | `math-formal-contract/template/` (copier) + the `lean/` Lake package | Copier's `.copier-answers.yml._commit` is an exact-commit pin of the template — structurally identical to the lakefile rule — and `copier update` is the only mechanism that migrates schema v1→v2 across N repos. Cookiecutter has no equivalent. | Vendoring the emitter as a templated metaprogram makes `copier update` a 3-way merge on 200 lines of Lean, and vendoring the `@[cites]` attribute makes two topic repos unable to share an environment (duplicate attribute registration is an import-time error, not a merge conflict). |

---

## The contract

Seven artifacts. Every one carries `schema_version: "<name>/<major>.<minor>"`, every schema is JSON Schema 2020-12 with **`additionalProperties: false`**, and no schema defines a property named `status`, `verified`, `ok`, `passed`, `trusted`, or `result` — enforced by `mfc lint-schemas`, with a rejection fixture.

### 1. `registry/<work-slug>.yaml` — hand-minted, Lean repo, git-tracked

```yaml
schema_version: "registry/1.0"
registry_id: "9f4c1a20b7d3"        # 12 lowercase hex, minted once by `mfc registry init`
notebook_hint: "bridgeland-stability"   # advisory only; NEVER part of any key
entries:
  "stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2":
    kind: lemma                      # theorem|lemma|proposition|corollary|definition|
                                     #   construction|equation|remark|conjecture|obligation
    title: "Lemma 8.2"
    informal: "…one-sentence English gloss, human-written…"
    source:                          # REQUIRED. Coordinates are FIELDS, never key segments.
      scheme: arxiv                  # arxiv | doi | textbook | url
      id: "math/0212237"
      version: "v2"                  # REQUIRED when scheme==arxiv; pattern ^v[0-9]+$
      printed_number: "8.2"          # nullable — hint, never load-bearing
      locator: "§8"
    quote_mode: verbatim             # verbatim | digest_only  (licensing discriminator)
    quote: |
      …verbatim statement text, prefilled by `mfc registry mint` from get_chunk,
      confirmed by a human against the paper…
    quote_norm: "nfc-ws-collapse/1"  # sha256(NFC(" ".join(text.split())).encode())
    quote_sha256: "<64 hex>"
    mint_resolution:                 # REQUIRED, non-empty. An entry cannot exist until
      notebook: bridgeland-stability #   its quote has matched a live chunk at least once.
      chunk_id: "arxiv:math/0212237:a82c3230040fd724"
      matched_by: quote_sha256       # quote_sha256 | printed_number
      corpus_manifest_content_hash: "<64 hex>"
      observed_at: "2026-08-04T…Z"
    depends_on: ["stmt:9f4c1a20b7d3:bridgeland2007.defn-8.1"]
    frontier:                        # may be empty; must be present
      - id: gltilde-universal-cover
        kind_class: open-problem     # closed-lane | missing-library | open-problem | interface
        kind_label: "covering-space"
        statement: "GLTilde → GL⁺(2,ℝ) surjective, fibre ℤ, simply connected"
        discharged_by: null
    minted_at: "2026-08-04"
    minted_by: "Chris Dare"
    supersedes: null
    superseded_by: null
```

### 2. `attest/lean-emission.json` — generated by `lake exe mfc-emit`, **not committed**

The only file Lean writes. Contains **no digests** — Lean core ships no SHA-256 (Lake's `Hash` is a 64-bit non-cryptographic hash), and the consumer must be able to recompute anything it is served. All digesting is done by `mfc` in Python, on **both** sides, which also eliminates the cross-language-digest-implementation problem entirely.

```jsonc
{ "schema_version": "emission/1.0",
  "lean_version": "4.29.0", "lean_githash": "98dc76e…",
  "lean_options": {"autoImplicit": false, "relaxedAutoImplicit": false},
  "modules": ["BridgelandStabLean.Lattice.NumericalK", "…"],
  "counts": {"total": 121, "in_scope": 78, "internal": 43},
  "constants": [
    { "name": "BridgelandStabLean.Lattice.zsmul_injective",
      "module": "BridgelandStabLean.Lattice.Basic",
      "kind": "theorem",           // axiom|def|theorem|opaque|quot|inductive|ctor|rec
      "is_instance": false, "is_internal": false, "is_private": false,
      "num_levels": 0,
      "type_pp": "∀ (n : ℕ) …",    // rendered under pinned pp.all/pp.fullNames/pp.universes
      "value_pp": null,            // non-null ONLY for def/abbrev/opaque (statement-relevant)
      "local_deps": ["BridgelandStabLean.Lattice.NumLattice"],  // topic-local consts in the type
      "axioms": ["Classical.choice","Quot.sound","propext"],    // FULL transitive closure, SORTED
      "range": {"startLine":39,"startCol":0,"endLine":42,"endCol":27},
      "cites": [{"key":"stmt:9f4c1a20b7d3:…","relation_claimed":"one_way",
                 "frontier":["gltilde-universal-cover"],"note":"…"}] } ] }
```

**Scoping is by module, never by name prefix.** A declaration at root namespace or under a foreign namespace inside a topic module (`theorem sneaky : False := by sorry` outside `BridgelandStabLean.*`) still lands in the `.olean` and is importable downstream; prefix scoping misses it. `mfc-emit` selects on `env.getModuleIdxFor? n ∈ <the lean_lib's modules>`.

### 3. `attest/declarations.json` + `attest/environment.json` + `attest/bindings.json` — written by `mfc bundle`, **committed**

`environment.json` carries `env_digest`, `lean_toolchain`, `lean_githash`, resolved `lean_options`, `packages[] {name, rev, url}`, `root_package {name, rev, tag}`, `axiom_policy {allowlist[], additions[{axiom, justification}]}`, `emitter_version`, `repo_commit`.

`declarations.json` adds to each constant:

```jsonc
{ "statement_digest": "<64 hex>",   // Merkle: sha256(canonical_json({
                                    //   pp: type_pp,
                                    //   deps: {c: statement_digest(c) for c in local_deps}}))
                                    // where a local def/abbrev also folds value_pp in.
                                    // External (Mathlib/anchor) consts contribute name only —
                                    // env_digest already pins them.
  "axioms_disallowed": ["…"],       // RECOMPUTED by mfc, never trusted from the emission
  "contains_sorry_ax": false,
  "local_axioms": [] }
```

That Merkle construction is the repair for the flaw that killed Cairn on trust: swapping what `abbrev NumLattice : Type := Fin 2 → ℤ` unfolds to now changes the digest of every theorem whose statement mentions it, so a stale human review is forced to `stale` instead of riding along.

### 4. `attest/review.yaml` — hand-written by a named human. **The only contract file no machine may write.**

```yaml
schema_version: "review/1.0"
reviews:
  - key: "stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2"
    decl: "BridgelandStabLean.GroupAction.GLTilde"
    reviewer: {name: "Chris Dare", email: "…"}
    reviewed_at: "2026-08-11"
    reviewed_statement_digest: "<64 hex>"   # what the reviewer actually saw
    reviewed_quote_sha256: "<64 hex>"       # goes stale independently on the PAPER side
    reviewed_env_digest: "<64 hex>"
    faithfulness: adequate                  # adequate|divergent|inadequate|inconclusive
    relation_confirmed: one_way             # or `disputed`
    divergences: ["…"]
    note: "…"
```
An **absent** entry means not-reviewed and is distinct from every present value. `inconclusive` is a complete, legitimate outcome — abstention is a success.

### 5. `attest/build.json` and `attest/bundle.json`

`build.json` folds `lake env lean --json` NDJSON (verified: `data` strings are **unwrapped** in JSON — the 100-column wrapping that made `scripts/Audit.lean` unparseable is a terminal artifact) into `{lake_build_exit, jobs, diagnostics[], error_count, warning_count, sorry_diagnostic_count, independent_checkers[{name, result, allow_sorry}], ci{run_url, workflow_sha, runner}}`.

`bundle.json` is an **in-toto Statement v1**: one `subject` (`{name, digest:{gitCommit, gitTag}}`), N `predicates` each `{predicateType: <URI>, file, sha256, produced_by, produced_at, env_digest, self_attested}`. `contract_repo: {url, rev}` declares which contract version the producer satisfies. Unknown `predicateType` values are **ingested, never served, recorded as `unrecognized`** — that is the registry that makes the URI extension point safe.

**SLSA's VerificationSummaryAttestation is rejected**; its `verificationResult: PASSED|FAILED` is precisely the collapsed token §4.9 forbids.

### 6. `attest/resolution.json` — produced by arXMCP, **committed into the Lean repo**

```jsonc
{ "schema_version": "resolution/1.0",
  "registry_sha256": "<64 hex>",     // sha256 of the exact registry bytes this ran against
  "notebook": "bridgeland-stability",
  "corpus_version": 5048,
  "corpus_manifest_content_hash": "<64 hex>",
  "resolver_version": "…", "generated_at": "…",
  "results": [
    { "key": "stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2",
      "status": "current",           // current|drifted|unresolvable|paper_absent|not_run
      "matched_by": "quote_sha256",  // quote_sha256|printed_number|fuzzy|none
      "chunk_id": "arxiv:math/0212237:a82c3230040fd724",   // CACHE HINT, non-authoritative
      "matched_body_sha256": "<64 hex>",                   // REQUIRED when status==current
      "similarity": null } ] }
```
`registry_sha256` is the entire cross-repo freshness mechanism: one comparison, no clocks, no mtimes. Editing the registry without re-running the resolver turns the Lean repo's CI red. `matched_by: fuzzy` can **never** yield `status: current`.

### 7. `arxmcp://formal/{notebook}` and `arxmcp://formal/{notebook}/{key}` — MCP **resources**

Registered in `server/mcp_resources.py` after `register_all_tools`, before `mount_mcp`; wrapped in `<retrieved_formal_record>` per the existing `wrap_retrieved_text` discipline. **Key order is load-bearing**: `caveats[]` first, then `axes`, then evidence. The three existing guard tests (`test_tools_list_hash_unchanged_with_resources`, `test_resources_do_not_change_tools_vs_baseline`, `test_resources_add_no_tools`) must stay green with no re-pin — that is the mechanical proof of zero BP1 / zero `EXPECTED_TOOL_SCHEMA_SHA256` cost.

### Schema-versioning discipline

- `"<name>/<major>.<minor>"`. **MAJOR** = remove or retype a field, or narrow the meaning of an enum member → consumers **hard-refuse**, never best-effort parse. **MINOR** = add an optional field or an enum member → consumers accept MINOR ≤ theirs. Every MINOR addition requires a new fixture; every MAJOR requires a `copier update` that all N topic repos take, and a migration script in `math-formal-contract/migrations/<from>-to-<to>.py`.
- `contract.lock` on both sides pins the contract repo by **40-hex, never a branch**; `mfc` verifies the vendored `contract/` tree hashes to the pin. `copier update` opens PRs; it **never auto-merges**, and a MAJOR bump fails the consumer's CI until a human acts. (FROZEN WIRE's `bump_consumers.py` auto-re-green conveyor is explicitly rejected.)

---

## The identifier scheme

```
key         = "stmt:" registry-id ":" local-label
registry-id = [0-9a-f]{12}          ; minted once by `mfc registry init`, in the file header
local-label = ^[a-z][a-z0-9._-]{0,63}$
```

**Why the paper coordinate is not in the key.** Three of the four candidate designs put `arxiv:<id>v<n>` into a colon-positional key. That fails on `math/0212237` only by luck (no colon) and fails outright on `textbook:<slug>` — which arXMCP ships today (`ingest/identifiers.py`, `tools/notebook_textbook_ingest.py`, live notebooks `bridgeland-stability-pdfs` and `fourier-duality-pdfs`) — and it silently blesses `doi:` with an immutability guarantee DOIs do not have. Putting the coordinate in **typed, schema-validated fields** is strictly better: `version` can be `required` when `scheme == arxiv` and absent for `textbook`, and no tokenizer can be broken by an id containing a delimiter.

**Why `registry-id` and not the notebook slug.** Notebook slugs are `^[a-z][a-z0-9-]{2,30}$` rows in a machine-local, unauthenticated sqlite DB with no global registry. Two adopters both minting `number-theory` collide. A 12-hex minted once and checked into git is globally unique in practice and a collision is detectable and fixable.

**Why it survives a re-ingest that rotates every `chunk_id`.** Nothing arXMCP computes appears in it. Not `chunk_id`, not `corpus_version` (a LanceDB MVCC integer that a restore-from-backup can present *lower* over different bytes), not `parse_artifact_sha256`, not the notebook slug. `make ingest-recover-preambles`, a chunker bump, an ar5iv re-render, a LaTeXML upgrade, an HTML→MinerU migration — none can invalidate a string they never contributed to.

**Why it survives an arXiv version bump.** It doesn't, and that is correct: `math/0212237v1` §8 Lemma 8.2 and `math/0212237v2` §8 Lemma 8.2 are different statements if the author renumbered or edited. A version bump means a **new key** with `supersedes` pointing at the old one. The old key stays valid forever and keeps its quote.

**Resolution ladder — Lean side (authoritative, offline, arXMCP deleted from the machine):**
the entry carries `quote` and `quote_sha256`. `mfc lint` recomputes the hash from the inline quote. A human resolves the key by opening `arxiv.org/abs/<id>v<n>` and reading §8. **Nothing in the contract requires arXMCP to be running, installed, or ingested.**

**Resolution ladder — arXMCP side (advisory, drift detection):**
1. `mint_resolution.chunk_id` → fetch, recompute `sha256(NFC(" ".join(body_text.split())))`, accept only on match. A rotation invalidates the cache; it never corrupts the answer.
2. Scan the paper's chunks for the same hash → `matched_by: quote_sha256`. This is the `source_span.txt` mechanism (`ingest/schema.py:240-250`, "the authoritative resolving key") which is **100% NULL live** — so `mfc` computes it at mint time and the design does not wait on the unshipped forward-wiring.
3. Fall back to `printed_number` → `matched_by: printed_number`. Hint only: `_extract_printed_number` lives in the ar5iv/LaTeXML chunker; the textbook and MinerU paths never populate it, and coverage is 36 of 66 chunks even on the flagship paper.
4. Otherwise `status: drifted` or `unresolvable`, with the reason. **It never guesses**, and a fuzzy match can never be `current`.

**Poisoning.** arXMCP has no authentication and a 17-route unauthenticated `/ui/api` mutation plane. The frozen `quote_sha256` is the substitute: anything that alters a registered statement's text flips resolution away from `current`, which reddens the Lean repo's CI. It is trust-on-first-use, not authentication — mint-time resolution is what bounds the window, and the design says so rather than overclaiming.

### Worked example — Bridgeland 2007, Lemma 8.2

Registry entry (`registry/bridgeland2007.yaml`):

```yaml
"stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2":
  kind: lemma
  title: "Lemma 8.2"
  source:
    scheme: arxiv
    id: "math/0212237"
    version: "v?"           # ← MUST BE CONFIRMED, see Open Questions.
    printed_number: "8.2"   # verified present in the corpus for this chunk
    locator: "§8"
  quote_mode: verbatim
  quote: |
    <prefilled by `mfc registry mint --from-chunk arxiv:math/0212237:a82c3230040fd724`,
     then confirmed by a human against the PDF>
  quote_norm: "nfc-ws-collapse/1"
  quote_sha256: "<computed by mfc over the inline quote>"
  mint_resolution:
    notebook: bridgeland-stability
    chunk_id: "arxiv:math/0212237:a82c3230040fd724"    # the audit's recomputed, verified id
    matched_by: quote_sha256
    corpus_manifest_content_hash: "<64 hex>"
    observed_at: "2026-08-04T…Z"
  frontier:
    - id: gltilde-universal-cover
      kind_class: open-problem
      statement: "GLTilde → GL⁺(2,ℝ) surjective, fibre ℤ, simply connected"
      discharged_by: null
```

Lean side (which declaration binds, and at what strength, is the author's assertion and a reviewer's to confirm — I am not asserting the mathematics):

```lean
@[cites "stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2"
        (relation := one_way)
        (frontier := ["gltilde-universal-cover"])]
theorem BridgelandStabLean.GroupAction.… : … := …
```

Now trace three events.

*A re-ingest rotates every `chunk_id`.* The key is unchanged. `statement_resolve.py` finds `a82c3230040fd724` gone, scans, matches `quote_sha256` against the new chunk, writes `status: current, matched_by: quote_sha256, chunk_id: <new>, matched_body_sha256: <64 hex>`. The Lean repo commits the new `resolution.json`. **No Lean source changes, no key changes, no review goes stale.**

*A LaTeXML upgrade rewrites the rendered text.* `status: drifted`. CI reddens. A human adjudicates: either the render changed (re-mint the quote, append a new entry with `supersedes`) or the paper changed (new arXiv version, new key). Loud, not silent.

*`abbrev NumLattice` is redefined in the Lean repo.* `local_deps` puts `NumLattice`'s digest inside the dependent theorem's `statement_digest`; the digest changes; `statement_stable` flips to `fail` against `reviewed_statement_digest`; the served record's `faithfulness` renders `stale`. This is the case Cairn missed.

---

## Trust model

Seven axes. Values `pass | fail | not_run | not_applicable`. **No aggregate field exists in any schema**, and `additionalProperties: false` means a producer cannot add one.

The independence rule, stated precisely because two candidate designs failed it: *two axes are distinct only if they have distinct evidence-producing programs.* Three views of one axiom closure are one axis.

| # | Axis | Asserted by | Verifiable by | Evidence (required, schema-enforced) |
|---|---|---|---|---|
| 1 | `elaborates` | Lean elaborator, producer CI | anyone who rebuilds at the pin | `{lake_build_exit, error_count, diagnostics[]}` |
| 2 | `kernel_replay` | an independent kernel checker over the built oleans | anyone who reruns the checker | `{checker, version, allow_sorry:false}` |
| 3 | `axiom_closure` | `Lean.collectAxioms`, producer | anyone who reruns `mfc-emit` | `{policy_allowlist[], observed[], disallowed[], contains_sorry_ax, local_axioms[]}` — **the set, never a boolean** |
| 4 | `statement_stable` | `mfc`, comparing `statement_digest` to `reviewed_statement_digest` | anyone with both files | `{current, reviewed, env_digest, reviewed_env_digest}` |
| 5 | `binding_resolves` | **arXMCP's resolver** — a different system | anyone with the corpus | `{status, matched_by, matched_body_sha256, corpus_manifest_content_hash}` |
| 6 | `frontier_discharged` | `mfc`, over the registry dependency graph | anyone with the registry | `{open[], discharged[]}` |
| 7 | `faithfulness` | **a named human, dated. Never computed, never defaulted.** | another human | `{reviewer, reviewed_at, relation_confirmed, divergences[]}` |

Every axis record additionally carries `env_digest`, `computed_at`, `source`, `self_attested: bool`, and — when produced in CI — `ci: {run_url, workflow_sha, runner}`. `self_attested` is honest labelling for a solo-operated repo: it says "the party that wrote the code also produced this measurement," which is true for axes 1–4 and 6, and false for 5.

**Sorry-laundering — five independent blocks, three of them mechanical and one independent of the elaborator.**
1. The emitter derives everything from `Environment.constants` + `Lean.collectAxioms`. It **never parses source**, so `set_option maxHeartbeats 400000 in theorem sneaky : False := bad` and `open Classical in theorem …` — both of which the audit reproduced defeating `_DECL_SITE_RE`/`_DECL_NAME_RE` with `complete=True` and `outcome:"clean"` — are simply constants in the environment.
2. Module-scoped, not prefix-scoped, so a root- or foreign-namespace declaration inside a topic module cannot hide.
3. `lake exe mfc-emit` **exits non-zero** on `sorryAx`. Nothing in the default path does: measured on this toolchain, `lake env lean` exits 0 while `#print axioms` prints `[sorryAx]`, and still exits 0 under `-E hasSorry`. `assert_no_sorry` (verified present at `.lake/packages/mathlib/Mathlib/Util/AssertNoSorry.lean`) is the belt-and-braces command that also errors.
4. Independent kernel replay with `allow_sorry: false`. **Unverified**: I could not confirm offline that `leanprover/lean-action` exposes `leanchecker`/`nanoda`/`nanoda-allow-sorry` inputs, or that `nanoda-allow-sorry` defaults to `true`. If they do not exist, axis 2 ships `not_run` — honest, and the design does not silently count it.
5. Schema: `contains_sorry_ax: true` with `axiom_closure: pass` is invalid; `mfc` **recomputes** `axioms_disallowed` rather than trusting the emission; `git diff --exit-code attest/` rejects a hand-edited bundle in producer CI; and `tools/formal_release_pin.py` re-derives every file digest **from the git tag object** (`git rev-parse`, `git cat-file`), refusing a dirty worktree — so the gates survive the seam, which they did not in ABR as drawn.

The repo's stronger norm is preserved and is *better* than any of this: an unproved result is **not declared**. It is a registry entry of `kind: obligation` with `decls: []` that appears in the work queue — navigable, not invisible.

**Same-name-different-statement drift.** `statement_digest` is a Merkle root over the type's rendering *plus the digests of every topic-local constant the type mentions* (including a local `def`/`abbrev`'s value). Renaming nothing while changing what a definition means changes the digest, which forces `statement_stable: fail` and renders `faithfulness: stale`. Within a fixed environment this is enforceable. Across a toolchain bump it is not — a pretty-printer change rotates everything at once — so `statement_stable` is **`not_applicable`** across environments, never `pass`, and the record says so. **v1.1 hedge, not v1**: `mfc-emit --restate-check` re-elaborates the recorded `pp.all` string in the new environment and checks `isDefEq` against the current type, which distinguishes pretty-printer drift from statement drift. `pp.all` output is round-trippable by construction, so this is the mechanism Cairn declared not to exist; it is deferred only because `elabTerm`/`isDefEq` availability at v4.29.0 is unverified.

**Toolchain skew.** Every digest carries `env_digest`, computed from `rev` fields (never `inputRev` — nine packages track branches) plus resolved `leanOptions`. A consumer reading an axis whose `env_digest` differs from the record's environment **must** render `not_applicable`. arXMCP therefore cannot produce axes 1–4 for this repo at all, which is the correct encoding of "arXMCP's REPL is v4.31.0 and the pin is v4.29.0." `lean_verify` output, if ever cited, gets `predicateType: .../provisional-self-reported/v1`, which satisfies zero axes.

**Over-reading by an LLM consumer — four mechanisms, all mechanical.**
1. `relation_claimed` is the only spelling permitted in machine artifacts. `relation_confirmed` appears **only inside a review record**. An agent reading `relation_claimed: exact` with `faithfulness: not_run` reads the word "claimed". This is the repair for the composition-level collapse that killed FROZEN WIRE.
2. The served record's **first key** is `caveats[]`, generated mechanically from the axis values, e.g. `"faithfulness: not_run — no human has compared this Lean statement to the paper"`; `"axiom_closure: pass — this says nothing about whether the statement is the paper's"`; `"frontier: 1 undischarged item (gltilde-universal-cover) — this is a theorem about the interface, not about the object"`. Generated, so it cannot drift.
3. `assumption_frontier` is **required, may be empty, must be present**, and `mfc lint` **rejects an empty frontier when `relation_claimed ∈ {specialization, one_way, reformulation}`** and requires a non-empty `note` when `no_claim`. **[Superseded 2026-08-04: `reformulation` is struck from the enum — it was never given a meaning, and the rule now reads `∈ {specialization, one_way}`. Rationale in the fourth correction at the head of `2026-08-04-contract-schemas.md`. Left in place here because this note is a dated record of what was designed, not of what shipped.]** Plus per-topic `closed_lanes` are mechanized as `forbidden_module_prefixes` / `forbidden_constants` checked against the emission — so "the geometric lane is closed" is a build failure, not a paragraph.
4. `not_run` and `not_applicable` are structurally distinct from `fail` and from `pass`, and `required_axes` filtering at the serving layer is **fail-closed**: a caller asking for `faithfulness=adequate` gets nothing back for an unreviewed entry, never a downgraded record. A fixture (`not-run-as-pass`) rejects any consumer that collapses them.

**Honest limit, stated once and in the served record:** a matching `statement_digest` means *unchanged since a human looked*. It never means *faithful to the paper*. A digest cannot detect that `Fin 2 → ℤ` was described as a Kuznetsov component; only a human reading both can. TheoremGraph's 22/24-typecheck versus 5/24-faithful is the reference gap.

---

## Generalization to a new topic

**Mechanism:** `math-formal-contract` is simultaneously the spec, the fixture corpus, the `mfc` CLI, the **shared Lake package**, and the copier template. Zero bytes anywhere in it mention Bridgeland, and — this is the change from all four candidates — the emitter is a **library in a pinned dependency**, not a templated metaprogram. The topic repo's only generated Lean file is three lines:

```lean
import MathFormalContract.Emit
def main (args : List String) : IO UInt32 :=
  MathFormalContract.emitMain (rootLib := `BridgelandStabLean) args
```

The emitter loads the topic's environment with `Lean.initSearchPath` + `Lean.importModules` — the same pattern `importGraph` (already in this repo's package tree) and doc-gen4 use. So `copier update` never 3-way-merges 200 lines of Lean, and the emitter's toolchain compatibility is CI-matrixed once, in the contract repo, rather than N times.

The `@[cites]` attribute is a `SimplePersistentEnvExtension` modeled on `Mathlib/Tactic/StacksAttribute.lean` (verified present at the pin). It lives in the **shared package** — vendoring it would make two topic repos unable to coexist in one environment, since duplicate attribute registration is an import-time error.

**Copier answers:** `topic_slug`, `root_namespace`, `lean_toolchain`, `anchor` (**optional** — `{name, git, rev:40hex}`; when omitted, `mathlib_rev:40hex` becomes required and the generated lakefile requires Mathlib directly, with a §1 worded as a rule about *the topmost pin* rather than about the anchor), `notebook_hint`, `axiom_policy {allowlist[], additions[{axiom, justification}]}`, `closed_lanes[{name, forbidden_module_prefixes[], forbidden_constants[], note}]`, `frontier_kind_labels[]`.

**Numbered walkthrough — adopter #2, "analytic number theory," Iwaniec–Kowalski + arXiv, no upstream anchor, Mathlib coverage high:**

1. `make init NOTEBOOK=analytic-nt EMAIL=…` in arXMCP; hand-edit `papers.txt`; `notebook_fetch`; `notebook_ingest`. *(Unchanged. arXMCP's notebook standup is un-mechanized today and this design does not fix it; `mfc init` prints the exact command sequence including the three silently-skippable steps that left `bridgeland-stability` with `display_name=""` after 13 ingest runs.)*
2. `pipx install "git+…/math-formal-contract@<40hex>"`.
3. `mfc init --topic analytic-nt --no-anchor --mathlib-rev <40hex> --toolchain leanprover/lean4:v4.31.0` → renders the topic repo: lakefile with the direct Mathlib pin and `[[lean_lib]] Scripts`, `scripts/Emit.lean` (3 lines), `.github/workflows/contract.yml`, `contract/` vendored + `contract.lock`, `registry/.gitkeep`, `formalization.yaml` skeleton with every unfillable field `none`/`pending`, `CLAUDE.md` with the four invariants parameterized.
4. `mfc registry init` → mints a fresh 12-hex `registry_id`.
5. `lake exe cache get && lake build && lake exe mfc-emit && mfc bundle` — an emission and an `env_digest` exist **before a single entry is minted**.
6. `mfc registry mint --notebook analytic-nt --paper arxiv:2401.01234v2 --printed-number 3.7 --kind theorem` → prefills the quote from `get_chunk`, computes the hash, records `mint_resolution`. Human confirms against the paper and edits `informal`/`frontier`. For a textbook source: `--paper textbook:iwaniec-kowalski --locator "Thm 5.8, p.112"` with `quote_mode: digest_only` if licensing requires.
7. Annotate declarations with `@[cites]`. For this topic most bindings are `relation_claimed: exact` with empty frontiers, because Mathlib has the substrate — the vocabulary degrades correctly at both coverage extremes (`no_claim` + non-empty frontier at one end, `exact` + empty at the other).
8. `mfc lint && mfc conformance && git tag v0.1.0`.
9. arXMCP: `make formal-resolve NOTEBOOK=analytic-nt REGISTRY=…` then `make formal-pin NOTEBOOK=analytic-nt REPO=… TAG=v0.1.0`. **Zero new code in arXMCP. Zero schema migration. Zero `EXPECTED_TOOL_SCHEMA_SHA256` re-pin. The resources template on `{notebook}` and pick it up.**

**What genuinely does not generalize, stated rather than hidden:** minting is human labor and does not scale past the low tens of entries; `printed_number` exists only on the ar5iv/LaTeXML path so textbook and PDF-OCR topics fall straight to `quote_sha256`; and the mathematics is not helped by any of this.

---

## Testing strategy

Neither repo has CI today. Both get one job. **The cross-repo test crosses no network boundary, because the contract artifact is a file.**

**Producer — `bridgeland-stab-lean/.github/workflows/contract.yml`:**
- `leanprover/lean-action@<sha>`: `build: true`, `use-mathlib-cache: true`, and (if the inputs exist) `leanchecker: true`, `nanoda: true`, **`nanoda-allow-sorry: false`** — the default is `true`, and leaving it adds a check that passes on sorry-backed proofs. Consume the per-axis outputs; there is deliberately **no aggregate `status` output** in lean-action, which is §4.9 already shipping.
- `lake exe mfc-emit --out attest/` → `mfc bundle attest/` → `mfc lint` → `mfc conformance`.
- `mfc check-ilean-coverage` — set-diff `.lake/build/lib/lean/**/*.ilean` `decls` against the emission. This catches a module covered by no `lean_lib` (today `scripts/` is covered by none, so `Audit.lean` is not built by `lake build` and its own header admits it can rot), **and** it is the vacuous-pass guard: `mfc lint` fails if `constants[] == []` or if any `.ilean` decl is missing. That is the repair for FTC's null acceptance test.
- `mfc check-resolution` — `resolution.json.registry_sha256` vs the current registry bytes.
- Reproducibility: re-run the emitter and assert byte-identity modulo `{emitted_at}`. Verified achievable — the ground-phase probe produced byte-identical output across two runs. **Fix required first**: `collectAxioms` output is *unsorted* (`probe-inventory.json` shows `["propext","Quot.sound","Classical.choice"]` on one declaration and `["Quot.sound","propext","Classical.choice"]` on the next). Sort every emitted array.
- `git diff --exit-code attest/`.

**Consumer — `arXMCP/.github/workflows/ci.yml` (deliberately cheap: no LanceDB, no Lean, no models, no network):**
- existing `pytest`, plus `mfc conformance` over the vendored fixture corpus.
- `tests/test_statement_resolve.py` — a synthetic 3-chunk fixture, then **rotate every chunk_id** (mutate whitespace, which changes `chunk_id` but not `quote_sha256` under `nfc-ws-collapse/1`) and assert every entry still resolves `current` via `quote_sha256`; assert a genuinely-removed statement yields `unresolvable`, never a wrong match. *This single test is what proves the identifier scheme works.*
- `tests/test_formal_release_pin.py` — a **tampered bundle is refused**: flip `contains_sorry_ax`, recompute the file's sha256 into `bundle.json`, and assert the pinner still refuses because it re-derives from the git tag object.
- `tests/test_formal_resource.py` — asserts `EXPECTED_TOOL_SCHEMA_SHA256` is **unchanged**, mechanically proving the zero-BP1 claim.

**Cross-repo — the Bowtie / JSON-Schema-Test-Suite model.** The fixture corpus lives in `math-formal-contract`, in neither implementation, in a language-neutral format. Both sides vendor it at a pinned commit and run it locally; neither can drift the tests toward its own behavior and neither needs the other running. Then **one** integration job in the contract repo clones both siblings at pinned commits and runs `mfc join` — a pure function of two directories of JSON.

**Adversarial fixtures (`testdata/invalid/`; arXMCP has zero today).** Each named for the failure it reproduces, each MUST be rejected: `sorry-laundered`, `axiom-injected` (mfc recomputes), `env-digest-mismatch`, `stale-review`, `unknown-key`, `key-is-chunk-id-shaped`, `source-arxiv-unversioned`, `aggregate-status` (rejected by `additionalProperties: false` — this is the one that turns the trust-language policy from review habit into machine constraint), `axis-without-evidence`, `not-run-as-pass`, `empty-emission` (vacuous pass), `relation-exact-with-frontier`, `resolution-current-without-body-digest`, `foreign-env-attestation` (must render `not_applicable`). Plus `testdata/valid/textbook-source` — a `scheme: textbook` entry with no arXiv version, which **must validate**.

**One fixture is not JSON.** `testdata/lean/set-option-evasion/` is a real, minimal Lean project containing `set_option maxHeartbeats 400000 in theorem sneaky : False := by sorry`, compiled by the contract repo's Lean CI matrix. The emission must list `sneaky` and the emitter must exit non-zero. A JSON fixture here would pass by construction and test nothing — that was Cairn's mistake.

---

## Migration

| # | Repo | Change | Effort | What becomes true |
|---|---|---|---|---|
| 0 | Lean | `formalization.yaml`: `source.id` gains `v<n>` (**confirm, do not guess** — the live corpus has `arxiv_version = ''` for `math/0212237`); delete the "mirrors the anchor key-for-key" comment (the audit proves seven shared keys differ in type and the anchor's first key `schema_version` is absent); replace with an honest one-liner. | 30 min | A live silent-drift hazard is closed and the file stops making a false claim about itself. |
| 1 | Lean | `lakefile.toml`: `[[lean_lib]] name = "Scripts"`. | 15 min | `scripts/` is actually built by `lake build`; `Audit.lean` can no longer silently rot. |
| 2 | Contract | Create `math-formal-contract`: 7 JSON Schemas, the fixture corpus (14 invalid + the textbook-valid case), `mfc` (`validate\|bundle\|lint\|lint-schemas\|registry\|conformance\|join\|init`). Deps: `jsonschema`, `pyyaml`, `copier`. | 2 evenings | The spec exists and is green on its own conformance before either sibling touches it. |
| 3 | Contract | `lean/` Lake package: `@[cites]` + `#cites_dump` + `MathFormalContract.Emit` (hardening the verified probe: sort arrays, module-scope, `pp.all`, emit `local_deps`, no digests). CI matrix over ≥2 toolchains. Add `testdata/lean/set-option-evasion/`. | 2 evenings | The emitter is a shared, version-matrixed binary rather than N vendored copies. |
| 4 | Lean | `[[require]] MathFormalContract … subDir = "lean"` at exact 40-hex; `scripts/Emit.lean` (3 lines); `[[lean_exe]] mfc-emit`; `make attest`; vendor `contract/` + `contract.lock`. | 1 evening | `make attest` produces a full bundle from the pinned environment. |
| 5 | Lean | **First CI ever.** lean-action + `mfc-emit` + `mfc bundle` + `mfc lint` + `mfc check-ilean-coverage` + `git diff --exit-code attest/`. | 1 evening | `builds_clean: true` and `axiom_count: 0` stop being unreproducible assertions about one workstation. Update `formalization.yaml.machine_review` in the same commit. |
| 6 | Lean | `mfc registry init`; mint 6–10 entries for `math/0212237v<n>` with quotes prefilled from `get_chunk` (start with `lem-8.2` / `prop-8.1`, whose chunk ids the audit already recomputed and confirmed). Annotate declarations with `@[cites]`. **Expect this to fail loudly on `GLTilde`** — the name asserts a universal cover the repo has not proved, so `relation_claimed: one_way` with an open frontier, which is the design working. | 1 evening | The interface has an identifier for the first time. A repo-wide grep of all tracked Lean-repo files for `arxmcp\|arxiv:\|chunk_id` currently returns **zero hits**. |
| 7 | arXMCP | `tools/statement_resolve.py` + `make formal-resolve` + tests + **arXMCP's first CI**. Run it against `bridgeland-stability` and measure how many entries resolve by `quote_sha256` vs `printed_number` vs not at all. | 1 evening | **The gamble resolves.** Deliberately before any template work, so the answer is known before the pattern is cloned. |
| 8 | Both | Commit `resolution.json` into the Lean repo; CI green; `git tag v0.1.0` with `attest/*` as release assets. | ½ day | **The first release in this repo's history.** Until now R5's premise — "pins *released* formalizations" — is literally false. |
| 9 | arXMCP | `tools/formal_release_pin.py` (fetch by **tag**, re-derive digests from git objects, refuse dirty worktree or mismatch) + `notebooks.db` v5→v6 `formal_releases` table via the documented recipe at `notebooks_store.py:60-67`. **In the same change**, fix `tools/notebook_restore.py`, which writes the `notebooks` table by raw sqlite3 with no `user_version` handling and re-arms the v0→v1 unconditional DROP. | 1 evening | **The contract exists.** The artifact both repos call "the entire interface" gets its first reader, on the consumer side, per Pact. |
| 10 | arXMCP | Register `arxmcp://formal/{notebook}` and `/{key}` in `server/mcp_resources.py`; add the guard test asserting `EXPECTED_TOOL_SCHEMA_SHA256` unchanged. | 1 evening | An agent can read the trust record. Zero BP1 cost, proved rather than asserted. |
| 11 | Lean | First human faithfulness review: 2–3 entries, named, dated, with `reviewed_statement_digest` + `reviewed_quote_sha256` + `reviewed_env_digest`. | ½ day | `human_review` stops being `none` for the first time — and only for those entries. `statement_stable` acquires a baseline and starts detecting the drift the audit called undetectable. |
| 12 | Contract | `template/` + copier, then the **second-topic gate**: stand up a deliberately *different* topic end-to-end — no anchor, Mathlib-complete, at least one textbook-sourced entry, ≥1 real binding reaching `relation_claimed: exact`. Publish the template **only after** this passes. | 2 evenings | Generalization is demonstrated, not asserted. This is the step all four candidates deferred to last and one of them made unfalsifiable. |
| 13 | arXMCP | Fix `_DECL_SITE_RE`/`_DECL_NAME_RE`; ship the frozen `lean_verify_result.json` as the advertised `outputSchema`; land R3-m1's `status:"ok"` → `elaborated_no_errors` rename — **all in one commit**, one `TOOL_SCHEMA_VERSION` bump, one BP1 invalidation. | ½ day | Not part of the contract, but it is on the same wire an agent reads: today an agent can get `outcome: "clean"` on a sorry-backed proof from the tool next to the honest record. |
| 14 | Both | Prose. Lean `CLAUDE.md §8` cites arXMCP §4.8 for a rule §4.8 does not contain and uses present indicative for an unshipped R5; rewrite against what shipped. Add the reciprocal section to arXMCP (which today has **zero** mentions of the sibling — the contract is unilateral). Mirror §4.8/§4.9 into arXMCP's untracked `AGENTS.md`, which has neither. | ½ day | A non-Claude agent in either repo receives the boundary. |

---

## Open questions for the user

1. **Which arXiv version of `math/0212237` was §8 formalized against?** `documents.db` in the live `bridgeland-stability` notebook records `arxiv_version = ''` (empty), so **nothing on this machine knows**. Everything downstream pins it, and the unversioned form silently resolves to arXiv's latest. This must be confirmed by opening the abstract page, not inferred — I have deliberately written `v?` everywhere above rather than guess.

2. **Third repo, or `contract/` inside arXMCP?** I recommend the third repo (`math-formal-contract`), and I am flagging that this **contradicts a recorded verdict**: `_pipeline/stage-1-discovery/synthesis/target-architecture.md:113-126` says "NOT NOW — create on trigger," rejecting a third repo because it "would be nearly empty (a handful of schemas)," and assigns contracts custody to `math-research-orchestrator` on creation. My argument for overriding it: the conformance corpus *must* live outside both implementations or neither side can be prevented from drifting tests, and with N topic repos it cannot live in any one of them. The cheaper alternative is `arXMCP/contract/` vendored by topic repos — which is defensible under Pact (the consumer writes the contract) but means adopter #2 needs commit rights or a fork. Your call; the schemas and fixtures are identical either way.

3. **Shared Lake dependency, or vendored attribute?** The `@[cites]` attribute and emitter as a `[[require]]` at exact commit costs **one more pin per topic repo**, against `CLAUDE.md §1`'s "a second pin is a second thing to drift." Vendoring avoids the pin but makes two topic repos permanently unable to share a Lean environment (duplicate attribute registration is an import-time error). I recommend the dependency, on the grounds that it is a leaf package with **zero** transitive dependencies (core Lean only, no Mathlib), so it is the least drift-prone pin in the tree. But §1 is your rule.

4. **What is the registry's size ceiling, and who reviews?** `faithfulness` is the only axis that can catch the model-vs-geometry conflation, it is human-only, and R5 budgets ~2 owner-days for 5–10 entries against a notebook of 146 papers and 15,280 chunks. Everything else in this design scales; this does not. Is the answer "10 curated entries, permanently," or is there a second reviewer, or do you want an explicit `faithfulness: agent_drafted` sub-state (which I have deliberately **not** included, because it would let an LLM verdict occupy the one human axis)?

5. **Quote licensing — `verbatim` or `digest_only` by default?** Registry entries inline verbatim statement text. Bridgeland 2007 is arXiv perpetual-non-exclusive, so this is fine here. A future adopter's source may not be, and `digest_only` mode weakens offline verification (the Lean repo can no longer recompute its own hash) and degrades resolution to `printed_number`, which is exactly the field most likely to be absent on textbook and PDF-OCR sources. Do you want `quote_mode` required from v1 (my recommendation, so the two grounding strengths are always distinguishable in the served record), or is verbatim-only acceptable for now?