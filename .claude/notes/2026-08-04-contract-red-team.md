## Ranked gaps

---

**1 — Axis 5, the only independently-produced axis, is unsound w.r.t. arXiv versions and has no freshness gate.**
**Severity: critical.**
Evidence: I queried both live notebooks — `arxiv_version` is `''` for **every** row, not just `math/0212237`:
```
var/arxmcp/notebooks/bridgeland-stability/documents.db → ('0705.3794',''), ('0708.2247',''), … (all 8 sampled)
var/arxmcp/notebooks/fourier-duality/documents.db     → ('0708.3055',''), ('0809.4942',''), … (all 8 sampled)
```
So the design's Open Question 1 is understated: it is not "we don't know which version §8 was formalized against," it is "the corpus structurally cannot represent a version for any paper." Consequences: (a) `notebook_fetch` pulls ar5iv for the bare id = arXiv *latest*, so after arXiv posts v3 and the operator re-ingests, `statement_resolve.py` matches `quote_sha256` against v3 bytes and writes `status: current` for a registry entry declaring `version: v2` — the record asserts a v2 pin confirmed by unknown-version bytes; (b) `corpus_manifest_content_hash` hashes `(work_id, arxiv_version, …)` with `arxiv_version=''`, so it cannot distinguish versions either, and the `mint_resolution` stamp is not the guard it looks like; (c) `mfc check-resolution` compares only `registry_sha256` against the *registry* bytes, so a `resolution.json` produced on mint day stays `pass` indefinitely — nothing in producer CI notices that the corpus moved. The one axis the design points to as "a different system, a different program" is therefore a stale assertion about an unidentified document version.
Fix: `resolution.json` gains `resolved_source_version` and `corpus_manifest_content_hash`; `statement_resolve.py` emits `status: not_applicable` (never `current`) when `documents.arxiv_version == ''`; producer CI fails when `resolution.corpus_manifest_content_hash` differs from the live manifest *or* when `generated_at` exceeds `resolution_max_age_days`. Prerequisite: an arXiv-version backfill in arXMCP ingest — that is a third arXMCP change, not two, and it should be added to the migration table before step 6.

---

**2 — Coverage is never computed. At achievable human throughput the contract serves ~10 records against 15,280 chunks and an agent will correctly conclude the surface is empty.**
**Severity: critical.**
Evidence: R5 budgets ~2 owner-days for 5–10 faithfulness reviews (≈2 h/entry); minting (confirm quote, write `informal`, enumerate `frontier`) is another 20–40 min. Ten entries ≈ 5–8 owner-days. The notebook has 146 papers / 15,280 chunks. One entry per paper ≈ 36–73 owner-days ≈ 2–4 months full-time for one person. The design's own honest-limits paragraph says "minting is human labor and does not scale past the low tens" and then never carries the number forward into the serving design. Hit rate for `arxmcp://formal/{notebook}/{key}` at 10 entries is ~0.07%. An LLM that queries the formal surface three times, gets nothing, and stops querying is the rational outcome — and that reproduces the exact failure the audit found ("the artifact both repos call 'the entire interface' has no consumer"), one level up.
Fix: make coverage a first-class dated census on the index resource (`{entries, papers_covered, corpus_chunks, generated_at}`) — arXMCP §4.9 already mandates "novelty claims are dated censuses," so this is policy-compliant rather than new. Add a **non-trust lane**: `kind: sketch` entries that are agent-drafted, satisfy **zero** axes, are excluded from `required_axes` filtering, and carry a mandatory caveat. The design deliberately rejected `faithfulness: agent_drafted` — correctly, because it would let an LLM occupy the human axis — but rejecting it *without* a substitute means volume is unreachable by any route. A separate lane occupies no axis and is the graceful degradation the design currently lacks.

---

**3 — Minting requires corpus access from `mfc`, which contradicts the cold seam, the declared dependency set, and the migration ordering.**
**Severity: high.**
Evidence: `mfc` deps are stated as `jsonschema, pyyaml, copier`. Walkthrough step 6 is `mfc registry mint --paper arxiv:2401.01234v2 --printed-number 3.7` which "prefills the quote from `get_chunk`." With those three deps it can reach neither LanceDB nor a loopback MCP server. Worse, `--printed-number` needs a printed-number→chunk lookup that **does not exist** (audit §4: "No tool accepts `printed_number` as an input… there is no 'fetch the chunk numbered 8.2' path"). Worse still, `mint_resolution` is schema-`REQUIRED` and non-empty, so *no registry entry can be created* until a resolver exists — but the resolver is migration step 7 and minting is step 6.
Fix: minting belongs in arXMCP as `tools/statement_mint.py`, offline and read-only, on the same plane as `statement_resolve.py` (three arXMCP CLIs, not two); it emits a candidate YAML fragment the human pastes into `registry/`. Reorder migration: 7 before 6. Relax `mint_resolution` to optional-with-`reason` so an offline adopter with no arXMCP can still mint (the design elsewhere claims arXMCP is not required — this field silently makes it required).

---

**4 — `git diff --exit-code attest/` can never pass as specified.**
**Severity: high** (it is one of four claimed sorry-gates, and the one that survives the seam).
Evidence: `bundle.json` carries `produced_at` per predicate and `contract_repo`/`ci` metadata; `build.json` carries `ci{run_url, workflow_sha, runner}`. Both are committed. Both change every run. The determinism assertion is scoped only to "re-run the emitter and assert byte-identity modulo `{emitted_at}`" — which covers `lean-emission.json`, an *uncommitted* file, not the committed bundle.
Fix: split volatile provenance into `attest/run.json`, uncommitted and attached as a release asset; or add `mfc bundle --normalize` that zeroes a named field list, and state that list in the schema. Either way the gate must be tested by a fixture, or it will be quietly deleted the first time CI reddens on a no-op commit.

---

**5 — No revocation. A published record cannot be retracted after a human review says "not faithful."**
**Severity: high. Nobody in the batch addressed failure mode 4.**
Evidence: `review.yaml` has `faithfulness: divergent|inadequate`, and the registry has `superseded_by` — but both live *inside the producer's next tag*. arXMCP pins one tag in `formal_releases` and "re-serves verbatim"; it "may downgrade an axis from its own fresher resolution" but has no path to remove a record and no `withdrawn` state anywhere in the seven artifacts. If v0.1.0 is pinned and v0.2.0 marks an entry `inadequate`, the pinned surface keeps serving the old record until a human re-pins — and nothing tells them to.
Fix: add `withdrawals.yaml` (producer-side, append-only, `{key, withdrawn_at, reason, withdrawn_by}`) and a `withdrawn` lifecycle state. Make `formal_release_pin.py` fetch the withdrawal list from the **newest** tag even when pinned to an older one — the single channel permitted to travel forward, because it can only *remove* trust, never grant it. Serve `withdrawn: true` as the first entry in `caveats[]`.

---

**6 — `decls` is not a field of the registry schema, so the obligation/work-queue story has no mechanism.**
**Severity: high.**
Evidence: the registry entry schema lists `kind, title, informal, source, quote_mode, quote, quote_norm, quote_sha256, mint_resolution, depends_on, frontier, minted_at, minted_by, supersedes, superseded_by`. There is no `decls`. Yet the role-split table and the sorry-laundering section both rely on "a registry entry of `kind: obligation` with `decls: []` that appears in the work queue," and **no work queue is among the seven artifacts**. Cairn's best idea was adopted in prose and dropped from the schema. As written, an obligation is indistinguishable from a `kind: theorem` entry nobody got around to.
Fix: do **not** add `decls` (that would duplicate the binding `@[cites]` already owns and create a two-writer drift). Add artifact #8: `attest/workqueue.json`, generated by `mfc join` = every registry entry with zero inbound `@[cites]`, partitioned by `kind`, with `frontier` rolled up. That is the file an agent plans against and the one thing in the design with a real chance of getting an LLM to use it.

---

**7 — Axis 6 (`frontier_discharged`) is human assertion wearing a computed axis's clothes, violating the design's own independence rule.**
**Severity: high.**
Evidence: the design states the rule precisely — "two axes are distinct only if they have distinct evidence-producing programs" — and uses it to kill FTC's three-views-of-one-closure. But `frontier[].discharged_by` is hand-edited YAML; `mfc` only aggregates it. Nothing checks that the named discharger proves anything, and unlike axis 7 it carries no reviewer, no date, and no `self_attested` semantics distinct from the machine axes. Two of seven axes are human, and one of them is unattributed.
Fix: require `discharged_by` to name a declaration that (a) exists in the emission and (b) carries `@[discharges "<frontier-id>"]`, so the edge is anchored in `Environment.constants` rather than in prose; then axis 6 is genuinely computed over emission ∪ registry. Otherwise label its evidence `asserted` and fold it under axis 7's reviewer+date discipline.

---

**8 — `closed_lanes` mechanizes the opposite of the rule it claims to enforce.**
**Severity: high. This is the Bridgeland-specific structure hiding in plain sight.**
Evidence: the design mechanizes CLAUDE.md §4 ("the geometric lane is closed") as `forbidden_module_prefixes` / `forbidden_constants` checked against the emission, then claims this makes §3 ("never conflate the lattice model with geometry") a build failure. It does not. §4's hazard is *importing* geometry — a denylist catches that, though denylists over Mathlib are unbounded. §3's hazard is *claiming* geometry you do not have: `abbrev NumLattice : Type := Fin 2 → ℤ` imports nothing forbidden, and a doc-comment calling it `K_num(Ku(X))` passes every check in the design. The design's own honest-limit paragraph concedes this ("a digest cannot detect that `Fin 2 → ℤ` was described as a Kuznetsov component") and then leaves §3 with zero mechanical enforcement while presenting it as enforced.
Fix: (a) invert to an **import allowlist** (`permitted_module_prefixes`) checked against `.ilean` `directImports` — bounded, mechanical, and it catches new Mathlib modules the denylist author never heard of; (b) add `forbidden_vocabulary[]` per topic (`"Kuznetsov"`, `"Enriques"`, `"D^b(Coh"`, `"Chern"`) linted against **declaration names and doc-comments** of any declaration whose `frontier` is non-empty. That is §3, mechanized, and it generalizes: every low-coverage topic has a list of words its interfaces must not claim.

---

**9 — Motivic homotopy theory: at near-zero Mathlib coverage, 100% of truth-protection collapses onto the one axis that does not scale.**
**Severity: high.**
Walkthrough: Mathlib at any pin has no ∞-categories, no motivic spectra, no A¹-homotopy. So the topic repo consists entirely of self-declared interface structures. `closed_lanes` forbids nothing useful — there is nothing in Mathlib to forbid. Every entry is `relation_claimed ∈ {one_way, no_claim}` with a non-empty `frontier` of `kind_class: interface`, all of it hand-written and unchecked (gap 7). `statement_digest` is computed over your own definitions, so it detects drift in a private fiction. Axes 1–4 and 6 all pass, greenly, about a repo that has formalized nothing anyone else would recognize. **Bridgeland hides this** because it has an upstream anchor supplying real `Slicing` / `PreStabilityCondition` definitions, so `relation_claimed` has something external to relate to. Remove the anchor and the design's only remaining defense is human review, which is the resource already exhausted by gap 2.
Fix: make `frontier[].kind_class: interface` entries require a *named external referent* — the Mathlib or anchor constant the interface is claimed to model, or an explicit `no_referent: true` with a mandatory note. Then `mfc lint` can at least assert that an `interface` frontier item either points at something real or loudly says it points at nothing. Add `interface_ratio` (interfaces / total frontier items) to the served caveats.

---

**10 — Analytic number theory: no `external_decl` binding, so at high Mathlib coverage the design measures your wrapper instead of the theorem, and adds nothing over `docs/1000.yaml`.**
**Severity: high.**
Walkthrough: for ANT the natural target of a paper's Lemma 3.7 is frequently *already in Mathlib*. Emission is **module-scoped** to the topic's `lean_lib` (correctly — that is the fix for prefix-scope evasion), which means `@[cites]` can never be attached to `Mathlib.NumberTheory.…`. The adopter must restate. The restatement's `statement_digest`, `axiom_closure`, and `kernel_replay` then describe the wrapper, not the theorem, and the wrapper's faithfulness to the paper is a *different* question from Mathlib's. Meanwhile mathlib's own `1000.yaml` solves the high-coverage case in one line (`decl: <name>`), which the design studied and then dropped.
Fix: add `external_decls[]` to the registry entry (`{name, env_digest}`); `mfc-emit --include-external` runs `collectAxioms` on those named constants — legal and cheap, they are in the environment — and records them with `scope: external`. Without this, the architecture is useful only in the middle of the coverage range, which is exactly where Bridgeland sits.

---

**11 — `quote_sha256` survives only one of the two rotation classes, and the flagship test is rigged to pass.**
**Severity: high.**
Evidence: the audit's named rotation trigger is `ingest-recover-preambles`, which changes `preamble_text` and leaves `body_text` alone — `quote_sha256` survives that, correctly. But a **chunker bump changes chunk boundaries**, which changes `body_text`, which changes the whitespace-collapsed NFC hash exactly as it changes `chunk_id`. The design claims survival against "a chunker bump, an ar5iv re-render, a LaTeXML upgrade, an HTML→MinerU migration"; only the first class actually survives. And the test the design calls "what proves the identifier scheme works" mutates **whitespace** — the one perturbation `nfc-ws-collapse/1` absorbs by construction. Second problem: `quote` is described as human-confirmed against the paper, but `mint_resolution.matched_by: quote_sha256` requires byte-equality with the chunk body; any human correction of a LaTeXML artifact permanently breaks exact match and silently demotes the entry to `printed_number` (36/66 coverage even on the flagship paper) or `unresolvable`.
Fix: (a) state the guarantee honestly — survives preamble-class rotation, not re-chunking; (b) split `quote_as_minted` (byte-equal to the chunk, hashed, machine-owned) from `quote_as_read` (human-corrected, displayed, not hashed); (c) add ladder rung `matched_by: quote_containment` (chunk body contains the normalized quote) which is `status: current` — this is what actually survives a merge/split; (d) replace the whitespace test with two fixtures: one that merges two chunks and one that splits one.

---

**12 — Bootstrap is impossible as specified: the vacuous-pass guard fires on every new topic repo.**
**Severity: medium-high.**
Evidence: producer CI runs `mfc lint`, which "fails if `constants[] == []`." Walkthrough step 5 runs the emitter *before any entry is minted*, and a brand-new topic repo has zero declarations. Adopter #2's first green build is unreachable. Separately: `mfc-emit` exits non-zero on `sorryAx` — unspecified whether it still *writes* the emission. If not, a mid-development repo produces no record at all, so there is no honest artifact saying "this repo currently has 3 sorries," and the work-queue use case dies at exactly the moment it is most useful.
Fix: `bootstrap: true` in `formalization.yaml` permits an empty emission and forces every axis to `not_run`; `mfc lint` clears the flag automatically once `constants[] != []` and refuses to let it be re-set. Emitter always writes the file; the sorry signal is exit code + `contains_sorry_ax` count, never file absence.

---

**13 — A Mathlib or anchor bump invalidates 100% of human review simultaneously, and the mitigation is deferred to v1.1.**
**Severity: medium-high. This is failure mode "Mathlib bumps" at 6 months.**
Evidence: `env_digest` includes every package `rev`; `statement_digest` folds external constants by name under that digest; `statement_stable` is `not_applicable` (never `pass`) across environments. So one bump renders every `faithfulness` record inapplicable at once, and the recovery cost equals the entire original review budget (gap 2) — per bump. `--restate-check` is the stated fix and is explicitly v1.1, deferred because `elabTerm`/`isDefEq` availability at v4.29.0 is unverified. That verification is roughly thirty minutes of work against the environment that is already on this machine.
Fix: verify `elabTerm`/`isDefEq` at the pin now and promote `--restate-check` to v1.0. Cheaper interim: record `reviewed_statement_pp` in `review.yaml` and have `mfc` emit `review-migration.json` listing entries whose `type_pp` is byte-identical across the bump; those carry forward with a dated `carried_forward_from` record. A pp-identical statement under a new toolchain is not proof of sameness, but it is a defensible, dated, machine-recorded distinction from "re-read the paper."

---

**14 — Renaming a declaration silently orphans its review.**
**Severity: medium.**
Evidence: `review.yaml` records `decl: <name>`; `mfc` joins reviews to declarations by name. A rename leaves `reviewed_statement_digest` matching (a rename does not change the type) while `decl` dangles. Nothing in the lint list checks that `review.decl` exists in the emission. Result: `faithfulness` silently reverts to `not_run` — or, if the join is lenient, a review floats free.
Fix: key reviews on `(registry key, reviewed_statement_digest)` and demote `decl` to a hint; `mfc lint` errors when a review's digest matches no constant *and* its `decl` is absent — that is a genuine rename-plus-restatement, which must be adjudicated by a human.

---

**15 — `lean-action` detail the design got wrong (and one it hedged unnecessarily).**
**Severity: medium.**
I fetched `action.yml`. Confirmed: inputs `leanchecker`, `lean4checker`, `nanoda`, `nanoda-allow-sorry` all exist, `nanoda-allow-sorry` defaults to `"true"` (so the design's warning is right and load-bearing), and there is **no aggregate status output** (so the §4.9-compliance claim holds). But the outputs are exactly `build-status, test-status, lint-status, mk_all-status, detected-mathlib, nanoda-status` — **there is no `leanchecker-status`**. The design says "consume the per-axis outputs" for both checkers; only nanoda's is readable. The design also ships axis 2 as possibly `not_run` on the grounds that it could not verify these inputs — that hedge is now discharged and should be removed rather than left as a standing excuse.
Fix: axis 2 evidence is `{checker: "nanoda", version, allow_sorry: false}` from `nanoda-status`; run `leanchecker` as an explicit step and capture its exit code directly if you want it as a second checker.

---

**16 — `mfc` runs on both sides, which removes the independent implementation the Bowtie model exists to provide.**
**Severity: medium.**
The design presents "all digesting is done by `mfc` in Python, on both sides" as eliminating the cross-language-digest problem. It also eliminates the check: a canonicalization bug is symmetric and invisible to conformance, because both implementations *are* the implementation. JSON-Schema-Test-Suite works because ~20 independent implementations run the corpus.
Fix: keep the single implementation (correct for a solo operator) but require every fixture in `testdata/valid/` to carry **hand-computed expected digests** checked into the corpus, so canonicalization is pinned by data rather than by code agreement.

---

**17 — Predicted rot, with the audit's own precedents.**
**Severity: medium.**
Will decay, because nothing reads them: `informal` (hand-written prose, compared to nothing — the same shape as `formalization.yaml`'s false "mirrors the anchor key-for-key" claim); `notebook_hint` (explicitly "advisory only" — the precedent is `display_name=""`, `description=""` after 13 ingest runs); `mint_resolution.observed_at` (TOFU window never revisited); `frontier[].kind_label` (free string, no vocabulary); `contract.lock` via `copier update` PRs that never auto-merge, against one operator and N=1 consumers. Self-enforcing, and correctly so: generated `caveats[]`, `additionalProperties: false` (which really does turn the trust-language policy into a machine constraint — the design's best single idea), `registry_sha256`, and `git diff --exit-code` *once gap 4 is fixed*.
Fix: delete from v1 every field no test reads. Specifically, either `informal` gets a lint rule (non-empty, ≥N chars, differs from `title`, and — the real one — is re-confirmed whenever `statement_digest` changes) or it does not ship.

---

**18 — Step 12, the second-topic gate, is estimated at "2 evenings" and is off by an order of magnitude; it is therefore the step that will be dropped.**
**Severity: medium-high as a process risk.**
It requires standing up a new arXMCP notebook (fetch + ingest a real corpus), minting entries, *and* "≥1 real binding reaching `relation_claimed: exact`" — i.e. actually formalizing a theorem in a field the operator does not work in. That is weeks, not evenings. The design correctly makes it the falsifiability gate and says "publish the template only after this passes," which means the realistic outcome is that the template never ships or the gate is quietly relaxed — the same dynamic that left `queries.json` a template after 13 runs.
Fix: shrink the gate to something honestly two-evening-sized — one paper, five entries, one binding to a theorem **already in Mathlib** (which also forces gap 10's `external_decls` to exist) — and budget it at 2 weeks anyway. Ship the template with `generalization_validated: false` in its own trust record until the gate passes, so the claim is dated and visible rather than deferred.

---

## The single biggest risk

Every mechanical part of this design is downstream of a human bottleneck that nobody sized, and at the throughput actually available the contract will serve roughly ten records against a 15,280-chunk corpus — a ~0.07% hit rate. An agent that queries `arxmcp://formal/{notebook}` three times, gets nothing, and stops querying is behaving rationally, and at that point the apparatus is a well-tested, schema-validated, adversarially-fixtured pipeline with no consumer — which is precisely the failure the audit already documented one level down ("the artifact both repos call 'the entire interface' has **no consumer**, and no reader on either side"). The design fixes the reader problem with real rigor and then reproduces the *content* problem in a more expensive form, because it deliberately closed the only volume path (rejecting `faithfulness: agent_drafted`) without opening a substitute lane that occupies zero axes. Compounding it: the one axis with genuinely independent evidence is unsound against arXiv versions the corpus cannot even represent (gap 1), and the one rule the whole Lean repo exists to protect — do not describe `Fin 2 → ℤ` as a Kuznetsov component — remains enforced only by the human axis that the bottleneck exhausts (gap 8). So the plan's most likely six-month state is not a broken contract but an immaculate, green, empty one: CI passing, digests matching, `caveats[]` correctly generated, ten entries, and nothing reading it.