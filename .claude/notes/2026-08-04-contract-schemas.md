# THE CONTRACT — literal artifacts

Ground truth: the audit, plus locally re-verified facts. Repo HEAD moved again during this session: **`f166a3d`** ("feat(analysis): uniform continuity + interval reindexing for 3c"), clean tree, still `leanprover/lean4:v4.29.0`. All digests below marked **[COMPUTED]** were actually computed on this machine and are reproducible from the shown inputs.

**Three corrections to the architecture brief, applied throughout.** (a) The brief's `resolution.json` used a property named `status`, which its own `mfc lint-schemas` rule forbids — renamed to `resolution`. (b) The brief's `build.json` used `independent_checkers[].result`, also forbidden — the four-valued token is spelled **`value`** in every schema, without exception. (c) `type_pp` from the real toolchain **contains hard line breaks at the pretty-printer's wrap width** (measured below), so every digest normalizes whitespace before hashing; a raw `type_pp` hash would rotate on a `format.width` change.

**A fourth correction, 2026-08-04 (later): `relation_claimed` has FIVE values, not six. `reformulation` is struck.** Applied throughout — the emission schema, the review schema, the Lean sketch in §2.2, and the `mfc lint` frontier rule that named it.

This document listed `exact | equivalent | specialization | one_way | reformulation | no_claim` and **never said what `reformulation` meant** — the note defines no per-value semantics anywhere, and the only property it ever attached to the value was that an empty frontier is rejected for it, which is equally true of `specialization` and `one_way`. The shipped attribute (`MathFormalContract/Cites.lean`, and the table in that repo's README) defines five values precisely and omits it.

Struck rather than defined, for three reasons.

1. **An undefined value in a trust vocabulary is the failure this contract exists to prevent.** `relation` is mandatory precisely because "a missing relation that defaulted to anything would be a trust axis inferred from silence." A value whose meaning nobody can state is worse than a missing one: it is silence wearing a label, and it is *recorded* rather than absent.
2. **Its only plausible reading overlaps `equivalent`, with no stated boundary.** Two values a reviewer cannot tell apart make the recorded value carry no information, which is what an enum is for.
3. **The asymmetry runs one way.** Adding an enum value later is a MINOR bump. Removing one after registry entries already claim it is breaking, and those entries cannot be re-derived — the claim was a human's. Ship the five that are defined; `reformulation` can be added by whoever can define it and draw its boundary against `equivalent`.

`review/1.0`'s `relation_confirmed` keeps **`disputed`**, which is review-only and does have a meaning: a named human read the claim and rejected it. That is not the same kind of value and is not struck.

---

# PART 0 — Canonical primitives

Every digest in this contract is one of exactly four functions. They are defined once, implemented once (in Python, in `mfc`), and **never implemented in Lean** — Lean core at v4.29.0 ships no SHA-256, and a second implementation is a second thing to drift.

`math-formal-contract/mfc/digest.py`:

```python
"""The four canonical digest functions. This file is frozen: any change is a
MAJOR schema bump on every artifact that carries a digest."""
from __future__ import annotations
import hashlib, json, unicodedata
from typing import Any

TEXT_NORM_ID = "nfc-ws-collapse/1"

def norm_text(s: str) -> str:
    """NFC-normalize, then collapse every run of Unicode whitespace to a single
    U+0020 and strip. Order is load-bearing: NFC FIRST, then split/join."""
    return " ".join(unicodedata.normalize("NFC", s).split())

def canonical_json(obj: Any) -> str:
    """The repo-wide canonicalization. Byte-identical to
    server/corpus_manifest.py::compute_manifest_hash and to
    tests/test_server_tool_schema.py::_serialize_tools in arXMCP."""
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True)

def sha256_hex(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()

# ---- D1: quote_sha256 -------------------------------------------------------
def quote_sha256(quote: str) -> str:
    """Digest of a statement's verbatim text as printed in the source.
    Deliberately whitespace-insensitive: a re-render (ar5iv -> MinerU, LaTeXML
    upgrade) that changes only wrapping MUST NOT rotate this."""
    return sha256_hex(norm_text(quote).encode("utf-8"))

# ---- D2: env_digest ---------------------------------------------------------
def env_digest(lean_toolchain: str, lean_githash: str,
               lean_options: dict[str, bool | int | str],
               packages: list[tuple[str, str]]) -> str:
    """Fingerprint of the Lean environment.

    `packages` is [(name, rev)] from lake-manifest.json, SORTED. We hash `rev`
    and NEVER `inputRev`: nine of the fourteen packages in bridgeland-stab-lean
    carry inputRev "main"/"master", which `lake update` would re-resolve.
    `lean_options` MUST be the RESOLVED [leanOptions] table, because
    autoImplicit is elaboration-affecting."""
    return sha256_hex(canonical_json({
        "lean_toolchain": lean_toolchain,
        "lean_githash": lean_githash,
        "lean_options": lean_options,
        "packages": [list(p) for p in sorted(packages)],
    }).encode("utf-8"))

# ---- D3: statement_digest (Merkle over topic-local constants) ---------------
STATEMENT_DIGEST_V = "statement-digest/1"

def statement_digest(name: str, kind: str, type_pp: str,
                     value_pp: str | None, dep_digests: dict[str, str]) -> str:
    """Merkle node. `dep_digests` maps each TOPIC-LOCAL constant occurring in
    this constant's type (and, for def/abbrev/opaque, in its value) to that
    constant's statement_digest. External constants (Mathlib, the anchor)
    contribute NOTHING here -- env_digest already pins them by commit.

    value_pp is non-null ONLY for kind in {def, opaque}. This is the whole
    repair for the 'edit an abbrev's body, every dependent theorem's digest is
    unchanged' hole. Measured proof in PART 4, case ADV-4.

    Cycles: constants in one mutual/inductive SCC substitute
    {"__scc__": "<name>"} for an in-SCC dependency instead of a digest, and
    the emitter records `scc_members[]` on every member."""
    return sha256_hex(canonical_json({
        "v": STATEMENT_DIGEST_V,
        "kind": kind,
        "pp": norm_text(type_pp),
        "value_pp": norm_text(value_pp) if value_pp is not None else None,
        "deps": dict(sorted(dep_digests.items())),
    }).encode("utf-8"))

# ---- D4: file_digest --------------------------------------------------------
def file_digest(path) -> str:
    """Raw sha256 of file BYTES. Not canonicalized -- bundle.json commits to
    the exact bytes on disk, and `git diff --exit-code attest/` is what keeps
    them honest."""
    with open(path, "rb") as fh:
        return sha256_hex(fh.read())
```

**Measured values for `bridgeland-stab-lean` @ `f166a3d` [COMPUTED]:**

```
env_digest = 52b407ea4c1e8c51bfefe1d9a1f173e142729c6abf09a750a383869d5b160349
```
from canonical JSON (975 bytes) of:
```json
{"lean_githash":"98dc76e3c0a9b856c9b98726b713fb04fab16740",
 "lean_options":{"autoImplicit":false,"relaxedAutoImplicit":false},
 "lean_toolchain":"leanprover/lean4:v4.29.0",
 "packages":[["BridgelandStability","9e48f23a382ba117b63076a33e0e775389fef1ba"],
             ["Cli","7802da01beb530bf051ab657443f9cd9bc3e1a29"],
             ["MD4Lean","6a3fb240133bcb7e1a066fdc784b3fdc304e3fc5"],
             ["Qq","707efb56d0696634e9e965523a1bbe9ac6ce141d"],
             ["aesop","7152850e7b216a0d409701617721b6e469d34bf6"],
             ["batteries","756e3321fd3b02a85ffda19fef789916223e578c"],
             ["importGraph","48d5698bc464786347c1b0d859b18f938420f060"],
             ["informal","be2042471694a77eea68089c770de3c9a9245d7c"],
             ["LeanSearchClient","c5d5b8fe6e5158def25cd28eb94e4141ad97c843"],
             ["mathlib","8a178386ffc0f5fef0b77738bb5449d50efeea95"],
             ["plausible","83e90935a17ca19ebe4b7893c7f7066e266f50d3"],
             ["proofwidgets","3c52dee17f0cd89c1ec14de78920d1bdaa3d26b3"],
             ["subverso","ce893b9042128037e2d3c0158b9567fab9fae268"],
             ["verso","7ae82ac2ae54ae5dcc9948a701669e9b596e5cae"]]}
```

---

# PART 1 — The seven schemas

Layout in `math-formal-contract`:

```
math-formal-contract/
  contract.version                       # "1.0" — the contract's own MAJOR.MINOR
  schema/
    registry-1.0.schema.json
    emission-1.0.schema.json
    environment-1.0.schema.json
    declarations-1.0.schema.json
    review-1.0.schema.json
    build-1.0.schema.json
    bundle-1.0.schema.json
    resolution-1.0.schema.json
    served-record-1.0.schema.json        # the shape arXMCP's resource emits
  testdata/valid/…  testdata/invalid/…  testdata/lean/…
  mfc/                                   # the Python CLI
  lean/                                  # the zero-dependency Lake package
  template/                              # copier
  migrations/
```

## 1.0 Schema-version discipline (normative, applies to all seven)

Every artifact's first key is `schema_version: "<name>/<major>.<minor>"`.

| Change | Bump | Consumer behaviour |
|---|---|---|
| add an **optional** property; add an **enum member** | MINOR | accept if `major == mine` and `minor <= mine`. If `minor > mine`: **hard-refuse**, emit `contract_version_unsupported`, do not best-effort parse. |
| remove a property; retype a property; **narrow** an enum member's meaning; change any digest function | MAJOR | **hard-refuse** unconditionally. |

The consumer algorithm is one function, shared:

```python
# mfc/version.py
class ContractVersionUnsupported(Exception): ...

def accept(seen: str, supported: dict[str, tuple[int, int]]) -> None:
    """`seen` is e.g. "registry/1.3"; `supported` is {"registry": (1, 0)}.
    There is NO tolerant mode. A consumer that cannot parse an artifact
    exactly refuses it; it never renders a partial trust record, because a
    partial trust record is indistinguishable from a complete one downstream."""
    name, _, ver = seen.partition("/")
    try:
        maj, minr = (int(x) for x in ver.split("."))
    except ValueError:
        raise ContractVersionUnsupported(f"malformed schema_version {seen!r}")
    if name not in supported:
        raise ContractVersionUnsupported(f"unknown artifact kind {name!r}")
    smaj, sminr = supported[name]
    if maj != smaj:
        raise ContractVersionUnsupported(
            f"{name}: major {maj} != supported {smaj}; a MAJOR bump requires a "
            f"`copier update` and a migrations/{smaj}.x-to-{maj}.0.py run")
    if minr > sminr:
        raise ContractVersionUnsupported(
            f"{name}: minor {minr} > supported {sminr}; refusing rather than "
            f"parsing an artifact that may carry fields this reader ignores")
```

**On the arXMCP side specifically**, a refusal is served, not swallowed: `arxmcp://formal/{notebook}` returns `{"caveats": ["contract_version_unsupported: registry/2.0 ..."], "axes": {}, "records": []}`. It never omits the release silently, and it never downgrades to "no data".

**Forbidden property names** — enforced by `mfc lint-schemas` walking every `properties` key of every schema in `schema/`, with the rejection fixture `testdata/invalid/aggregate-status/`:

```python
FORBIDDEN_PROPERTY_NAMES = frozenset({
    "status", "verified", "ok", "passed", "pass", "trusted", "result",
    "verdict", "score", "confidence", "valid", "success", "clean",
})
```
`additionalProperties: false` on every object in every schema is what makes this a *structural* guarantee rather than a review habit — a producer literally cannot add `"status": "verified"` to an artifact and have it validate.

---

## 1.1 `registry/<work-slug>.yaml` — schema `registry/1.0`

**Home:** `bridgeland-stab-lean/registry/`. Hand-minted, git-tracked, human-authored, machine-validated. **This is the formalization plan.**

### 1.1a Filled instance — `registry/bridgeland2007.yaml`

```yaml
# ============================================================================
# Statement registry for Bridgeland, "Stability conditions on triangulated
# categories", section 8.  This file is the ONLY place a durable statement
# identifier is minted.  Nothing arXMCP computes appears in any key here:
# not chunk_id, not corpus_version, not parse_artifact_sha256, not the
# notebook slug.  A re-ingest that rotates every chunk_id in the corpus
# cannot invalidate one byte of this file.
# ============================================================================
schema_version: "registry/1.0"

# 12 lowercase hex, minted ONCE by `mfc registry init`, never derived from
# content, never reused.  Notebook slugs are NOT used: they are rows in an
# unauthenticated machine-local sqlite DB with no global registry, so two
# adopters both minting `number-theory` would collide.
registry_id: "9f4c1a20b7d3"

# Advisory routing hint for the resolver.  NEVER part of any key.  Changing it
# changes no identifier and invalidates no review.
notebook_hint: "bridgeland-stability"

entries:

  # --------------------------------------------------------------------------
  "stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2":
    kind: lemma          # theorem|lemma|proposition|corollary|definition|
                         # construction|equation|remark|conjecture|obligation
    title: "Lemma 8.2"

    # Human-written, one to three sentences, in English.  This is what an agent
    # reads first.  It is NOT the quote and is NOT hashed.
    informal: >
      For (T, f) in the group G~L+(2,R) of compatible pairs and a stability
      condition (Z, P), the pair (T^-1 . Z, P . f) is again a stability
      condition; this defines a right action of G~L+(2,R) on the space of
      stability conditions.

    # Paper coordinates are TYPED FIELDS, never key segments.  This is what
    # makes `textbook:<slug>` sources (which arXMCP ships today) and DOIs
    # expressible, and what removes the colon-tokenization failure that
    # `arxiv:math/0212237v2:lem-8.2` would have.
    source:
      scheme: arxiv                 # arxiv | doi | textbook | url
      id: "math/0212237"
      version: "v?"                 # REQUIRED when scheme==arxiv, pattern ^v[0-9]+$
                                    # DELIBERATELY UNFILLED — see OPEN ITEM 1.
                                    # `mfc lint` REJECTS the literal "v?".
      printed_number: "8.2"         # nullable. HINT ONLY, never load-bearing:
                                    # populated only on the ar5iv/LaTeXML path,
                                    # 36 of 66 chunks on this very paper.
      locator: "section 8"
      title: "Stability conditions on triangulated categories"
      authors: ["Tom Bridgeland"]

    quote_mode: verbatim            # verbatim | digest_only
    quote: |
      <<<PLACEHOLDER — NOT MINTED>>>
      Prefilled by:
        mfc registry mint --from-chunk arxiv:math/0212237:a82c3230040fd724
      then CONFIRMED BY A HUMAN against the arXiv PDF at the pinned version.
      Left unfilled here because the arXMCP server was not running when this
      specification was authored; fabricating a verbatim quote from a paper
      would be exactly the failure this whole contract exists to prevent.
    quote_norm: "nfc-ws-collapse/1"
    quote_sha256: "ebacfe5caa6c1df8229ec6bfbcf55f855a524a77cf78a9fb3171b81172d6f50d"
      # [COMPUTED] this is quote_sha256("PLACEHOLDER-QUOTE-NOT-YET-MINTED"),
      # i.e. a real hash of a real placeholder, not a fabricated hash of text
      # nobody has read.  `mfc lint --strict` REJECTS an entry whose quote
      # contains "<<<PLACEHOLDER".

    # REQUIRED and non-empty.  An entry cannot come into existence until its
    # quote has matched a live chunk at least once.  This is the trust-on-
    # first-use anchor: arXMCP has no authentication and a 17-route
    # unauthenticated mutation plane, so the frozen quote_sha256 is what
    # bounds later tampering, and mint-time resolution is what bounds the
    # window before the freeze.
    mint_resolution:
      notebook: "bridgeland-stability"
      chunk_id: "arxiv:math/0212237:a82c3230040fd724"   # audit-verified by
                                                        # independent recompute
      matched_by: quote_sha256                          # quote_sha256|printed_number
      corpus_manifest_content_hash: "<64 hex from arxmcp://corpus-manifest>"
      corpus_version: 5048
      observed_at: "2026-08-04T00:00:00Z"

    depends_on:
      - "stmt:9f4c1a20b7d3:bridgeland2007.defn-8.1"

    # REQUIRED, MAY be empty, MUST be present.  `mfc lint` rejects an empty
    # frontier when any binding to this entry claims
    # relation_claimed in {specialization, one_way}.
    frontier:
      - id: gltilde-universal-cover
        kind_class: open-problem     # closed-lane|missing-library|open-problem|interface
        kind_label: "covering-space"
        statement: >
          The projection GLTilde -> GL+(2,R) is surjective with fibre Z, and
          GLTilde is simply connected.  bridgeland-stab-lean proves GLTilde is
          a GROUP and nothing more; the NAME asserts the universal cover, the
          proved content does not.
        discharged_by: null
      - id: stability-vs-prestability
        kind_class: missing-library
        kind_label: "local-finiteness"
        statement: >
          The action is proved on PreStabilityCondition.WithClassMap only.
          StabilityCondition additionally carries local finiteness; step 3c is
          blocked on an anchor-side restriction lemma for
          IsStrictArtinianObject / IsStrictNoetherianObject.
        discharged_by: null

    minted_at: "2026-08-04"
    minted_by: "Chris Dare"
    supersedes: null
    superseded_by: null
    note: >
      A version bump on the source paper mints a NEW key with `supersedes`
      pointing here.  This key stays valid forever and keeps this quote.

  # --------------------------------------------------------------------------
  # An `obligation` entry: the repo's "leave it UNDECLARED with a TODO" rule,
  # made navigable.  decls: [] is not an omission — it is the whole point.
  # This entry appears in `mfc work-queue` output.  It is what a `sorry` would
  # have been, without a sorry-backed constant entering any .olean.
  "stmt:9f4c1a20b7d3:bridgeland2007.obl-stab-action":
    kind: obligation
    title: "Action on StabilityCondition (step 3c)"
    informal: >
      The G~L+(2,R) action extends from PreStabilityCondition.WithClassMap to
      StabilityCondition.WithClassMap, i.e. local finiteness is preserved.
    source:
      scheme: arxiv
      id: "math/0212237"
      version: "v?"
      printed_number: null
      locator: "section 8"
    quote_mode: digest_only
    quote: null
    quote_norm: "nfc-ws-collapse/1"
    quote_sha256: null              # permitted ONLY when quote_mode==digest_only
                                    # AND quote_digest_source is present
    quote_digest_source: null       # null => this obligation is not anchored to
                                    # a specific printed statement; it is the
                                    # author's decomposition.  `mfc lint` then
                                    # REQUIRES a non-empty `note`.
    mint_resolution: null           # permitted ONLY for kind==obligation
    depends_on: ["stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2"]
    frontier:
      - id: stability-vs-prestability
        kind_class: missing-library
        kind_label: "local-finiteness"
        statement: >
          IsStrictArtinianObject / IsStrictNoetherianObject restrict along the
          full-subcategory inclusion of a sub-interval.  The anchor's
          IsLocallyFinite docstring asserts shrinking a witness is harmless but
          never proves it; its only consumers merely destructure the witness.
        discharged_by: null
    minted_at: "2026-08-04"
    minted_by: "Chris Dare"
    supersedes: null
    superseded_by: null
    note: >
      Deliberately undeclared in Lean.  A sorry-backed instance would typecheck,
      get imported, and launder an unproved claim downstream.  This entry is the
      visible replacement.
```

### 1.1b `schema/registry-1.0.schema.json`

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://github.com/chris-dare-dev/math-formal-contract/schema/registry-1.0.schema.json",
  "title": "Statement registry (registry/1.0)",
  "type": "object",
  "additionalProperties": false,
  "required": ["schema_version", "registry_id", "entries"],
  "properties": {
    "schema_version": { "const": "registry/1.0" },
    "registry_id":    { "type": "string", "pattern": "^[0-9a-f]{12}$" },
    "notebook_hint":  { "type": ["string", "null"], "pattern": "^[a-z][a-z0-9-]{2,30}$" },
    "entries": {
      "type": "object",
      "minProperties": 1,
      "propertyNames": { "$ref": "#/$defs/citationKey" },
      "additionalProperties": { "$ref": "#/$defs/entry" }
    }
  },
  "$defs": {
    "citationKey": {
      "type": "string",
      "pattern": "^stmt:[0-9a-f]{12}:[a-z][a-z0-9._-]{0,63}$",
      "$comment": "3 segments, fixed arity, no corpus-derived bytes. The paper coordinate is NOT here."
    },
    "sha256":  { "type": "string", "pattern": "^[0-9a-f]{64}$" },
    "isoDate": { "type": "string", "pattern": "^[0-9]{4}-[0-9]{2}-[0-9]{2}$" },
    "isoTs":   { "type": "string", "pattern": "^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9:.]+Z$" },

    "source": {
      "type": "object",
      "additionalProperties": false,
      "required": ["scheme", "id", "version", "printed_number", "locator"],
      "properties": {
        "scheme":  { "enum": ["arxiv", "doi", "textbook", "url"] },
        "id":      { "type": "string", "minLength": 1, "maxLength": 512 },
        "version": { "type": ["string", "null"], "pattern": "^v[0-9]+$" },
        "printed_number": { "type": ["string", "null"], "maxLength": 64 },
        "locator": { "type": ["string", "null"], "maxLength": 256 },
        "title":   { "type": ["string", "null"], "maxLength": 512 },
        "authors": { "type": "array", "items": { "type": "string" } }
      },
      "allOf": [
        { "$comment": "arXiv ids are immutable only WITH a version; the bare form resolves to LATEST and silently drifts.",
          "if":   { "properties": { "scheme": { "const": "arxiv" } }, "required": ["scheme"] },
          "then": { "properties": { "version": { "type": "string", "pattern": "^v[0-9]+$" } },
                    "required": ["version"] } },
        { "$comment": "textbook:<slug> sources carry no version axis; a version here is a category error.",
          "if":   { "properties": { "scheme": { "const": "textbook" } }, "required": ["scheme"] },
          "then": { "properties": { "version": { "type": "null" } } } }
      ]
    },

    "frontierItem": {
      "type": "object",
      "additionalProperties": false,
      "required": ["id", "kind_class", "statement", "discharged_by"],
      "properties": {
        "id":         { "type": "string", "pattern": "^[a-z][a-z0-9-]{0,63}$" },
        "kind_class": { "enum": ["closed-lane", "missing-library", "open-problem", "interface"] },
        "kind_label": { "type": ["string", "null"], "maxLength": 64,
                        "$comment": "free per-topic label; the copier answer `frontier_kind_labels[]` is the allowlist mfc lint checks against" },
        "statement":  { "type": "string", "minLength": 1 },
        "discharged_by": {
          "oneOf": [
            { "type": "null" },
            { "type": "object", "additionalProperties": false,
              "required": ["key", "discharged_at", "discharged_by_reviewer"],
              "properties": {
                "key":  { "$ref": "#/$defs/citationKey" },
                "discharged_at": { "$ref": "#/$defs/isoDate" },
                "discharged_by_reviewer": { "type": "string", "minLength": 1 },
                "note": { "type": ["string", "null"] }
              } }
          ]
        }
      }
    },

    "mintResolution": {
      "type": "object",
      "additionalProperties": false,
      "required": ["notebook", "chunk_id", "matched_by",
                   "corpus_manifest_content_hash", "observed_at"],
      "properties": {
        "notebook":   { "type": "string", "pattern": "^[a-z][a-z0-9-]{2,30}$" },
        "chunk_id":   { "type": "string", "minLength": 1,
                        "$comment": "CACHE HINT ONLY. Rotates on any parse change; there is no alias table and merge_insert has no delete arm, so a stale id stays addressable. Never authoritative." },
        "matched_by": { "enum": ["quote_sha256", "printed_number"],
                        "$comment": "`fuzzy` is deliberately absent: an entry may not be MINTED on a fuzzy match." },
        "corpus_manifest_content_hash": { "$ref": "#/$defs/sha256" },
        "corpus_version": { "type": ["integer", "null"],
                            "$comment": "LanceDB MVCC integer. Recorded, never trusted: a restore-from-backup presents a LOWER version over different bytes." },
        "observed_at": { "$ref": "#/$defs/isoTs" }
      }
    },

    "entry": {
      "type": "object",
      "additionalProperties": false,
      "required": ["kind", "title", "informal", "source", "quote_mode",
                   "quote", "quote_norm", "quote_sha256", "mint_resolution",
                   "depends_on", "frontier", "minted_at", "minted_by",
                   "supersedes", "superseded_by"],
      "properties": {
        "kind": { "enum": ["theorem", "lemma", "proposition", "corollary",
                           "definition", "construction", "equation", "remark",
                           "conjecture", "obligation"] },
        "title":    { "type": "string", "minLength": 1, "maxLength": 256 },
        "informal": { "type": "string", "minLength": 1 },
        "source":   { "$ref": "#/$defs/source" },
        "quote_mode": { "enum": ["verbatim", "digest_only"] },
        "quote":      { "type": ["string", "null"] },
        "quote_norm": { "const": "nfc-ws-collapse/1" },
        "quote_sha256": { "oneOf": [{ "$ref": "#/$defs/sha256" }, { "type": "null" }] },
        "quote_digest_source": {
          "$comment": "digest_only mode: WHERE the hash came from, since the text is not inlined.",
          "oneOf": [{ "type": "null" },
                    { "type": "object", "additionalProperties": false,
                      "required": ["notebook", "chunk_id", "computed_at"],
                      "properties": { "notebook": { "type": "string" },
                                      "chunk_id": { "type": "string" },
                                      "computed_at": { "$ref": "#/$defs/isoTs" } } }]
        },
        "mint_resolution": { "oneOf": [{ "$ref": "#/$defs/mintResolution" }, { "type": "null" }] },
        "depends_on": { "type": "array", "items": { "$ref": "#/$defs/citationKey" }, "uniqueItems": true },
        "frontier":   { "type": "array", "items": { "$ref": "#/$defs/frontierItem" } },
        "minted_at":  { "$ref": "#/$defs/isoDate" },
        "minted_by":  { "type": "string", "minLength": 1 },
        "supersedes":     { "oneOf": [{ "$ref": "#/$defs/citationKey" }, { "type": "null" }] },
        "superseded_by":  { "oneOf": [{ "$ref": "#/$defs/citationKey" }, { "type": "null" }] },
        "note": { "type": ["string", "null"] }
      },
      "allOf": [
        { "$comment": "verbatim mode MUST inline the text and MUST hash it.",
          "if":   { "properties": { "quote_mode": { "const": "verbatim" } }, "required": ["quote_mode"] },
          "then": { "properties": { "quote": { "type": "string", "minLength": 1 },
                                    "quote_sha256": { "$ref": "#/$defs/sha256" } },
                    "required": ["quote", "quote_sha256"] } },
        { "$comment": "Only an obligation may lack a mint_resolution. Every other kind must have matched a live chunk at least once.",
          "if":   { "not": { "properties": { "kind": { "const": "obligation" } } } },
          "then": { "properties": { "mint_resolution": { "$ref": "#/$defs/mintResolution" } },
                    "required": ["mint_resolution"] } }
      ]
    }
  }
}
```

### 1.1c `mfc lint` rules over the registry that JSON Schema cannot express

| Rule id | Check | Fixture |
|---|---|---|
| `R-01` | `source.version` is not the literal `"v?"` or `""` | `invalid/source-arxiv-unversioned` |
| `R-02` | `quote_sha256 == quote_sha256(entry.quote)` recomputed from the inline text | `invalid/quote-hash-mismatch` |
| `R-03` | `quote` does not contain `<<<PLACEHOLDER` | `invalid/placeholder-quote` |
| `R-04` | every `depends_on` / `supersedes` / `superseded_by` / `frontier[].discharged_by.key` resolves inside the registry set, and the `depends_on` graph is acyclic | `invalid/unknown-key`, `invalid/cyclic-depends` |
| `R-05` | `registry_id` in the key equals the file's `registry_id` | `invalid/registry-id-mismatch` |
| `R-06` | no key matches `^arxiv:` or `^[a-z]+:[^:]+:[0-9a-f]{16}$` (a `chunk_id`/`equation_id` shape) | `invalid/key-is-chunk-id-shaped` |
| `R-07` | `superseded_by` is symmetric with the target's `supersedes` | `invalid/asymmetric-supersede` |
| `R-08` | `frontier[].kind_label ∈ copier answer frontier_kind_labels[]` | `invalid/unknown-frontier-label` |
| `R-09` | `kind: obligation` with `quote_sha256: null` requires non-empty `note` | `invalid/obligation-without-note` |

---

## 1.2 `attest/lean-emission.json` — schema `emission/1.0`

**Home:** `bridgeland-stab-lean/attest/lean-emission.json`. **Generated. NOT committed** (`.gitignore`: `attest/lean-emission.json`). Written by Lean; contains **no digests**, because Lean core at v4.29.0 ships no SHA-256 and a consumer must be able to recompute everything it is served.

### 1.2a Filled instance (abridged; real measured `type_pp` values)

```json
{
  "schema_version": "emission/1.0",
  "emitter_version": "mfc-emit/1.0.0",
  "lean_version": "4.29.0",
  "lean_githash": "98dc76e3c0a9b856c9b98726b713fb04fab16740",
  "lean_options": { "autoImplicit": false, "relaxedAutoImplicit": false },
  "pp_options": { "pp.fullNames": true, "pp.universes": true,
                  "pp.explicit": false, "pp.notation": true,
                  "format.width": 120 },
  "root_lib": "BridgelandStabLean",
  "modules": [
    "BridgelandStabLean",
    "BridgelandStabLean.Lattice.Basic",
    "BridgelandStabLean.Lattice.NumericalK",
    "BridgelandStabLean.GroupAction.NormalizedShift",
    "BridgelandStabLean.GroupAction.GLTilde",
    "BridgelandStabLean.GroupAction.ComplexBridge",
    "BridgelandStabLean.GroupAction.ShiftAnalysis",
    "BridgelandStabLean.GroupAction.SlicingAction",
    "BridgelandStabLean.GroupAction.PreStabilityAction"
  ],
  "counts": { "total": 121, "in_scope": 78, "internal": 43,
              "with_range": 68, "instances": 6, "private": 0 },
  "constants": [
    {
      "name": "BridgelandStabLean.Lattice.NumLattice",
      "module": "BridgelandStabLean.Lattice.NumericalK",
      "kind": "def",
      "is_instance": false, "is_internal": false, "is_private": false,
      "is_reducible": true,
      "num_levels": 0,
      "type_pp": "Type",
      "value_pp": "Fin 2 \u2192 \u2124",
      "local_deps": [],
      "scc_members": [],
      "axioms": [],
      "range": { "startLine": 27, "startCol": 0, "endLine": 27, "endCol": 38 },
      "cites": []
    },
    {
      "name": "BridgelandStabLean.Lattice.finrank_numLattice",
      "module": "BridgelandStabLean.Lattice.NumericalK",
      "kind": "theorem",
      "is_instance": false, "is_internal": false, "is_private": false,
      "is_reducible": false,
      "num_levels": 0,
      "type_pp": "Module.finrank \u2124 BridgelandStabLean.Lattice.NumLattice = 2",
      "value_pp": null,
      "local_deps": ["BridgelandStabLean.Lattice.NumLattice"],
      "scc_members": [],
      "axioms": ["Classical.choice", "Quot.sound", "propext"],
      "range": { "startLine": 31, "startCol": 0, "endLine": 33, "endCol": 22 },
      "cites": []
    },
    {
      "name": "BridgelandStabLean.GroupAction.preMulAction",
      "module": "BridgelandStabLean.GroupAction.PreStabilityAction",
      "kind": "def",
      "is_instance": true, "is_internal": false, "is_private": false,
      "is_reducible": false,
      "num_levels": 3,
      "type_pp": "(C : Type u) \u2192 [inst : CategoryTheory.Category.{v, u} C] \u2192 ... \u2192 MulAction BridgelandStabLean.GroupAction.GLTilde (CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap C v)",
      "value_pp": null,
      "local_deps": ["BridgelandStabLean.GroupAction.GLTilde",
                     "BridgelandStabLean.GroupAction.actPre"],
      "scc_members": [],
      "axioms": ["Classical.choice", "Quot.sound", "propext"],
      "range": { "startLine": 90, "startCol": 0, "endLine": 109, "endCol": 34 },
      "cites": [
        { "key": "stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2",
          "relation_claimed": "one_way",
          "frontier": ["gltilde-universal-cover", "stability-vs-prestability"],
          "note": "Acts on PreStabilityCondition.WithClassMap, not StabilityCondition." }
      ]
    }
  ],
  "emitted_at": "2026-08-04T09:12:03Z"
}
```

> **Measured, not invented.** `type_pp` for `NumLattice` is exactly `"Type"` and for `finrank_numLattice` is exactly `"Module.finrank ℤ BridgelandStabLean.Lattice.NumLattice = 2"` — read out of the ground-phase probe's real output. The `preMulAction` string above is elided with `...` for readability *in this document only*; **`mfc lint` rejects any `type_pp` containing `⋯` (U+22EF), `…` (U+2026), or the ASCII `...`** precisely because pretty-printer elision would let two different statements hash identically. See rule `E-07`.

### 1.2b `schema/emission-1.0.schema.json` (structure)

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://github.com/chris-dare-dev/math-formal-contract/schema/emission-1.0.schema.json",
  "type": "object",
  "additionalProperties": false,
  "required": ["schema_version","emitter_version","lean_version","lean_githash",
               "lean_options","pp_options","root_lib","modules","counts",
               "constants","emitted_at"],
  "properties": {
    "schema_version": { "const": "emission/1.0" },
    "emitter_version": { "type": "string", "pattern": "^mfc-emit/[0-9]+\\.[0-9]+\\.[0-9]+$" },
    "lean_version": { "type": "string" },
    "lean_githash": { "type": "string", "pattern": "^[0-9a-f]{40}$" },
    "lean_options": { "type": "object", "additionalProperties": { "type": ["boolean","integer","string"] } },
    "pp_options":   { "type": "object", "additionalProperties": { "type": ["boolean","integer","string"] } },
    "root_lib": { "type": "string" },
    "modules": { "type": "array", "minItems": 1, "items": { "type": "string" }, "uniqueItems": true },
    "counts": { "type": "object", "additionalProperties": false,
      "required": ["total","in_scope","internal","with_range","instances","private"],
      "properties": { "total": {"type":"integer","minimum":1},
                      "in_scope": {"type":"integer","minimum":1},
                      "internal": {"type":"integer","minimum":0},
                      "with_range": {"type":"integer","minimum":0},
                      "instances": {"type":"integer","minimum":0},
                      "private": {"type":"integer","minimum":0} },
      "$comment": "minimum:1 on total and in_scope is the VACUOUS-PASS GUARD. An emission of zero constants is the observable signature of a mis-scoped emitter, and it must not validate." },
    "constants": { "type": "array", "minItems": 1, "items": { "$ref": "#/$defs/constant" } },
    "emitted_at": { "type": "string" }
  },
  "$defs": {
    "constant": {
      "type": "object", "additionalProperties": false,
      "required": ["name","module","kind","is_instance","is_internal","is_private",
                   "is_reducible","num_levels","type_pp","value_pp","local_deps",
                   "scc_members","axioms","range","cites"],
      "properties": {
        "name":   { "type": "string", "minLength": 1 },
        "module": { "type": "string", "minLength": 1 },
        "kind":   { "enum": ["axiom","def","theorem","opaque","quot","inductive","ctor","rec"] },
        "is_instance": {"type":"boolean"}, "is_internal": {"type":"boolean"},
        "is_private": {"type":"boolean"},  "is_reducible": {"type":"boolean"},
        "num_levels": { "type": "integer", "minimum": 0 },
        "type_pp":  { "type": "string", "minLength": 1 },
        "value_pp": { "type": ["string","null"] },
        "local_deps": { "type": "array", "items": {"type":"string"}, "uniqueItems": true,
                        "$comment": "SORTED. Topic-local constants only." },
        "scc_members": { "type": "array", "items": {"type":"string"}, "uniqueItems": true },
        "axioms": { "type": "array", "items": {"type":"string"}, "uniqueItems": true,
                    "$comment": "FULL transitive closure from Lean.collectAxioms, SORTED. collectAxioms returns them UNSORTED -- measured: [propext, Quot.sound, Classical.choice] on one decl and [Quot.sound, propext, Classical.choice] on the next in the same run. Sorting is REQUIRED for byte-reproducibility." },
        "range": { "oneOf": [ {"type":"null"},
          { "type":"object","additionalProperties":false,
            "required":["startLine","startCol","endLine","endCol"],
            "properties": { "startLine":{"type":"integer"},"startCol":{"type":"integer"},
                            "endLine":{"type":"integer"},"endCol":{"type":"integer"} } } ] },
        "cites": { "type": "array", "items": { "$ref": "#/$defs/cite" } }
      },
      "allOf": [
        { "$comment": "value_pp is statement-relevant ONLY for these kinds; anywhere else it would fold a PROOF TERM into a statement digest, making every proof edit look like a statement change.",
          "if": { "not": { "properties": { "kind": { "enum": ["def","opaque"] } } } },
          "then": { "properties": { "value_pp": { "type": "null" } } } }
      ]
    },
    "cite": {
      "type": "object", "additionalProperties": false,
      "required": ["key","relation_claimed","frontier","note"],
      "properties": {
        "key": { "type": "string", "pattern": "^stmt:[0-9a-f]{12}:[a-z][a-z0-9._-]{0,63}$" },
        "relation_claimed": { "enum": ["exact","equivalent","specialization","one_way","no_claim"],
          "$comment": "ALWAYS spelled `relation_claimed` in machine artifacts. `relation_confirmed` exists ONLY inside review/1.0. An agent reading this field reads the word 'claimed'." },
        "frontier": { "type": "array", "items": {"type":"string"}, "uniqueItems": true },
        "note": { "type": ["string","null"] }
      }
    }
  }
}
```

### 1.2c `mfc lint` rules over the emission

| Rule id | Check | Fixture |
|---|---|---|
| `E-01` | no constant has `"sorryAx"` in `axioms` | `invalid/sorry-laundered` |
| `E-02` | no constant has `kind: "axiom"` unless its name is in `environment.axiom_policy.additions[].axiom` | `invalid/local-axiom-undeclared` |
| `E-03` | `axioms ⊆ allowlist ∪ declared additions`, recomputed set-wise, never trusted from the file | `invalid/axiom-injected` |
| `E-04` | every `cites[].key` exists in the registry | `invalid/unknown-key` |
| `E-05` | `relation_claimed == "exact"` ⟹ the cited entry's `frontier == []` AND `cites[].frontier == []` | `invalid/relation-exact-with-frontier` |
| `E-06` | `relation_claimed == "no_claim"` ⟹ `note` non-empty | `invalid/no-claim-without-note` |
| `E-07` | no `type_pp` or `value_pp` contains `⋯`, `…`, or `...` | `invalid/elided-type-pp` |
| `E-08` | `counts.in_scope >= 1` and every `.ilean` decl name appears in `constants[].name` (`mfc check-ilean-coverage`) | `invalid/empty-emission` |
| `E-09` | no constant's `module` matches any `closed_lanes[].forbidden_module_prefixes`, and no `local_deps`/`type_pp` mentions any `closed_lanes[].forbidden_constants` | `invalid/closed-lane-breach` |
| `E-10` | `axioms` and `local_deps` arrays are sorted ascending | `invalid/unsorted-axioms` |

`E-09` is what turns CLAUDE.md §4 ("the geometric lane is closed") from a paragraph into a build failure. For this topic the copier answer is:

```yaml
closed_lanes:
  - name: geometry
    forbidden_module_prefixes:
      - "Mathlib.AlgebraicGeometry."
      - "Mathlib.CategoryTheory.Sites."
    forbidden_constants:
      - "CategoryTheory.Sheaf"
    note: >
      D^b(Coh X), Serre duality, Chern characters, HRR, numerical Grothendieck
      groups of varieties, SODs, Fourier-Mukai transforms. None exist in Mathlib
      at the pinned commit. A reachable prefix here means someone started the
      multi-year program by accident.
```

---

## 1.3 `attest/environment.json` — schema `environment/1.0`

**Home:** `bridgeland-stab-lean/attest/environment.json`. Written by `mfc bundle`. **Committed.** This is the artifact that closes audit gap #2 by *handing* arXMCP a pin rather than letting it infer one.

```json
{
  "schema_version": "environment/1.0",
  "env_digest": "52b407ea4c1e8c51bfefe1d9a1f173e142729c6abf09a750a383869d5b160349",
  "env_digest_algorithm": "sha256(canonical_json({lean_toolchain,lean_githash,lean_options,packages:[[name,rev]] sorted}))",
  "lean_toolchain": "leanprover/lean4:v4.29.0",
  "lean_githash": "98dc76e3c0a9b856c9b98726b713fb04fab16740",
  "lean_options": { "autoImplicit": false, "relaxedAutoImplicit": false },
  "lake_version": "5.0.0-src+98dc76e",
  "packages": [
    { "name": "BridgelandStability", "rev": "9e48f23a382ba117b63076a33e0e775389fef1ba",
      "url": "https://github.com/mattrobball/BridgelandStability",
      "input_rev": "9e48f23a382ba117b63076a33e0e775389fef1ba", "inherited": false },
    { "name": "Cli", "rev": "7802da01beb530bf051ab657443f9cd9bc3e1a29",
      "url": "https://github.com/leanprover/lean4-cli", "input_rev": "v4.29.0", "inherited": true },
    { "name": "MD4Lean", "rev": "6a3fb240133bcb7e1a066fdc784b3fdc304e3fc5",
      "url": "https://github.com/acmepjz/md4lean", "input_rev": "main", "inherited": true },
    { "name": "LeanSearchClient", "rev": "c5d5b8fe6e5158def25cd28eb94e4141ad97c843",
      "url": "https://github.com/leanprover-community/LeanSearchClient", "input_rev": "main", "inherited": true },
    { "name": "Qq", "rev": "707efb56d0696634e9e965523a1bbe9ac6ce141d",
      "url": "https://github.com/leanprover-community/quote4", "input_rev": "master", "inherited": true },
    { "name": "aesop", "rev": "7152850e7b216a0d409701617721b6e469d34bf6",
      "url": "https://github.com/leanprover-community/aesop", "input_rev": "master", "inherited": true },
    { "name": "batteries", "rev": "756e3321fd3b02a85ffda19fef789916223e578c",
      "url": "https://github.com/leanprover-community/batteries", "input_rev": "main", "inherited": true },
    { "name": "importGraph", "rev": "48d5698bc464786347c1b0d859b18f938420f060",
      "url": "https://github.com/leanprover-community/import-graph", "input_rev": "main", "inherited": true },
    { "name": "informal", "rev": "be2042471694a77eea68089c770de3c9a9245d7c",
      "url": "https://github.com/mattrobball/lean-informal", "input_rev": "main", "inherited": true },
    { "name": "mathlib", "rev": "8a178386ffc0f5fef0b77738bb5449d50efeea95",
      "url": "https://github.com/leanprover-community/mathlib4", "input_rev": "v4.29.0", "inherited": true },
    { "name": "plausible", "rev": "83e90935a17ca19ebe4b7893c7f7066e266f50d3",
      "url": "https://github.com/leanprover-community/plausible", "input_rev": "main", "inherited": true },
    { "name": "proofwidgets", "rev": "3c52dee17f0cd89c1ec14de78920d1bdaa3d26b3",
      "url": "https://github.com/leanprover-community/ProofWidgets4", "input_rev": "v0.0.95", "inherited": true },
    { "name": "subverso", "rev": "ce893b9042128037e2d3c0158b9567fab9fae268",
      "url": "https://github.com/leanprover/subverso", "input_rev": "main", "inherited": true },
    { "name": "verso", "rev": "7ae82ac2ae54ae5dcc9948a701669e9b596e5cae",
      "url": "https://github.com/leanprover/verso", "input_rev": "v4.29.0", "inherited": true }
  ],
  "input_rev_is_branch": ["MD4Lean","LeanSearchClient","Qq","aesop","batteries",
                          "importGraph","informal","plausible","subverso"],
  "root_package": {
    "name": "BridgelandStabLean",
    "url": "https://github.com/chris-dare-dev/bridgeland-stab-lean",
    "rev": "f166a3d73e2062052b249102001900b3beb929d1",
    "tag": "v0.1.0",
    "worktree_dirty": false
  },
  "axiom_policy": {
    "allowlist": ["Classical.choice", "Quot.sound", "propext"],
    "additions": []
  },
  "emitter_version": "mfc-emit/1.0.0",
  "mfc_version": "1.0.0",
  "contract_repo": { "url": "https://github.com/chris-dare-dev/math-formal-contract",
                     "rev": "0000000000000000000000000000000000000000" }
}
```

Schema notes (`environment-1.0.schema.json`, `additionalProperties: false` throughout):

* `env_digest`, `lean_githash`, `packages[].rev`, `root_package.rev`, `contract_repo.rev` all `pattern: "^[0-9a-f]{40}$"` (except `env_digest`: 64).
* `root_package.tag` is `["string","null"]`. A **null tag is a valid artifact but an invalid release**: `tools/formal_release_pin.py` refuses to pin it. This is the mechanical statement of "arXMCP pins *released* formalizations" — and it is why the migration's step 8 (`git tag v0.1.0`) is not optional; `git tag` in this repo is currently empty.
* `worktree_dirty: true` → `mfc lint` fails in CI mode.
* `input_rev_is_branch[]` is generated, not authored: it names every package whose `inputRev` is not a 40-hex, i.e. every package a `lake update` would silently re-resolve. It is emitted so the drift risk is *visible in the trust record*, and it explains why `env_digest` hashes `rev` and not `inputRev`.

---

## 1.4 `attest/declarations.json` — schema `declarations/1.0`

**Home:** `bridgeland-stab-lean/attest/declarations.json`. Written by `mfc bundle` **from** `lean-emission.json` + `environment.json`. **Committed.** Every field `mfc` adds is *recomputed*, never carried across from the emission.

```json
{
  "schema_version": "declarations/1.0",
  "env_digest": "52b407ea4c1e8c51bfefe1d9a1f173e142729c6abf09a750a383869d5b160349",
  "emission_sha256": "<64 hex of the lean-emission.json bytes it was derived from>",
  "statement_digest_version": "statement-digest/1",
  "counts": { "total": 121, "in_scope": 78, "internal": 43, "cited": 9 },
  "declarations": [
    {
      "name": "BridgelandStabLean.Lattice.NumLattice",
      "module": "BridgelandStabLean.Lattice.NumericalK",
      "kind": "def",
      "is_internal": false,
      "statement_digest": "c44dc5545999699041be0421a8767f82c45ae16d38a736db3dbf532a3d6a1acf",
      "local_deps": [],
      "axioms": [],
      "axioms_disallowed": [],
      "contains_sorry_ax": false,
      "local_axioms": [],
      "range": { "startLine": 27, "startCol": 0, "endLine": 27, "endCol": 38 },
      "cites": []
    },
    {
      "name": "BridgelandStabLean.Lattice.finrank_numLattice",
      "module": "BridgelandStabLean.Lattice.NumericalK",
      "kind": "theorem",
      "is_internal": false,
      "statement_digest": "bee014f3f5e761cfe1e329560ab0c5f26ebf3c6c24be8c85bcfed64b7cf72af2",
      "local_deps": ["BridgelandStabLean.Lattice.NumLattice"],
      "axioms": ["Classical.choice", "Quot.sound", "propext"],
      "axioms_disallowed": [],
      "contains_sorry_ax": false,
      "local_axioms": [],
      "range": { "startLine": 31, "startCol": 0, "endLine": 33, "endCol": 22 },
      "cites": []
    }
  ]
}
```

> **Both `statement_digest` values above are [COMPUTED]** by running `mfc/digest.py::statement_digest` on the real measured `type_pp`/`value_pp`. They are reproducible: `statement_digest("…NumLattice", "def", "Type", "Fin 2 → ℤ", {})` → `c44dc554…`; `statement_digest("…finrank_numLattice", "theorem", "Module.finrank ℤ BridgelandStabLean.Lattice.NumLattice = 2", None, {"BridgelandStabLean.Lattice.NumLattice": "c44dc554…"})` → `bee014f3…`.

**Recomputation rules (`mfc bundle`, never trusting the emission):**

```python
# mfc/bundle.py  (the load-bearing 12 lines)
policy = set(env["axiom_policy"]["allowlist"]) | {a["axiom"] for a in env["axiom_policy"]["additions"]}
for c in emission["constants"]:
    axioms = sorted(set(c["axioms"]))                     # RE-SORT, RE-DEDUPE
    disallowed = sorted(set(axioms) - policy)             # RECOMPUTED. The emission
                                                          # never reports this field.
    contains_sorry = "sorryAx" in axioms                  # RECOMPUTED
    local_axioms = sorted(k["name"] for k in emission["constants"] if k["kind"] == "axiom")
    # INVARIANT, checked here and again in the schema:
    #   contains_sorry_ax == True  =>  the axiom_closure axis MUST be `fail`.
    #   There is no code path in mfc that can produce `pass` with sorryAx present.
```

Schema-level cross-field constraint in `declarations-1.0.schema.json`:

```json
{ "$comment": "A declaration carrying sorryAx must report it in BOTH places, consistently. The `invalid/sorry-laundered` fixture flips exactly one of these and MUST be rejected.",
  "allOf": [
    { "if":   { "properties": { "contains_sorry_ax": { "const": true } }, "required": ["contains_sorry_ax"] },
      "then": { "properties": { "axioms": { "contains": { "const": "sorryAx" } } } } },
    { "if":   { "properties": { "axioms": { "contains": { "const": "sorryAx" } } } },
      "then": { "properties": { "contains_sorry_ax": { "const": true } } } }
  ] }
```

---

## 1.5 `attest/review.yaml` — schema `review/1.0`

**Home:** `bridgeland-stab-lean/attest/review.yaml`. **The only contract file no machine may write.** `mfc bundle` reads it; `mfc` has no subcommand that creates or edits an entry, and CI asserts `git log --format=%an -1 -- attest/review.yaml` is not a bot identity.

```yaml
# ============================================================================
# Human faithfulness review.  Written by hand, by a named person, on a date.
#
# An ABSENT entry means NOT REVIEWED, and that is structurally distinct from
# every present value.  There is no default.  There is no `agent_drafted`
# state -- deliberately, because it would let an LLM verdict occupy the one
# axis that exists to catch what an LLM cannot: that `Fin 2 -> Z` was
# described as a Kuznetsov component.
#
# `inconclusive` is a COMPLETE and LEGITIMATE outcome.  Abstention is a
# success, not a failure.
# ============================================================================
schema_version: "review/1.0"

reviews:
  - key: "stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2"
    decl: "BridgelandStabLean.GroupAction.preMulAction"
    reviewer:
      name: "Chris Dare"
      email: "chris.dare.bak@gmail.com"
    reviewed_at: "2026-08-11"

    # What the reviewer ACTUALLY SAW.  Three digests that go stale
    # INDEPENDENTLY -- the Lean statement, the paper text, the environment.
    reviewed_statement_digest: "<64 hex — copied from declarations.json at review time>"
    reviewed_quote_sha256:     "<64 hex — copied from the registry at review time>"
    reviewed_env_digest:       "52b407ea4c1e8c51bfefe1d9a1f173e142729c6abf09a750a383869d5b160349"

    faithfulness: adequate        # adequate | divergent | inadequate | inconclusive
    relation_confirmed: one_way   # exact|equivalent|specialization|one_way|
                                  # no_claim|disputed
                                  # `relation_confirmed` appears ONLY in this file.

    divergences:
      - "Acts on PreStabilityCondition.WithClassMap; the paper's Lemma 8.2 is
         about StabilityCondition, which additionally carries local finiteness.
         Frontier item `stability-vs-prestability` is undischarged."
      - "GLTilde is proved a GROUP only. Nothing here establishes it is the
         universal cover of GL+(2,R): projection surjectivity, fibre Z, and
         simple connectedness are all unproved. Frontier item
         `gltilde-universal-cover` is undischarged. The NAME asserts more than
         the proved content; do not cite GLTilde as a formalized universal cover."
    note: >
      Reviewed against the arXiv PDF at the version pinned in registry
      source.version.  I read the Lean statement and the printed statement side
      by side.  This review says the Lean statement is an ADEQUATE one-way
      consequence-direction rendering under the two named divergences.  It does
      NOT say the paper's Lemma 8.2 is formalized.
```

`schema/review-1.0.schema.json` essentials:

```json
{ "type":"object","additionalProperties":false,
  "required":["schema_version","reviews"],
  "properties":{
    "schema_version":{"const":"review/1.0"},
    "reviews":{"type":"array","items":{
      "type":"object","additionalProperties":false,
      "required":["key","decl","reviewer","reviewed_at","reviewed_statement_digest",
                  "reviewed_quote_sha256","reviewed_env_digest","faithfulness",
                  "relation_confirmed","divergences"],
      "properties":{
        "key":{"pattern":"^stmt:[0-9a-f]{12}:[a-z][a-z0-9._-]{0,63}$","type":"string"},
        "decl":{"type":"string","minLength":1},
        "reviewer":{"type":"object","additionalProperties":false,
          "required":["name"],
          "properties":{"name":{"type":"string","minLength":1},
                        "email":{"type":["string","null"]},
                        "affiliation":{"type":["string","null"]}}},
        "reviewed_at":{"type":"string","pattern":"^[0-9]{4}-[0-9]{2}-[0-9]{2}$"},
        "reviewed_statement_digest":{"type":"string","pattern":"^[0-9a-f]{64}$"},
        "reviewed_quote_sha256":{"type":["string","null"],"pattern":"^[0-9a-f]{64}$"},
        "reviewed_env_digest":{"type":"string","pattern":"^[0-9a-f]{64}$"},
        "faithfulness":{"enum":["adequate","divergent","inadequate","inconclusive"]},
        "relation_confirmed":{"enum":["exact","equivalent","specialization","one_way",
                                      "no_claim","disputed"]},
        "divergences":{"type":"array","items":{"type":"string"}},
        "note":{"type":["string","null"]}
      },
      "allOf":[
        {"$comment":"A `divergent` or `inadequate` verdict without a written divergence is not a review.",
         "if":{"properties":{"faithfulness":{"enum":["divergent","inadequate"]}},"required":["faithfulness"]},
         "then":{"properties":{"divergences":{"minItems":1}}}},
        {"$comment":"`exact` confirmed with a stated divergence is self-contradictory.",
         "if":{"properties":{"relation_confirmed":{"const":"exact"}},"required":["relation_confirmed"]},
         "then":{"properties":{"divergences":{"maxItems":0}}}}
      ]}}}}
```

Additional `mfc lint` rules: `V-01` at most one review per `(key, decl)` pair — a second review of the same pair must **supersede** by later `reviewed_at`, and `mfc` takes the latest; `V-02` `reviewed_env_digest` must appear in the repo's git history of `attest/environment.json` (a review pinned to an environment that never existed is rejected).

---

## 1.6 `attest/build.json` — schema `build/1.0`

```json
{
  "schema_version": "build/1.0",
  "env_digest": "52b407ea4c1e8c51bfefe1d9a1f173e142729c6abf09a750a383869d5b160349",
  "lake_build_exit": 0,
  "lake_build_jobs": 3428,
  "diagnostics": [
    { "file_name": "BridgelandStabLean/GroupAction/SlicingAction.lean",
      "severity": "warning", "kind": "linter.unusedVariables",
      "pos": { "line": 121, "column": 8 },
      "end_pos": { "line": 121, "column": 30 },
      "data": "unused variable `hb`" }
  ],
  "error_count": 0,
  "warning_count": 1,
  "sorry_diagnostic_count": 0,
  "independent_checkers": [
    { "name": "leanchecker", "version": "bundled-4.29.0", "value": "pass", "allow_sorry": false },
    { "name": "nanoda",      "version": "unknown",        "value": "not_run", "allow_sorry": false }
  ],
  "ci": { "run_url": "https://github.com/chris-dare-dev/bridgeland-stab-lean/actions/runs/…",
          "workflow_sha": "f166a3d73e2062052b249102001900b3beb929d1",
          "runner": "ubuntu-24.04" },
  "produced_at": "2026-08-04T09:12:41Z"
}
```

**How `diagnostics[]` is produced.** `lake build` emits 42 bytes of prose and has no `--json` at Lake 5.0.0. The machine-readable path that *does* exist and *was verified*:

```bash
lake env lean --json scripts/Emit.lean > attest/lean.ndjson
```

produces one JSON object per message with keys `{caption, data, endPos:{column,line}, fileName, isSilent, keepFullRange, kind, pos:{column,line}, severity}`. **The `data` strings are unwrapped** — the 100-column wrapping that makes `scripts/Audit.lean` unparseable by line is a terminal-render artifact, absent from JSON. `mfc bundle` folds this NDJSON into `diagnostics[]`.

**Three measured facts that force this design and are recorded in the schema's `$comment`s:**

| probe on this toolchain | exit |
|---|---|
| `lake build` clean | 0 |
| `lake env lean` on a genuine elaboration error | 1 |
| `lake env lean` on `theorem probe_thm : True := by sorry` + `#print axioms probe_thm` printing `[sorryAx]` | **0** |
| `lake env lean -E hasSorry` on the same file — relabels the message `error: declaration uses 'sorry'` in stdout | **0** |

So `sorry_diagnostic_count` is derived by counting NDJSON records with `kind == "hasSorry"`, and **the exit code is never the gate**. `build/1.0` schema requires: `sorry_diagnostic_count > 0` ⟹ the `elaborates` axis MUST be `fail`.

`independent_checkers[].value` is four-valued, and `not_run` is honest: **I could not confirm offline that `leanprover/lean-action` exposes `leanchecker` / `nanoda` / `nanoda-allow-sorry` inputs, nor that `nanoda-allow-sorry` defaults to `true`.** If the inputs do not exist, axis 2 ships `not_run` and nothing in the design silently counts it as evidence. If they do exist, `allow_sorry` must be `false` or the entry is rejected by:

```json
{ "if": { "properties": { "value": { "const": "pass" } }, "required": ["value"] },
  "then": { "properties": { "allow_sorry": { "const": false } },
            "$comment": "A checker that passed WHILE PERMITTING sorry has not checked the thing this axis is about." } }
```

---

## 1.7 `attest/bundle.json` — schema `bundle/1.0` (in-toto Statement v1)

```json
{
  "schema_version": "bundle/1.0",
  "_type": "https://in-toto.io/Statement/v1",

  "subject": [
    { "name": "bridgeland-stab-lean",
      "uri": "https://github.com/chris-dare-dev/bridgeland-stab-lean",
      "digest": { "gitCommit": "f166a3d73e2062052b249102001900b3beb929d1",
                  "gitTag": "v0.1.0" } }
  ],

  "contract_repo": { "url": "https://github.com/chris-dare-dev/math-formal-contract",
                     "rev": "0000000000000000000000000000000000000000" },
  "env_digest": "52b407ea4c1e8c51bfefe1d9a1f173e142729c6abf09a750a383869d5b160349",
  "registry_sha256": "<64 hex over the concatenated canonical bytes of registry/*.yaml>",

  "predicates": [
    { "predicateType": "https://github.com/chris-dare-dev/math-formal-contract/predicate/environment/v1",
      "file": "attest/environment.json",   "sha256": "<64 hex>",
      "produced_by": "mfc/1.0.0",          "produced_at": "2026-08-04T09:12:41Z",
      "env_digest": "52b407ea…", "self_attested": true },

    { "predicateType": "https://github.com/chris-dare-dev/math-formal-contract/predicate/declarations/v1",
      "file": "attest/declarations.json",  "sha256": "<64 hex>",
      "produced_by": "mfc-emit/1.0.0 + mfc/1.0.0", "produced_at": "2026-08-04T09:12:41Z",
      "env_digest": "52b407ea…", "self_attested": true },

    { "predicateType": "https://github.com/chris-dare-dev/math-formal-contract/predicate/build/v1",
      "file": "attest/build.json",         "sha256": "<64 hex>",
      "produced_by": "lean-action + mfc/1.0.0", "produced_at": "2026-08-04T09:12:41Z",
      "env_digest": "52b407ea…", "self_attested": true },

    { "predicateType": "https://github.com/chris-dare-dev/math-formal-contract/predicate/human-review/v1",
      "file": "attest/review.yaml",        "sha256": "<64 hex>",
      "produced_by": "human:Chris Dare",   "produced_at": "2026-08-11T00:00:00Z",
      "env_digest": "52b407ea…", "self_attested": false },

    { "predicateType": "https://github.com/chris-dare-dev/math-formal-contract/predicate/corpus-resolution/v1",
      "file": "attest/resolution.json",    "sha256": "<64 hex>",
      "produced_by": "arxmcp/statement_resolve.py@1.0.0", "produced_at": "2026-08-04T08:55:10Z",
      "env_digest": null, "self_attested": false,
      "$comment": "env_digest is null BY CONSTRUCTION: this predicate is about the corpus, not about a Lean environment. A non-null value here is rejected." },

    { "predicateType": "https://github.com/chris-dare-dev/math-formal-contract/predicate/provisional-self-reported/v1",
      "file": "attest/lean-verify-transcript.json", "sha256": "<64 hex>",
      "produced_by": "arxmcp/lean_verify@v4.31.0",  "produced_at": "2026-08-04T08:59:00Z",
      "env_digest": "<the v4.31.0 digest — DIFFERENT from the subject's>",
      "self_attested": true,
      "$comment": "RESERVED predicate type. It satisfies ZERO axes. This is where output from a Lean environment that is not the pinned one is allowed to be RECORDED without being allowed to COUNT."
    }
  ],

  "unrecognized_predicates": [],

  "$comment": "SLSA's VerificationSummaryAttestation is DELIBERATELY NOT USED. Its `verificationResult: PASSED|FAILED` is exactly the single collapsed trust token arXMCP CLAUDE.md section 4.9 forbids. One subject, N independently-dated, independently-sourced predicates, no aggregate."
}
```

Schema constraints:

* `predicates[].predicateType`: `"type": "string", "format": "uri"`. **Unknown values are ingested, never served**: `tools/formal_release_pin.py` moves any predicate whose type is not in the vendored `contract/predicate-types.json` into `unrecognized_predicates[]` and records it. That registry is what makes the URI extension point safe — a new topic can mint its own predicate types without touching the core schema, and an arXMCP that does not know one cannot be tricked into rendering it as evidence.
* `predicates[].self_attested` is **required**, `boolean`. Honest labelling for a solo-operated repo: `true` means "the party that wrote the code also produced this measurement."
* Exactly one predicate per `predicateType` per bundle; `file` paths must be repo-relative and must exist; `sha256` must equal `file_digest(file)`.

---

## 1.8 `attest/resolution.json` — schema `resolution/1.0`

**Produced by arXMCP. Committed into the Lean repo.** This is the only artifact that crosses the seam in the corpus→formal direction, and it is the only axis with genuinely independent evidence: a different system, a different program.

```json
{
  "schema_version": "resolution/1.0",

  "registry_sha256": "<64 hex over the EXACT registry bytes this ran against>",

  "notebook": "bridgeland-stability",
  "corpus_version": 5048,
  "corpus_manifest_content_hash": "<64 hex from arxmcp://corpus-manifest>",
  "resolver_version": "arxmcp/statement_resolve.py@1.0.0",
  "chunker_version": "<from the chunks row>",
  "generated_at": "2026-08-04T08:55:10Z",

  "results": [
    { "key": "stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2",
      "resolution": "current",
      "matched_by": "quote_sha256",
      "chunk_id": "arxiv:math/0212237:a82c3230040fd724",
      "matched_body_sha256": "ebacfe5caa6c1df8229ec6bfbcf55f855a524a77cf78a9fb3171b81172d6f50d",
      "printed_number": "8.2",
      "similarity": null,
      "reason": null },

    { "key": "stmt:9f4c1a20b7d3:bridgeland2007.obl-stab-action",
      "resolution": "not_run",
      "matched_by": "none",
      "chunk_id": null,
      "matched_body_sha256": null,
      "printed_number": null,
      "similarity": null,
      "reason": "kind==obligation and quote_sha256 is null; nothing to resolve" }
  ],

  "counts": { "current": 1, "drifted": 0, "unresolvable": 0,
              "paper_absent": 0, "not_run": 1 }
}
```

Schema (`resolution-1.0.schema.json`) — the load-bearing constraints:

```json
{ "$defs": { "result": {
  "type":"object","additionalProperties":false,
  "required":["key","resolution","matched_by","chunk_id","matched_body_sha256",
              "printed_number","similarity","reason"],
  "properties":{
    "key":{"type":"string","pattern":"^stmt:[0-9a-f]{12}:[a-z][a-z0-9._-]{0,63}$"},
    "resolution":{"enum":["current","drifted","unresolvable","paper_absent","not_run"]},
    "matched_by":{"enum":["quote_sha256","printed_number","fuzzy","none"]},
    "chunk_id":{"type":["string","null"]},
    "matched_body_sha256":{"type":["string","null"],"pattern":"^[0-9a-f]{64}$"},
    "printed_number":{"type":["string","null"]},
    "similarity":{"type":["number","null"],"minimum":0,"maximum":1},
    "reason":{"type":["string","null"]}
  },
  "allOf":[
    {"$comment":"`current` REQUIRES a recomputed body digest. A resolver that says `current` without showing its work is rejected.",
     "if":{"properties":{"resolution":{"const":"current"}},"required":["resolution"]},
     "then":{"required":["matched_body_sha256","chunk_id"],
             "properties":{"matched_body_sha256":{"type":"string","pattern":"^[0-9a-f]{64}$"},
                           "chunk_id":{"type":"string"}}}},
    {"$comment":"A FUZZY match can NEVER be `current`. Nearest-neighbour similarity is not identity, and this is the single line that stops a dense-ANN retrieval system from silently re-pointing a citation at a different theorem.",
     "if":{"properties":{"matched_by":{"const":"fuzzy"}},"required":["matched_by"]},
     "then":{"properties":{"resolution":{"enum":["drifted","unresolvable"]},
                           "similarity":{"type":"number"}}}},
    {"$comment":"printed_number is a HINT. Matching on it alone cannot be `current`, because printed_number is populated only on the ar5iv/LaTeXML path (36 of 66 chunks even on this paper) and authors renumber between versions.",
     "if":{"properties":{"matched_by":{"const":"printed_number"}},"required":["matched_by"]},
     "then":{"properties":{"resolution":{"enum":["drifted"]}}}}
  ]}}}
```

**`registry_sha256` is the entire cross-repo freshness mechanism.** One comparison, no clocks, no mtimes, no network. `mfc check-resolution` recomputes the registry bytes' digest and fails if it differs — so editing the registry without re-running the resolver turns the Lean repo's CI red, and there is no way to forget.

---

## 1.9 `served-record/1.0` — what `arxmcp://formal/{notebook}/{key}` returns

Not a file on disk; the shape arXMCP composes and serves. **Key order is load-bearing and pinned by a test.**

```json
{
  "caveats": [
    "faithfulness: not_run — no human has compared this Lean statement to the paper. Typecheck is not fidelity.",
    "frontier: 2 undischarged items (gltilde-universal-cover, stability-vs-prestability) — this is a theorem about the interface, not yet about the object.",
    "relation_claimed: one_way — this is the AUTHOR'S claim about the binding strength. No reviewer has confirmed it.",
    "axiom_closure: pass — this says nothing about whether the statement is the paper's.",
    "kernel_replay: not_run — no independent checker result is on file for this release."
  ],

  "axes": {
    "elaborates":          { "value": "pass",    "env_digest": "52b407ea…", "computed_at": "2026-08-04T09:12:41Z", "source": "lean-action@<sha>", "self_attested": true,  "evidence": { "lake_build_exit": 0, "error_count": 0, "diagnostics_ref": "attest/build.json" }, "ci": { "run_url": "…", "workflow_sha": "f166a3d…", "runner": "ubuntu-24.04" } },
    "kernel_replay":       { "value": "not_run", "env_digest": "52b407ea…", "computed_at": null, "source": null, "self_attested": true, "evidence": { "checker": null, "version": null, "allow_sorry": false } },
    "axiom_closure":       { "value": "pass",    "env_digest": "52b407ea…", "computed_at": "2026-08-04T09:12:41Z", "source": "mfc-emit/1.0.0", "self_attested": true, "evidence": { "policy_allowlist": ["Classical.choice","Quot.sound","propext"], "observed": ["Classical.choice","Quot.sound","propext"], "disallowed": [], "contains_sorry_ax": false, "local_axioms": [] } },
    "statement_stable":    { "value": "not_applicable", "env_digest": "52b407ea…", "computed_at": "2026-08-04T09:12:41Z", "source": "mfc/1.0.0", "self_attested": true, "evidence": { "current": "<64 hex>", "reviewed": null, "env_digest": "52b407ea…", "reviewed_env_digest": null }, "reason": "no review on file, so there is no baseline to be stable against" },
    "binding_resolves":    { "value": "pass",    "env_digest": null, "computed_at": "2026-08-04T08:55:10Z", "source": "arxmcp/statement_resolve.py@1.0.0", "self_attested": false, "evidence": { "resolution": "current", "matched_by": "quote_sha256", "matched_body_sha256": "ebacfe5c…", "corpus_manifest_content_hash": "<64 hex>", "corpus_version": 5048 } },
    "frontier_discharged": { "value": "fail",    "env_digest": "52b407ea…", "computed_at": "2026-08-04T09:12:41Z", "source": "mfc/1.0.0", "self_attested": true, "evidence": { "open": ["gltilde-universal-cover","stability-vs-prestability"], "discharged": [] } },
    "faithfulness":        { "value": "not_run", "env_digest": null, "computed_at": null, "source": null, "self_attested": false, "evidence": { "reviewer": null, "reviewed_at": null, "relation_confirmed": null, "divergences": [] } }
  },

  "key": "stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2",
  "registry_id": "9f4c1a20b7d3",
  "kind": "lemma",
  "title": "Lemma 8.2",
  "informal": "For (T, f) in the group G~L+(2,R) … defines a right action …",
  "source": { "scheme": "arxiv", "id": "math/0212237", "version": "v?",
              "printed_number": "8.2", "locator": "section 8" },
  "quote_mode": "verbatim",
  "quote_sha256": "ebacfe5c…",

  "bindings": [
    { "decl": "BridgelandStabLean.GroupAction.preMulAction",
      "module": "BridgelandStabLean.GroupAction.PreStabilityAction",
      "relation_claimed": "one_way",
      "relation_confirmed": null,
      "statement_digest": "<64 hex>",
      "permalink": "https://github.com/chris-dare-dev/bridgeland-stab-lean/blob/f166a3d73e2062052b249102001900b3beb929d1/BridgelandStabLean/GroupAction/PreStabilityAction.lean#L90-L109" }
  ],

  "assumption_frontier": [
    { "id": "gltilde-universal-cover", "kind_class": "open-problem", "kind_label": "covering-space",
      "statement": "The projection GLTilde -> GL+(2,R) is surjective with fibre Z, and GLTilde is simply connected. …", "discharged_by": null },
    { "id": "stability-vs-prestability", "kind_class": "missing-library", "kind_label": "local-finiteness",
      "statement": "The action is proved on PreStabilityCondition.WithClassMap only. …", "discharged_by": null }
  ],

  "release": { "repo": "https://github.com/chris-dare-dev/bridgeland-stab-lean",
               "tag": "v0.1.0", "commit": "f166a3d73e2062052b249102001900b3beb929d1",
               "env_digest": "52b407ea…", "pinned_at": "2026-08-04T10:00:00Z" },

  "contract": { "repo": "https://github.com/chris-dare-dev/math-formal-contract",
                "rev": "<40 hex>", "schema_version": "served-record/1.0" }
}
```

**`caveats[]` is the first key, is generated mechanically from the axis values, and cannot be authored.** The generator:

```python
# mfc/caveats.py — vendored into arXMCP, run at serve time.
def caveats(axes: dict, frontier: list, bindings: list) -> list[str]:
    out: list[str] = []
    f = axes["faithfulness"]["value"]
    if f == "not_run":
        out.append("faithfulness: not_run — no human has compared this Lean "
                   "statement to the paper. Typecheck is not fidelity.")
    elif f == "fail":
        out.append("faithfulness: fail — a named human reviewed this and found "
                   "it NOT an adequate rendering of the source statement.")
    elif f == "not_applicable":
        out.append("faithfulness: not_applicable — the review on file was made "
                   "against a different environment digest and does not carry over.")
    open_items = [x["id"] for x in frontier if x["discharged_by"] is None]
    if open_items:
        out.append(f"frontier: {len(open_items)} undischarged item(s) "
                   f"({', '.join(open_items)}) — this is a theorem about the "
                   f"interface, not yet about the object.")
    for b in bindings:
        if b["relation_confirmed"] is None:
            out.append(f"relation_claimed: {b['relation_claimed']} — this is the "
                       f"AUTHOR'S claim about the binding strength. No reviewer "
                       f"has confirmed it.")
            break
    if axes["axiom_closure"]["value"] == "pass":
        out.append("axiom_closure: pass — this says nothing about whether the "
                   "statement is the paper's.")
    if axes["kernel_replay"]["value"] == "not_run":
        out.append("kernel_replay: not_run — no independent checker result is on "
                   "file for this release.")
    if axes["binding_resolves"]["value"] in ("fail", "not_run"):
        out.append("binding_resolves: the registered quote no longer matches the "
                   "corpus. The paper text may have changed, or the parse did.")
    return out
```

The whole payload is wrapped in `<retrieved_formal_record>…</retrieved_formal_record>` via the existing `server.tools.wrap_retrieved_text` discipline, because `informal`, `note`, `divergences[]`, and `frontier[].statement` are all operator-authored free text flowing to an agent.

---

# PART 2 — The Lean-side emitter

## 2.0 What is verified and what is not

**VERIFIED on this machine, at `leanprover/lean4:v4.29.0` / Lake `5.0.0-src+98dc76e`** (the ground-phase `Inventory.lean` probe ran, exit 0, 121 constants, 69 451 bytes, 39.8 s wall, and produced **byte-identical output across two consecutive runs**):

`env.constants` · `env.getModuleIdxFor?` · `env.header.moduleNames` · `Lean.collectAxioms` · `Lean.findDeclarationRanges?` · `Lean.Meta.isInstance` · `Lean.PrettyPrinter.ppExpr` · `Lean.Json` / `Json.mkObj` / `Json.pretty` · `Lean.versionString` · `Lean.githash` · `Lean.isPrivateName` · `n.isInternalDetail` (as a `Name` method; the bare identifier `isInternalDetail` does **not** resolve) · `IO.FS.writeFile` from `CommandElabM` · `lake env lean <file>` exiting 1 on an elaboration error.

**NOT VERIFIED — flagged, with the exact command to settle each:**

| Unverified | Settle with |
|---|---|
| `@[cites]` attribute syntax + `registerSimplePersistentEnvExtension` round-tripping through `.olean` | `lake env lean lean/MathFormalContract/Cites.lean` then a two-module import test |
| `Lean.Expr` constant traversal helper name (`Expr.getUsedConstants` vs `Expr.getUsedConstantsAsSet`) at v4.29.0 | `#check @Lean.Expr.getUsedConstants` |
| The exact option name that disables pretty-printer elision | `#eval do let o ← Lean.getOptions; …` — but **the guard does not depend on knowing it** (see `E-07`) |
| `[[lean_exe]]` + `Lean.importModules`-based `main` | build it; the fallback is the verified `lake env lean` path below |
| Whether a failing `#eval` propagates to a non-zero process exit | `lake env lean scripts/Emit.lean; echo $?` — **the CI does not depend on this**, it parses `--json` for `severity == "error"` |

## 2.1 The shared Lake package

`math-formal-contract/lean/lakefile.toml`:

```toml
name = "MathFormalContract"
version = "1.0.0"
defaultTargets = ["MathFormalContract"]

# ZERO dependencies. Core Lean only. No Mathlib, no anchor.
# This is why taking it as a [[require]] in a topic repo is defensible against
# CLAUDE.md section 1 ("a second pin is a second thing to drift"): it is a leaf
# with no transitive closure, so it is the least drift-prone pin in the tree.

[[lean_lib]]
name = "MathFormalContract"
```

## 2.2 `lean/MathFormalContract/Cites.lean` — the `@[cites]` attribute

Modelled directly on `Mathlib/Tactic/StacksAttribute.lean` (verified present at `.lake/packages/mathlib/Mathlib/Tactic/StacksAttribute.lean` at the pin). **It lives in the shared package and is never vendored** — duplicate attribute registration is an import-time error, so two vendored copies would make two topic repos unable to coexist in one Lean environment.

```lean
/-
Copyright (c) 2026 math-formal-contract contributors. Apache-2.0.

`@[cites]` — bind a Lean declaration to a statement in an external corpus.

Direct prior art: `Mathlib/Tactic/StacksAttribute.lean` (@[stacks TAG]).
Two properties are copied deliberately:
  * the external id is an OPAQUE, EXTERNALLY-ISSUED, PERMANENTLY-STABLE string;
  * the binding lives IN THE SOURCE, NEXT TO THE DECLARATION, and is
    machine-extractable from the ENVIRONMENT -- no side file to drift.
-/
import Lean

namespace MathFormalContract

open Lean

/-- How strongly the author claims the Lean declaration renders the source
statement.  ALWAYS "claimed": confirming it is a human review's job, and the
confirmed value lives only in `attest/review.yaml`. -/
inductive Relation where
  | exact | equivalent | specialization | one_way | no_claim
  deriving Inhabited, DecidableEq, Repr

def Relation.toString : Relation → String
  | .exact => "exact" | .equivalent => "equivalent"
  | .specialization => "specialization" | .one_way => "one_way"
  | .no_claim => "no_claim"

def Relation.ofString? : String → Option Relation
  | "exact" => some .exact | "equivalent" => some .equivalent
  | "specialization" => some .specialization | "one_way" => some .one_way
  | "no_claim" => some .no_claim
  | _ => none

structure CiteEntry where
  declName        : Name
  key             : String
  relationClaimed : Relation
  frontier        : Array String
  note            : String
  deriving Inhabited

/-- Persistent environment extension: survives into the `.olean` and is
readable by any importer, exactly like `Mathlib.Tactic.Stacks.tagExt`. -/
initialize citesExt :
    SimplePersistentEnvExtension CiteEntry (Array CiteEntry) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun as => as.foldl Array.append #[]
    addEntryFn    := Array.push
  }

/-- The citation-key grammar, enforced AT PARSE TIME (the Stacks attribute
enforces its 4-char tag grammar the same way).  Three colon-separated
segments, fixed arity.  NO paper coordinate here: it lives in typed registry
fields, so an id containing a delimiter (`textbook:iwaniec-kowalski`) cannot
break the tokenizer. -/
def keyWellFormed (s : String) : Bool := Id.run do
  let parts := s.splitOn ":"
  unless parts.length == 3 do return false
  let #[pfx, rid, lbl] := parts.toArray | return false
  unless pfx == "stmt" do return false
  unless rid.length == 12 && rid.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    return false
  unless 1 ≤ lbl.length && lbl.length ≤ 64 do return false
  unless lbl.front.isLower do return false
  return lbl.all fun c =>
    c.isLower || c.isDigit || c == '.' || c == '_' || c == '-'

syntax (name := citesAttr) "cites " str
  (" relation " ident)?
  (" frontier " "[" str,* "]")?
  (" note " str)? : attr

initialize registerBuiltinAttribute {
  name  := `citesAttr
  descr := "Bind this declaration to a statement id in an external corpus registry."
  add   := fun decl stx _kind => do
    match stx with
    | `(attr| cites $k:str $[relation $r:ident]? $[frontier [$fs:str,*]]? $[note $nt:str]?) => do
      let key := k.getString
      unless keyWellFormed key do
        throwError "@[cites]: malformed citation key {key}\n\
          expected  stmt:<12 lowercase hex>:<local-label>\n\
          A chunk_id (arxiv:<paper>:<16hex>) is NOT a citation key: it rotates \
          on any parse change and has no alias table."
      let rel ←
        match r with
        | none => pure Relation.no_claim
        | some i =>
          match Relation.ofString? i.getId.toString with
          | some v => pure v
          | none   => throwError "@[cites]: unknown relation {i.getId}; expected one of \
                        exact|equivalent|specialization|one_way|no_claim"
      let front : Array String :=
        match fs with
        | none => #[]
        | some xs => xs.getElems.map (·.getString)
      let note : String := match nt with | none => "" | some s => s.getString
      if rel == .no_claim && note.isEmpty then
        throwError "@[cites]: relation := no_claim requires a `note` explaining \
          what relation, if any, is being asserted."
      if rel == .exact && !front.isEmpty then
        throwError "@[cites]: relation := exact is incompatible with a non-empty \
          frontier. An `exact` rendering has no undischarged assumptions."
      modifyEnv fun env =>
        citesExt.addEntry env
          { declName := decl, key := key, relationClaimed := rel,
            frontier := front, note := note }
    | _ => throwUnsupportedSyntax
  applicationTime := .afterCompilation
}

/-- Every `@[cites]` entry visible in the current environment (this module's
own plus everything imported). -/
def citesEntries (env : Environment) : Array CiteEntry :=
  citesExt.getState env ++ (citesExt.toEnvExtension.getState env).importedEntries.foldl
    (fun acc a => acc ++ a) #[]

/-- Dump command, mirroring `#stacks_tags`. -/
elab "#cites_dump" : command => do
  let env ← Lean.Elab.Command.liftCoreM Lean.getEnv
  for e in citesEntries env do
    logInfo m!"{e.declName}  ->  {e.key}  [{e.relationClaimed.toString}]"

end MathFormalContract
```

Usage in the topic repo:

```lean
@[cites "stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2"
        relation one_way
        frontier ["gltilde-universal-cover", "stability-vs-prestability"]
        note "Acts on PreStabilityCondition.WithClassMap, not StabilityCondition."]
instance preMulAction : MulAction GLTilde (PreStabilityCondition.WithClassMap C v) where
  …
```

## 2.3 `lean/MathFormalContract/Emit.lean` — the emitter

```lean
/-
The emitter.  It derives EVERYTHING from `Environment.constants` and
`Lean.collectAxioms`.  It NEVER PARSES SOURCE.

That is not a stylistic preference.  The audit reproduced, by executing them,
that arXMCP's `_DECL_SITE_RE` / `_DECL_NAME_RE` match NEITHER the site NOR the
name of the legal single-line forms

    set_option maxHeartbeats 400000 in theorem sneaky : False := bad
    open Classical in theorem sneaky : False := bad

leaving `complete = True` and emitting `outcome: "clean"`.  A source-parsing
extractor is defeated by declaration SYNTAX.  An environment sweep cannot be,
because it never sees syntax.

Scoping is BY MODULE, never by name prefix: a declaration at root namespace,
or under a foreign namespace, inside a topic module still lands in the .olean
and is importable downstream.  Prefix scoping misses it.
-/
import Lean
import MathFormalContract.Cites

namespace MathFormalContract

open Lean Elab Command Meta

private def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiom"   | .defnInfo _   => "def"
  | .thmInfo _    => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"    | .inductInfo _ => "inductive"
  | .ctorInfo _   => "ctor"    | .recInfo _    => "rec"

/-- Pretty-printer options pinned for digest stability.

`format.width` MUST be pinned: measured `type_pp` on this toolchain contains
HARD LINE BREAKS at the wrap width, e.g.

  "∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : …]\n  [inst_2 : …]"

so an unpinned width would rotate every digest.  `mfc` additionally
whitespace-normalizes before hashing, so this is belt AND braces. -/
private def ppOpts : Options :=
  ({} : Options)
    |>.setBool `pp.fullNames true
    |>.setBool `pp.universes true
    |>.setBool `pp.notation  true
    |>.setNat  `format.width 120

/-- Topic-local constants occurring in `e`.  "Topic-local" = declared in a
module of THIS library.  External constants contribute nothing to a statement
digest: `env_digest` already pins Mathlib and the anchor by commit. -/
private def localConstsIn (env : Environment) (mods : Std.HashSet Name)
    (e : Expr) : Array Name :=
  let used := e.getUsedConstants          -- UNVERIFIED name at v4.29.0; see 2.0
  let keep := used.filter fun n =>
    match env.getModuleIdxFor? n with
    | some i => mods.contains env.header.moduleNames[i.toNat]!
    | none   => false
  keep.qsort (fun a b => a.toString < b.toString) |>.eraseDups

/-- Emit the inventory.  Returns the number of `sorryAx`-carrying constants. -/
def emit (rootLib : Name) (outPath : System.FilePath) :
    CommandElabM Nat := do
  let env ← getEnv
  let allMods := env.header.moduleNames
  -- Module scope: the root module and everything under it.
  let inScopeMods : Std.HashSet Name :=
    allMods.foldl (init := {}) fun s m =>
      if m == rootLib || rootLib.isPrefixOf m then s.insert m else s
  if inScopeMods.isEmpty then
    throw <| .error (← getRef)
      m!"mfc-emit: root library {rootLib} matched ZERO modules. \
         An empty scope is the observable signature of a misconfigured \
         emitter and MUST NOT produce a passing artifact."
  let mut out    : Array Json := #[]
  let mut total  := 0
  let mut inScope := 0
  let mut internal := 0
  let mut withRange := 0
  let mut instances := 0
  let mut privateN := 0
  let mut sorryCount := 0
  let cites := citesEntries env
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := allMods[idx.toNat]!
    unless inScopeMods.contains modName do continue
    total := total + 1
    let axs ← liftCoreM <| collectAxioms n
    -- SORT: collectAxioms returns them UNSORTED.  Measured on this toolchain:
    -- ["propext","Quot.sound","Classical.choice"] on one declaration and
    -- ["Quot.sound","propext","Classical.choice"] on the very next.  Without
    -- this sort the emission is not byte-reproducible.
    let axsSorted := (axs.map (·.toString)).qsort (· < ·)
    if axsSorted.contains "sorryAx" then sorryCount := sorryCount + 1
    let rng ← liftCoreM <| findDeclarationRanges? n
    let isInt := n.isInternalDetail
    let isInst ← liftTermElabM (Meta.isInstance n)
    let isPriv := isPrivateName n
    if isInt then internal := internal + 1 else inScope := inScope + 1
    if rng.isSome then withRange := withRange + 1
    if isInst then instances := instances + 1
    if isPriv then privateN := privateN + 1
    let tyStr ← liftTermElabM <| withOptions (fun _ => ppOpts) do
      pure (toString (← PrettyPrinter.ppExpr ci.type))
    -- value_pp ONLY for def / opaque.  Folding a THEOREM's value into a
    -- statement digest would make every proof edit look like a statement
    -- change; folding a DEF's value in is the entire point (case ADV-4).
    let valStr : Option String ← match ci with
      | .defnInfo v   => liftTermElabM <| withOptions (fun _ => ppOpts) do
                           pure (some (toString (← PrettyPrinter.ppExpr v.value)))
      | .opaqueInfo v => liftTermElabM <| withOptions (fun _ => ppOpts) do
                           pure (some (toString (← PrettyPrinter.ppExpr v.value)))
      | _             => pure none
    let deps := localConstsIn env inScopeMods ci.type
    let deps := match ci with
      | .defnInfo v   => (deps ++ localConstsIn env inScopeMods v.value).qsort
                           (fun a b => a.toString < b.toString) |>.eraseDups
      | .opaqueInfo v => (deps ++ localConstsIn env inScopeMods v.value).qsort
                           (fun a b => a.toString < b.toString) |>.eraseDups
      | _ => deps
    let myCites := cites.filter (·.declName == n)
    out := out.push <| Json.mkObj [
      ("name",        Json.str n.toString),
      ("module",      Json.str modName.toString),
      ("kind",        Json.str (kindOf ci)),
      ("is_instance", Json.bool isInst),
      ("is_internal", Json.bool isInt),
      ("is_private",  Json.bool isPriv),
      ("is_reducible", Json.bool (← liftCoreM (isReducible n))),
      ("num_levels",  Json.num ci.levelParams.length),
      ("type_pp",     Json.str tyStr),
      ("value_pp",    match valStr with | some s => Json.str s | none => Json.null),
      ("local_deps",  Json.arr (deps.map (fun d => Json.str d.toString))),
      ("scc_members", Json.arr #[]),
      ("axioms",      Json.arr (axsSorted.map Json.str)),
      ("range",       match rng with
                      | some r => Json.mkObj [
                          ("startLine", Json.num r.range.pos.line),
                          ("startCol",  Json.num r.range.pos.column),
                          ("endLine",   Json.num r.range.endPos.line),
                          ("endCol",    Json.num r.range.endPos.column)]
                      | none => Json.null),
      ("cites", Json.arr (myCites.map fun c => Json.mkObj [
                  ("key",              Json.str c.key),
                  ("relation_claimed", Json.str c.relationClaimed.toString),
                  ("frontier",         Json.arr (c.frontier.map Json.str)),
                  ("note", if c.note.isEmpty then Json.null else Json.str c.note)]))]
  -- Deterministic ordering: env.constants iteration order is NOT specified.
  let out := out.qsort fun a b =>
    (a.getObjValD "name").getStr! < (b.getObjValD "name").getStr!
  let doc := Json.mkObj [
    ("schema_version",  Json.str "emission/1.0"),
    ("emitter_version", Json.str "mfc-emit/1.0.0"),
    ("lean_version",    Json.str Lean.versionString),
    ("lean_githash",    Json.str Lean.githash),
    ("lean_options",    Json.mkObj [("autoImplicit", Json.bool
                          ((← getOptions).getBool `autoImplicit true)),
                        ("relaxedAutoImplicit", Json.bool
                          ((← getOptions).getBool `relaxedAutoImplicit true))]),
    ("pp_options",      Json.mkObj [("pp.fullNames", Json.bool true),
                                    ("pp.universes", Json.bool true),
                                    ("pp.notation",  Json.bool true),
                                    ("format.width", Json.num 120)]),
    ("root_lib",        Json.str rootLib.toString),
    ("modules",         Json.arr ((inScopeMods.toArray.map (fun m => m.toString)).qsort (· < ·) |>.map Json.str)),
    ("counts", Json.mkObj [("total", Json.num total), ("in_scope", Json.num inScope),
                           ("internal", Json.num internal), ("with_range", Json.num withRange),
                           ("instances", Json.num instances), ("private", Json.num privateN)]),
    ("constants",  Json.arr out),
    ("emitted_at", Json.str (← IO.monoMsNow).repr)]   -- replaced by mfc; see 2.5
  IO.FS.writeFile outPath (doc.pretty ++ "\n")
  pure sorryCount

/-- The gate.  `lake env lean` exits 0 while `#print axioms` prints
`[sorryAx]` -- MEASURED on this toolchain -- and still exits 0 under
`-E hasSorry`.  So the sorry gate cannot ride on the default exit code and is
raised here as an elaboration error instead. -/
def emitMain (rootLib : Name) (outPath : System.FilePath) : CommandElabM Unit := do
  let n ← emit rootLib outPath
  if n != 0 then
    throw <| .error (← getRef) m!"mfc-emit: {n} constant(s) depend on sorryAx. \
      A sorry-backed declaration typechecks, gets imported, and launders an \
      unproved claim into everything downstream. Leave the result UNDECLARED \
      and mint a `kind: obligation` registry entry instead."

end MathFormalContract
```

## 2.4 The topic repo's three generated lines

`bridgeland-stab-lean/scripts/Emit.lean` — **the only Lean file copier renders**, so `copier update` never 3-way-merges 200 lines of metaprogram:

```lean
import BridgelandStabLean
import MathFormalContract.Emit

#eval MathFormalContract.emitMain
  (rootLib := `BridgelandStabLean)
  (outPath := "attest/lean-emission.json")
```

`bridgeland-stab-lean/lakefile.toml` gains:

```toml
[[require]]
name = "MathFormalContract"
git  = "https://github.com/chris-dare-dev/math-formal-contract"
rev  = "0000000000000000000000000000000000000000"   # exact 40-hex, never a branch
subDir = "lean"

# Fixes a structural gap independent of everything else: `scripts/` is
# currently covered by NO lean_lib, so `lake build` does not build
# scripts/Audit.lean and its own header admits it can silently rot.
[[lean_lib]]
name = "Scripts"
srcDir = "scripts"
```

## 2.5 The commands, in order

```bash
# 1. Build.  VERIFIED: exit 0, 42 bytes of stdout, no --json at Lake 5.0.0.
lake exe cache get && lake build

# 2. Emit.  This is the VERIFIED-REACHABLE shape (the ground-phase probe ran
#    exactly this way and produced byte-identical output across two runs).
#    --json gives NDJSON diagnostics whose `data` strings are UNWRAPPED, which
#    is what makes them parseable at all.
lake env lean --json scripts/Emit.lean > attest/lean.ndjson

# 3. Fold NDJSON -> build.json, emission -> declarations.json, and compute
#    every digest.  All digesting is Python-side, on BOTH sides of the seam,
#    which removes the cross-language digest-implementation problem entirely.
mfc bundle attest/

# 4. Validate.
mfc lint
mfc check-ilean-coverage    # set-diff .lake/build/lib/lean/**/*.ilean `decls`
                            # against constants[].name.  Two jobs at once:
                            # (a) catches a module covered by no lean_lib;
                            # (b) is the VACUOUS-PASS GUARD -- fails if
                            #     constants[] is empty or any .ilean decl is
                            #     missing.  `.ilean` is plain JSON that
                            #     `lake build` already writes, containing
                            #     EXACTLY the source-written declarations
                            #     (no _proof_N, no projections) -- VERIFIED:
                            #     60 across 7 modules at commit 62552e1.
mfc check-resolution        # resolution.json.registry_sha256 vs registry bytes
mfc conformance             # the vendored fixture corpus

# 5. Reproducibility gate.  VERIFIED achievable: byte-identical across runs.
lake env lean --json scripts/Emit.lean > /dev/null
mfc bundle attest/ --check-reproducible   # re-emits, diffs modulo {emitted_at}

# 6. No hand-edited bundle.
git diff --exit-code attest/
```

`emitted_at` is written by Lean as a monotonic clock value and **overwritten by `mfc bundle` with the CI run's `produced_at`** — this is why step 5 diffs "modulo `{emitted_at}`" and why the Lean side emits no wall-clock time.

## 2.6 What the Lean side **cannot** do today, stated plainly

1. **No SHA-256 in Lean core at v4.29.0.** Lake's `Hash` is a 64-bit non-cryptographic hash; the probe's `type_hash` was `hash (ci.type : Expr)`, a Lean-internal value (`312568070` on `relabel_P`) that is not portable across toolchains. **All contract digests are Python-side. `type_hash` appears in no contract artifact.**
2. **No cross-environment statement identity.** A pretty-printer change across a toolchain bump rotates every `statement_digest` at once. `statement_stable` is therefore **`not_applicable`** across environments, never `pass`. The **v1.1 hedge, deliberately deferred**: `mfc-emit --restate-check` re-elaborates the recorded `pp.all` string in the new environment and `isDefEq`s it against the current type, distinguishing pretty-printer drift from statement drift. Deferred because `elabTerm`/`isDefEq` availability and `pp.all` round-trippability at v4.29.0 are unverified.
3. **No exit-code sorry gate in the default path.** Measured: `lake env lean` exits 0 while printing `[sorryAx]`, and still exits 0 under `-E hasSorry` (which *does* relabel the message to `error:` in stdout — a genuine surprise). The gate is the emitter's own thrown error plus a `--json` scan for `severity == "error"`.
4. **`assert_no_sorry` is belt-and-braces, not the gate.** It is present at the pin (`.lake/packages/mathlib/Mathlib/Util/AssertNoSorry.lean`, `elab "assert_no_sorry " n:ident : command` → `Lean.collectAxioms`, errors on `` `sorryAx ``) and *does* fail elaboration, unlike `#print axioms`. But it is per-name and requires someone to remember to write it; the environment sweep does not.

---

# PART 3 — The arXMCP side

Every change is **offline CLI or read-only resource**. Zero writes from the MCP tool surface. Zero new tools — so `EXPECTED_TOOL_SCHEMA_SHA256` and the BP1 prompt-cache prefix are untouched, and that is *proved by a test*, not asserted.

## 3.0 Plan-track assignment

| Change | Track | Milestone |
|---|---|---|
| `tools/statement_resolve.py`, `Makefile: formal-resolve`, `tests/test_statement_resolve.py`, first CI | **`plans/formal-target-registry/`** (R5 — the track that must be *created*; it is brief-only today) | new **m0 · corpus-side statement resolver** |
| `tools/formal_release_pin.py`, `notebooks.db` v5→v6, `tools/notebook_restore.py` `user_version` fix | `plans/formal-target-registry/` | new **m1 · release pinning** |
| `server/formal_store.py`, two MCP resources, `tests/test_formal_resource.py` | `plans/formal-target-registry/` | new **m2 · serving surface** |
| `_DECL_SITE_RE`/`_DECL_NAME_RE` fix; ship frozen `lean_verify_result.json` as advertised `outputSchema`; `status:"ok"` → `elaborated_no_errors` | `plans/verification-contract/` (R3) | existing **m1**, lane `now`, one commit / one `TOOL_SCHEMA_VERSION` bump / one BP1 invalidation |
| `arxmcp://lean-env` naming `bridgeland-stab-lean@<tag>` alongside `bridgeland-anchor@<commit>` | `plans/verification-contract/` | existing **m5** |

**R5's entry gate says "R3 trust gate green."** m0 above deliberately does **not** depend on it: the resolver touches no Lean, so it can and should land first — the migration sequences it before any template work precisely so the identifier gamble resolves before the pattern is cloned.

## 3.1 `tools/statement_resolve.py` — NEW, offline, read-only, generic

```
python -m tools.statement_resolve \
    --notebook bridgeland-stability \
    --registry "C:/…/bridgeland-stab-lean/registry" \
    --out      "C:/…/bridgeland-stab-lean/attest/resolution.json"
```

Zero bytes mention Bridgeland. Contract:

```python
"""Resolve statement-registry entries against a notebook's live corpus.

READ-ONLY. Opens LanceDB read-only; writes exactly one file, OUTSIDE this
repo, at a path the operator names. Imports nothing from server/handlers/ and
registers no tool. This is an offline ingest-CLI-class program under
CLAUDE.md 4.8 rule 2.

arXMCP NEVER ISSUES IDENTITY. This program answers exactly one question:
  "does this registry entry's registered quote still appear in this notebook's
   corpus, and if so, in which chunk?"
It cannot mint a key, cannot alter a key, and cannot grant a trust axis.
"""
```

The resolution ladder, literally:

```python
def resolve_one(entry, key, tbl, chunk_index) -> dict:
    want = entry["quote_sha256"]
    if want is None:                       # obligation with no anchored quote
        return _r(key, "not_run", "none", reason="quote_sha256 is null")

    paper = entry["source"]["id"]
    if paper not in chunk_index.papers:
        return _r(key, "paper_absent", "none",
                  reason=f"no chunks for paper_id {paper} in this notebook")

    # RUNG 1 — the mint-time chunk_id, as a CACHE HINT ONLY.
    # We fetch it and RE-DERIVE the hash. A rotation invalidates the cache; it
    # can never corrupt the answer, because the id is never trusted.
    hint = (entry.get("mint_resolution") or {}).get("chunk_id")
    if hint:
        row = chunk_index.get(hint)
        if row is not None and _body_hash(row["body_text"]) == want:
            return _r(key, "current", "quote_sha256", chunk_id=hint,
                      matched_body_sha256=want,
                      printed_number=row.get("printed_number"))

    # RUNG 2 — scan this paper's chunks for the same normalized-text hash.
    # This is the `source_span.txt` mechanism that ingest/schema.py:240-250
    # calls "the authoritative resolving key (spike-3)" and that is 100% NULL
    # live (15280/15280) because ingest/store.py:598 writes it as literal None.
    # We compute it HERE, at resolve time, so the design does not wait on the
    # unshipped forward-wiring.
    for row in chunk_index.by_paper(paper):
        if _body_hash(row["body_text"]) == want:
            return _r(key, "current", "quote_sha256", chunk_id=row["chunk_id"],
                      matched_body_sha256=want,
                      printed_number=row.get("printed_number"))

    # RUNG 3 — printed_number. HINT ONLY, and it can never be `current`:
    # populated only on the ar5iv/LaTeXML path (36 of 66 chunks on this very
    # paper; NULL for kind in {proof-orphan, section}), and authors renumber
    # between arXiv versions.
    pn = entry["source"].get("printed_number")
    if pn:
        for row in chunk_index.by_paper(paper):
            if (row.get("printed_number") or "") == pn:
                return _r(key, "drifted", "printed_number",
                          chunk_id=row["chunk_id"],
                          matched_body_sha256=_body_hash(row["body_text"]),
                          printed_number=pn,
                          reason="text hash differs; matched only on the "
                                 "printed number, which is a hint")

    return _r(key, "unresolvable", "none",
              reason="registered quote hash matches no chunk of this paper, "
                     "and no chunk carries the registered printed number")


def _body_hash(body_text: str) -> str:
    """The SAME normalizer as mfc/digest.py::quote_sha256.
    Vendored from contract/mfc_digest.py at the pinned contract commit; the
    conformance corpus is what keeps the two in agreement."""
    import hashlib, unicodedata
    return hashlib.sha256(
        " ".join(unicodedata.normalize("NFC", body_text).split()).encode("utf-8")
    ).hexdigest()
```

**It never guesses.** There is no fuzzy/ANN rung at all in v1: `matched_by: "fuzzy"` exists in the schema so that a future rung is expressible, and the schema already forbids it from ever producing `current`.

`Makefile`:

```make
formal-resolve:  ## Resolve a statement registry against a notebook's corpus (READ-ONLY)
	@test -n "$(NOTEBOOK)" || (echo "usage: make formal-resolve NOTEBOOK=<slug> REGISTRY=<dir> OUT=<file>" && exit 2)
	$(PY) -m tools.statement_resolve --notebook $(NOTEBOOK) --registry "$(REGISTRY)" --out "$(OUT)"

formal-pin:      ## Pin a released formalization by GIT TAG (offline; re-derives every digest)
	@test -n "$(NOTEBOOK)" || (echo "usage: make formal-pin NOTEBOOK=<slug> REPO=<path-or-url> TAG=<tag>" && exit 2)
	$(PY) -m tools.formal_release_pin --notebook $(NOTEBOOK) --repo "$(REPO)" --tag "$(TAG)"
```

## 3.2 `tools/formal_release_pin.py` — NEW, offline

```python
"""Pin a RELEASED formalization: fetch by TAG, re-derive every digest from the
git tag object, validate against the vendored schemas, store in notebooks.db.

Five refusals, in order. Each is a test in tests/test_formal_release_pin.py.

R1. The ref MUST be an annotated or lightweight TAG that resolves to a commit.
    A branch or a bare SHA is refused. "The registry only pins RELEASES" is
    enforced here, and `git tag` in bridgeland-stab-lean is currently EMPTY --
    which is why the premise is presently false.

R2. The worktree MUST be clean and `environment.json.root_package.rev` MUST
    equal `git rev-parse <tag>^{commit}`.

R3. EVERY file digest in bundle.json is RE-DERIVED with
        git cat-file blob <tag>:<path>
    and sha256'd HERE. bundle.json's own claimed sha256 values are compared,
    never trusted. This is what makes the sorry gates survive the seam: a
    hand-edited attest/ tree that recomputed its own hashes still fails,
    because the pinner reads the git OBJECTS, not the working tree.

R4. `axiom_closure` is RECOMPUTED from declarations.json against
    environment.json.axiom_policy. Any `contains_sorry_ax: true` or non-empty
    `axioms_disallowed` refuses the pin outright.

R5. Any predicateType not in contract/predicate-types.json is moved to
    `unrecognized_predicates[]`, RECORDED, and NEVER served as evidence.

arXMCP MAY DOWNGRADE an axis (e.g. binding_resolves, from its own fresher
resolution run). arXMCP HAS NO CODE PATH THAT RAISES ONE. There is no function
in this module that writes `pass` into an axis it did not itself compute.
"""
```

Storage — `server/notebooks_store.py` v5 → **v6**, appended exactly per the documented recipe at `notebooks_store.py:60-67`, following the v4→v5 block's explicit `BEGIN`/`COMMIT` shape (the connection is `isolation_level=None`, so the transaction must be opened explicitly, and the block must be re-runnable after a crash between statements):

```python
#: v5→v6 is the formal-target-registry-m1 ADDITIVE migration adding two
#: tables that pin RELEASED formalizations and cache their per-statement
#: trust records. No existing table is dropped or altered. Both tables are
#: written ONLY by tools/formal_release_pin.py (offline CLI) and read
#: read-only by server/formal_store.py.
            if current_version < 6:
                conn.execute("BEGIN")
                try:
                    conn.execute("""
                        CREATE TABLE IF NOT EXISTS formal_releases (
                          notebook        TEXT NOT NULL,
                          repo_url        TEXT NOT NULL,
                          tag             TEXT NOT NULL,
                          commit_sha      TEXT NOT NULL,
                          env_digest      TEXT NOT NULL,
                          registry_id     TEXT NOT NULL,
                          registry_sha256 TEXT NOT NULL,
                          contract_rev    TEXT NOT NULL,
                          bundle_json     TEXT NOT NULL,
                          pinned_at       TEXT NOT NULL,
                          PRIMARY KEY (notebook, repo_url, tag)
                        )""")
                    conn.execute("""
                        CREATE TABLE IF NOT EXISTS formal_records (
                          notebook   TEXT NOT NULL,
                          repo_url   TEXT NOT NULL,
                          tag        TEXT NOT NULL,
                          key        TEXT NOT NULL,
                          record_json TEXT NOT NULL,   -- served-record/1.0
                          PRIMARY KEY (notebook, repo_url, tag, key),
                          FOREIGN KEY (notebook, repo_url, tag)
                            REFERENCES formal_releases(notebook, repo_url, tag)
                        )""")
                    conn.execute(
                        "CREATE INDEX IF NOT EXISTS idx_formal_records_key "
                        "ON formal_records(notebook, key)")
                    conn.execute("PRAGMA user_version = 6")
                    conn.execute("COMMIT")
                except Exception:
                    conn.execute("ROLLBACK")
                    raise
```

**In the same change**, `tools/notebook_restore.py` must be fixed: it writes the `notebooks` table by raw `sqlite3` at `:225,302,320` with **no `user_version` handling**, which re-arms the v0→v1 unconditional DROP. Adding two tables it does not know about makes that hazard strictly worse, so the fix is not deferrable.

## 3.3 `server/formal_store.py` — NEW, read-only

```python
"""Read-only accessor over formal_releases / formal_records.

Opens the SAME notebooks.db with `mode=ro` in the URI, mirroring
server/corpus_manifest.py's pattern -- a `resources/read` is an
unauthenticated MCP call and must be structurally incapable of writing.

Exposes exactly two coroutines:
    list_records(notebook) -> {release, count, keys[]}
    get_record(notebook, key) -> served-record/1.0 dict | None
No filtering logic beyond `required_axes`, which is FAIL-CLOSED: a caller
asking for faithfulness=adequate gets NOTHING for an unreviewed entry, never a
downgraded record. `not_run` and `not_applicable` never satisfy a required
axis, and neither is ever coerced to `pass`.
"""
```

## 3.4 `server/mcp_resources.py` — two new resources, zero new tools

Appended inside `register_resources(mcp_server)`, after `register_all_tools`, before `mount_mcp` — the same snapshot-at-mount constraint the three existing resources are under:

```python
FORMAL_INDEX_TEMPLATE_URI  = "arxmcp://formal/{notebook}"
FORMAL_RECORD_TEMPLATE_URI = "arxmcp://formal/{notebook}/{key}"

    @mcp_server.resource(
        FORMAL_INDEX_TEMPLATE_URI,
        name="formal-index",
        description=(
            "Pinned formal-target records for one notebook: the released Lean "
            "artifact (repo, tag, commit, env_digest) and the statement keys it "
            "binds. resources/read returns {release, count, keys, caveats}. "
            "Read-only; the record is produced by the Lean repo's CI and pinned "
            "verbatim -- this server produces no elaboration or axiom evidence "
            "and cannot raise a trust axis."),
        mime_type="text/plain",
    )
    async def _formal_index(notebook: str) -> str:
        validate_slug(notebook)            # FIRST call: an unauthenticated MCP
                                           # read treats the slug as hostile.
        return _wrap_json(await formal_store.list_records(notebook),
                          kind="formal_record")

    @mcp_server.resource(
        FORMAL_RECORD_TEMPLATE_URI,
        name="formal-record",
        description=(
            "One statement's multi-axis trust record. Seven axes, each "
            "pass|fail|not_run|not_applicable, each with its own evidence, "
            "env_digest, timestamp and self_attested flag. There is NO "
            "aggregate status field: no axis may be inferred from another. "
            "The FIRST key is `caveats` and it is generated, not authored. "
            "`relation_claimed` is the author's claim; `relation_confirmed` "
            "appears only when a named human has reviewed it on a stated date."),
        mime_type="text/plain",
    )
    async def _formal_record(notebook: str, key: str) -> str:
        validate_slug(notebook)
        return _wrap_json(await formal_store.get_record(notebook, key),
                          kind="formal_record")
```

`server/tools.py::wrap_retrieved_text` gains the `formal_record` kind → `<retrieved_formal_record>`. **No `ToolMeta` entry, no `inputSchema` byte changes, no new tool.** The three existing guard tests (`tests/test_mcp_resources.py::test_tools_list_hash_unchanged_with_resources`, `::test_resources_do_not_change_tools_vs_baseline`, `::test_resources_add_no_tools`) must stay green **with no re-pin of `EXPECTED_TOOL_SCHEMA_SHA256`** — that is the mechanical proof of the zero-BP1 claim, and it is a *test*, not a paragraph.

## 3.5 What arXMCP is forbidden from doing, structurally

* **Cannot produce axes 1–4.** It has no Lean at v4.29.0. Its REPL is v4.31.0 from a detached-HEAD directory outside the repo. `server/formal_store.py` renders any axis whose `env_digest` differs from the record's environment as **`not_applicable`** — never `pass`, never `fail`. This converts the toolchain skew from a silent soundness hole into a value in the type system.
* **`lean_verify` output can never satisfy an axis.** If cited at all it enters as `predicateType: .../provisional-self-reported/v1`, which `contract/predicate-types.json` maps to the empty axis set.
* **Cannot mint or alter a key.** No arXMCP module writes `registry/`.
* **Cannot serve without axes.** `served-record-1.0.schema.json` requires all seven axis objects present; a record missing one fails validation at pin time and is not stored.

---

# PART 4 — The conformance suite

**Bowtie / JSON-Schema-Test-Suite model.** The corpus lives in `math-formal-contract/testdata/`, in **neither implementation**, in a language-neutral format. Both siblings vendor it at a pinned commit (`contract.lock`) and run `mfc conformance` locally. Neither can drift the tests toward its own behavior; neither needs the other running.

Fixture layout:

```
testdata/
  valid/<case>/          input.{json,yaml} + expect.json  {"outcome":"accept"}
  invalid/<case>/        input.{json,yaml} + expect.json  {"outcome":"reject",
                                                           "rule":"E-01",
                                                           "must_contain":"sorryAx"}
  render/<case>/         inputs/ + expect-record.json     (served-record composition)
  lean/<case>/           a REAL minimal Lake project + expect.json
```

`mfc conformance` walks every case and asserts the outcome exactly. `expect.json` never says "an error" — it names the **rule id**, so a fixture cannot be satisfied by the wrong rejection.

## 4.1 The four required adversarial cases

### ADV-1 · `testdata/lean/set-option-evasion/` — the `set_option … in theorem` fail-open

**This fixture is not JSON.** It is a real, minimal Lake project, compiled by the contract repo's own Lean CI matrix. A JSON fixture here would pass by construction and test nothing.

`testdata/lean/set-option-evasion/lakefile.toml`:
```toml
name = "EvasionProbe"
defaultTargets = ["EvasionProbe"]
[[require]]
name = "MathFormalContract"
path = "../../../lean"
[[lean_lib]]
name = "EvasionProbe"
```

`testdata/lean/set-option-evasion/EvasionProbe.lean`:
```lean
import MathFormalContract.Cites

namespace EvasionProbe

theorem good : True := trivial

-- FORM A: the audit reproduced by EXECUTING arXMCP's regexes that
-- `_DECL_SITE_RE` / `_DECL_NAME_RE` match NEITHER the site NOR the name here,
-- returning (['good'], True) -- `complete` stays True, this declaration is
-- never `#print axioms`-ed, and the record emits `outcome: "clean"`.
set_option maxHeartbeats 400000 in
theorem sneaky_a : False := by sorry

-- FORM B: same evasion, different prefix.
open Classical in
theorem sneaky_b : False := by sorry

end EvasionProbe

-- FORM C: ROOT NAMESPACE, inside a topic module. A PREFIX-scoped emitter
-- (`ourPrefix.isPrefixOf n`, which is what the ground-phase probe used) misses
-- this entirely, yet it lands in the .olean and is importable downstream.
-- This is why the shipped emitter scopes BY MODULE.
theorem sneaky_c : False := by sorry
```

`expect.json`:
```json
{ "outcome": "reject",
  "rule": "E-01",
  "emitter_exit_nonzero": true,
  "emission_must_list": ["EvasionProbe.sneaky_a", "EvasionProbe.sneaky_b", "sneaky_c"],
  "emission_axioms_must_contain": { "EvasionProbe.sneaky_a": "sorryAx",
                                    "EvasionProbe.sneaky_b": "sorryAx",
                                    "sneaky_c": "sorryAx" },
  "must_contain": "depend on sorryAx",
  "note": "Three assertions, not one. (1) mfc-emit exits non-zero. (2) All THREE hidden declarations appear in constants[] -- an environment sweep cannot be evaded by declaration syntax, because it never parses syntax. (3) sneaky_c specifically proves module scoping beats prefix scoping." }
```

Runner: `mfc conformance --lean` builds the project, runs the emitter, asserts all three. **A green run of this fixture is the only evidence that the sorry gate is real.**

### ADV-2 · `testdata/invalid/foreign-env-attestation/` — toolchain skew

`input.json` (a `bundle/1.0` + `served-record` composition input):
```json
{ "subject_env_digest": "52b407ea4c1e8c51bfefe1d9a1f173e142729c6abf09a750a383869d5b160349",
  "predicates": [
    { "predicateType": ".../predicate/declarations/v1",
      "file": "attest/declarations.json", "sha256": "aa…aa",
      "produced_by": "arxmcp/lean_verify",
      "produced_at": "2026-08-04T08:59:00Z",
      "env_digest": "9c17e0b3ffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
      "self_attested": true } ] }
```
`expect.json`:
```json
{ "outcome": "reject", "rule": "B-03",
  "must_contain": "env_digest does not match the subject environment",
  "note": "arXMCP's REPL is v4.31.0 from a detached-HEAD directory OUTSIDE the repo; the pin is v4.29.0. An `ok` from it is not evidence about THIS environment. A declarations/v1 predicate carrying a foreign env_digest is REJECTED at pin time, and if it is instead admitted under the reserved `provisional-self-reported/v1` type it satisfies ZERO axes." }
```

Companion `testdata/render/foreign-env-review/` asserts the *rendering* half: a `review.yaml` whose `reviewed_env_digest` differs from the current `env_digest` must render `statement_stable: not_applicable` **and** `faithfulness: not_applicable`, never `pass`, never `fail`, with the caveat string `"the review on file was made against a different environment digest and does not carry over."`

### ADV-3 · `testdata/render/chunk-id-rotation/` — the identifier scheme's whole point

Executed as `arXMCP/tests/test_statement_resolve.py` against a synthetic 3-chunk LanceDB fixture (no network, no models, no real corpus):

```python
def test_rotation_preserves_resolution(tmp_path):
    """Rotate EVERY chunk_id and assert every entry still resolves `current`.

    `make ingest-recover-preambles` help text: "NOTE: triggers chunk_id
    rotation; follow with make re-embed-all." Rotation is a routine FIRST-PARTY
    operation. There is no alias table, no previous_chunk_id column, and
    merge_insert has no delete arm -- so rotation DOUBLES rather than fails.

    This single test is what proves the identifier scheme works."""
    tbl = build_fixture_chunks(tmp_path, n=3)
    reg = mint_registry_from(tbl, keys=3)          # mint_resolution captures ids
    r0 = resolve(reg, tbl)
    assert [x["resolution"] for x in r0["results"]] == ["current"] * 3
    assert {x["matched_by"] for x in r0["results"]} == {"quote_sha256"}

    # Rotate: perturb ONLY whitespace + preamble_text. chunk_id =
    # sha256(preamble_text + NFC(body_text))[:16] rotates; quote_sha256 under
    # nfc-ws-collapse/1 does NOT.
    tbl2 = rotate_all_chunk_ids(tbl, whitespace_only=True)
    assert set(ids(tbl2)).isdisjoint(set(ids(tbl)))   # every id really changed

    r1 = resolve(reg, tbl2)
    assert [x["resolution"] for x in r1["results"]] == ["current"] * 3
    assert {x["matched_by"] for x in r1["results"]} == {"quote_sha256"}
    assert [x["chunk_id"] for x in r1["results"]] == ids(tbl2)   # cache refreshed
    # AND: not one byte of the registry changed.
    assert registry_sha256(reg) == r0["registry_sha256"] == r1["registry_sha256"]

def test_removed_statement_is_unresolvable_never_a_wrong_match(tmp_path):
    """A genuinely removed statement must yield `unresolvable`. It must NEVER
    silently re-point at the nearest surviving chunk. Dense ANN retrieval makes
    a wrong match the DEFAULT failure mode; the resolver has no fuzzy rung."""
    tbl = build_fixture_chunks(tmp_path, n=3)
    reg = mint_registry_from(tbl, keys=3)
    tbl2 = delete_chunk(tbl, index=1)
    r = resolve(reg, tbl2)
    assert r["results"][1]["resolution"] == "unresolvable"
    assert r["results"][1]["chunk_id"] is None
    assert r["results"][1]["matched_by"] == "none"

def test_printed_number_only_match_is_drifted_never_current(tmp_path):
    """Author edits the statement TEXT but keeps the number 8.2."""
    tbl = build_fixture_chunks(tmp_path, n=3)
    reg = mint_registry_from(tbl, keys=3)
    tbl2 = edit_body_text(tbl, index=0, keep_printed_number=True)
    r = resolve(reg, tbl2)
    assert r["results"][0]["resolution"] == "drifted"
    assert r["results"][0]["matched_by"] == "printed_number"
```

Language-neutral fixture form for `mfc conformance`: `testdata/render/chunk-id-rotation/{registry.yaml, chunks-before.json, chunks-after.json, expect.json}`.

### ADV-4 · `testdata/invalid/same-name-different-statement/` — the drift the audit called undetectable

The dangerous case, and the one that lands in the exact file CLAUDE.md §3 exists to protect.

`inputs/declarations-before.json`:
```json
{ "declarations": [
  { "name": "BridgelandStabLean.Lattice.NumLattice", "kind": "def",
    "type_pp": "Type", "value_pp": "Fin 2 → ℤ", "local_deps": [],
    "statement_digest": "c44dc5545999699041be0421a8767f82c45ae16d38a736db3dbf532a3d6a1acf" },
  { "name": "BridgelandStabLean.Lattice.finrank_numLattice", "kind": "theorem",
    "type_pp": "Module.finrank ℤ BridgelandStabLean.Lattice.NumLattice = 2",
    "value_pp": null, "local_deps": ["BridgelandStabLean.Lattice.NumLattice"],
    "statement_digest": "bee014f3f5e761cfe1e329560ab0c5f26ebf3c6c24be8c85bcfed64b7cf72af2" } ] }
```

`inputs/declarations-after.json` — **the `abbrev` body is edited to `Fin 3 → ℤ`; the theorem's own `type_pp` is byte-identical**:
```json
{ "declarations": [
  { "name": "BridgelandStabLean.Lattice.NumLattice", "kind": "def",
    "type_pp": "Type", "value_pp": "Fin 3 → ℤ", "local_deps": [],
    "statement_digest": "5864ab81e0687a3560108ace1827f23e7f4771cc6ae165fc88102cd05f654644" },
  { "name": "BridgelandStabLean.Lattice.finrank_numLattice", "kind": "theorem",
    "type_pp": "Module.finrank ℤ BridgelandStabLean.Lattice.NumLattice = 2",
    "value_pp": null, "local_deps": ["BridgelandStabLean.Lattice.NumLattice"],
    "statement_digest": "483199562962637025b958ccadbe289692d4d15692a9dc9082367780a5ef3a90" } ] }
```

`inputs/review.yaml` pins `reviewed_statement_digest: "bee014f3f5e761cfe1e329560ab0c5f26ebf3c6c24be8c85bcfed64b7cf72af2"`.

`expect.json`:
```json
{ "outcome": "reject",
  "rule": "D-04",
  "axes": { "statement_stable": "fail", "faithfulness": "not_applicable" },
  "must_contain": "statement_digest differs from reviewed_statement_digest",
  "note": "A TYPE-ONLY digest of `finrank_numLattice` is BYTE-IDENTICAL before and after -- and `NumLattice`'s OWN type_pp is the string \"Type\" in both. Both facts are MEASURED on the real toolchain, not stipulated. Only the Merkle fold over local_deps, which pulls a def's value_pp into every dependent theorem's digest, detects it. This is exactly the audit's gap #8, landing in Lattice/NumericalK.lean -- the file CLAUDE.md section 3 exists to protect." }
```

**All four digests above are [COMPUTED]** and reproducible:

```
NumLattice          (Fin 2 → ℤ)  c44dc5545999699041be0421a8767f82c45ae16d38a736db3dbf532a3d6a1acf
finrank_numLattice               bee014f3f5e761cfe1e329560ab0c5f26ebf3c6c24be8c85bcfed64b7cf72af2
NumLattice'         (Fin 3 → ℤ)  5864ab81e0687a3560108ace1827f23e7f4771cc6ae165fc88102cd05f654644
finrank_numLattice'              483199562962637025b958ccadbe289692d4d15692a9dc9082367780a5ef3a90
                                 -> theorem digest CHANGED: True
```

## 4.2 The remaining fixture corpus

| Case | Rule | What it reproduces |
|---|---|---|
| `invalid/sorry-laundered` | `D-01` | `contains_sorry_ax: false` while `axioms` contains `sorryAx` — the two must agree, both directions |
| `invalid/axiom-injected` | `E-03` | `axioms: ["myAxiom"]` with `axioms_disallowed: []` — `mfc` **recomputes** and rejects |
| `invalid/local-axiom-undeclared` | `E-02` | a `kind: "axiom"` constant absent from `axiom_policy.additions[]` |
| `invalid/env-digest-mismatch` | `B-02` | `declarations.json.env_digest` ≠ `environment.json.env_digest` |
| `invalid/stale-review` | `D-04` | review's `reviewed_quote_sha256` ≠ registry's `quote_sha256` (paper-side staleness, independent of Lean-side) |
| `invalid/unknown-key` | `E-04` | `@[cites]` key with no registry entry |
| `invalid/key-is-chunk-id-shaped` | `R-06` | key `arxiv:math/0212237:a82c3230040fd724` — must be rejected as a citation key |
| `invalid/source-arxiv-unversioned` | `R-01` | `scheme: arxiv` with `version: null` / `"v?"` / `""` |
| **`invalid/aggregate-status`** | `S-01` | a record with `"status": "verified"` — rejected by `additionalProperties: false`. **This is the fixture that turns the trust-language policy from a review habit into a machine constraint.** |
| `invalid/axis-without-evidence` | `A-01` | `"faithfulness": {"value": "pass"}` with `evidence: {}` |
| **`invalid/not-run-as-pass`** | `A-02` | a consumer that treats `not_run` or `not_applicable` as satisfying `required_axes` — run against **both** `mfc` and arXMCP's `formal_store.list_records(required_axes=…)` |
| `invalid/empty-emission` | `E-08` | `constants: []`, `counts.in_scope: 0` — **the vacuous-pass guard**; a mis-set root lib yields exactly this and must not be a green build |
| `invalid/relation-exact-with-frontier` | `E-05` | `relation_claimed: exact` with a non-empty frontier |
| `invalid/resolution-current-without-body-digest` | `RS-01` | `resolution: current` with `matched_body_sha256: null` |
| `invalid/resolution-fuzzy-current` | `RS-02` | `matched_by: fuzzy` with `resolution: current` |
| `invalid/unsorted-axioms` | `E-10` | breaks byte-reproducibility |
| `invalid/elided-type-pp` | `E-07` | `type_pp` containing `⋯` — two different statements could hash identically |
| `invalid/closed-lane-breach` | `E-09` | a constant in a module under `Mathlib.AlgebraicGeometry.` — "the geometric lane is closed" as a build failure |
| `valid/textbook-source` | — | `scheme: textbook`, `id: "textbook:iwaniec-kowalski"`, `version: null`, `printed_number: null`, `quote_mode: digest_only`. **MUST validate.** arXMCP ships `textbook:<slug>` ids today (`ingest/identifiers.py`, live notebooks `bridgeland-stability-pdfs`, `fourier-duality-pdfs`); a grammar that cannot express them is disqualified. |
| `valid/obligation-entry` | — | `kind: obligation`, `decls: []`, `mint_resolution: null`. **MUST validate.** The undeclared-with-a-TODO rule, made navigable. |
| `valid/minimal-release` | — | the smallest complete bundle: 1 entry, 1 decl, all seven axes present, five of them `not_run` |

## 4.3 The two CI workflows

`bridgeland-stab-lean/.github/workflows/contract.yml` — **the first CI in this repo's history**:

```yaml
name: contract
on: [push, pull_request]
jobs:
  producer:
    runs-on: ubuntu-24.04
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@<40-hex>
        id: lean
        with:
          build: true
          use-mathlib-cache: true
          # UNVERIFIED that these three inputs exist -- see PART 2.0. If they
          # do not, the `kernel_replay` axis ships `not_run` and nothing counts
          # it. nanoda-allow-sorry DEFAULTS TO TRUE; leaving it would add a
          # check that PASSES ON SORRY-BACKED PROOFS.
          leanchecker: true
          nanoda: true
          nanoda-allow-sorry: false
      # lean-action has NO aggregate `status` output -- only per-axis
      # build-status / test-status / lint-status / nanoda-status, each
      # SUCCESS|FAILURE|"" where "" means DID NOT RUN. That three-valued
      # per-axis shape is section 4.9 already shipping in the ecosystem.
      - run: pipx install "git+https://github.com/chris-dare-dev/math-formal-contract@$(cat contract.lock)"
      - run: lake env lean --json scripts/Emit.lean > attest/lean.ndjson
      - run: mfc bundle attest/
              --lean-status "${{ steps.lean.outputs.build-status }}"
              --checker-status "${{ steps.lean.outputs.nanoda-status }}"
      - run: mfc lint
      - run: mfc check-ilean-coverage
      - run: mfc check-resolution
      - run: mfc conformance
      - run: mfc bundle attest/ --check-reproducible
      - run: git diff --exit-code attest/
```

`arXMCP/.github/workflows/ci.yml` — **the first CI in that repo's history**, deliberately cheap (no LanceDB, no Lean, no models, no network):

```yaml
name: ci
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-24.04
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-python@v5
        with: { python-version: "3.11" }
      - run: pip install -e ".[dev]"
      - run: pytest -q                       # existing suite
      - run: pipx install "git+https://github.com/chris-dare-dev/math-formal-contract@$(cat contract.lock)"
      - run: mfc conformance --corpus contract/testdata
      - run: pytest -q tests/test_statement_resolve.py
      - run: pytest -q tests/test_formal_release_pin.py
      - run: pytest -q tests/test_formal_resource.py
```

`tests/test_formal_release_pin.py::test_tampered_bundle_is_refused` — the one that proves the gates survive the seam:

```python
def test_tampered_bundle_is_refused(git_repo_with_tag):
    """Flip contains_sorry_ax to false, RECOMPUTE the file's sha256, write it
    into bundle.json so the bundle is SELF-CONSISTENT -- and assert the pinner
    still refuses, because it re-derives every digest from
    `git cat-file blob <tag>:attest/declarations.json`, not from the worktree."""
    tamper(git_repo_with_tag, "attest/declarations.json",
           lambda d: set_field(d, "contains_sorry_ax", False))
    rehash_bundle(git_repo_with_tag)          # bundle.json now internally consistent
    with pytest.raises(PinRefused, match="R3: file digest differs from git object"):
        pin_release(notebook="t", repo=git_repo_with_tag, tag="v0.1.0")
```

`tests/test_formal_resource.py::test_tool_schema_hash_unchanged`:

```python
def test_tool_schema_hash_unchanged():
    """Mechanically prove the zero-BP1 claim: registering two new RESOURCES
    must not move EXPECTED_TOOL_SCHEMA_SHA256. If this fails, the change added
    a TOOL, and a tool costs a deliberate re-pin
    (pytest --update-tool-schema-hash + a hand-edited EXPECTED_BP1_SHA256)."""
    app = create_app()
    assert serialize_tools(app) == EXPECTED_TOOL_SCHEMA_SHA256
```

## 4.4 The cross-repo integration job

One job, in the **contract** repo, crossing no network boundary between the siblings:

```yaml
  integration:
    runs-on: ubuntu-24.04
    steps:
      - uses: actions/checkout@v4                                   # contract
      - uses: actions/checkout@v4
        with: { repository: chris-dare-dev/bridgeland-stab-lean, ref: <pinned sha>, path: lean }
      - uses: actions/checkout@v4
        with: { repository: chris-dare-dev/arXMCP, ref: <pinned sha>, path: corpus }
      - run: pip install -e .
      # `mfc join` is a PURE FUNCTION of two directories of JSON. No server, no
      # port, no auth, no version handshake. That is the cold seam.
      - run: mfc join --lean lean/attest --registry lean/registry --resolution lean/attest/resolution.json --out /tmp/records.json
      - run: mfc validate --schema served-record/1.0 /tmp/records.json
```

---

# PART 5 — Worked end-to-end trace

**Bridgeland 2007, §8, Lemma 8.2 → an LLM agent's query.** Seven hops. Every value is either measured on this machine, computed here, or explicitly marked unfilled.

---

### HOP 1 — Paper

```
Tom Bridgeland, "Stability conditions on triangulated categories"
arXiv:math/0212237 , section 8, printed as "Lemma 8.2"
```

**Blocked field, deliberately:** the arXiv **version** is unknown. `documents.db` in the live `bridgeland-stability` notebook records `arxiv_version = ''` for this paper. The unversioned form resolves to arXiv's *latest* and therefore silently drifts. Every artifact below carries `version: "v?"`, and **`mfc lint` rule `R-01` refuses to let a release ship with it**. This must be settled by opening the abstract page, not inferred.

---

### HOP 2 — Corpus (arXMCP, read-only)

```
notebook            : bridgeland-stability
corpus_version      : 5048              (LanceDB MVCC integer — recorded, never trusted)
chunk_id            : arxiv:math/0212237:a82c3230040fd724
printed_number      : "8.2"
preamble_ref        : NULL   -> preamble_text = ""  -> chunk_id = sha256(NFC(body_text))[:16]
source_span         : NULL   (100% NULL corpus-wide: ingest/store.py:598 writes literal None)
source_revision_id  : NULL   (98.96% NULL corpus-wide)
theorem_name        : NULL   (100% NULL for this paper)
theorem_label       : NULL
```

The `chunk_id` was **independently recomputed and confirmed by the audit**. It is nonetheless used **only as a cache hint** from here on.

---

### HOP 3 — Registry node (`bridgeland-stab-lean/registry/bridgeland2007.yaml`)

A human runs:

```bash
mfc registry mint \
  --notebook bridgeland-stability \
  --from-chunk arxiv:math/0212237:a82c3230040fd724 \
  --paper arxiv:math/0212237 --version v? \
  --printed-number 8.2 --kind lemma --label bridgeland2007.lem-8.2
```

which prefills `quote` from `get_chunk`, computes `quote_sha256`, records `mint_resolution`, and then **stops and prints**:

```
MINTED  stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2
  quote prefilled from arxiv:math/0212237:a82c3230040fd724 (matched_by=quote_sha256)
  ACTION REQUIRED, by a human, before this entry may enter a release:
    1. Open arxiv.org/abs/math/0212237v<N> and CONFIRM the quote character by
       character. A corpus parse is not a paper.
    2. Replace source.version "v?" with the confirmed version. `mfc lint` will
       refuse the literal "v?".
    3. Write `informal` in your own words.
    4. Write `frontier[]`. It may be empty; it MUST be present.
```

Resulting node (fields as in §1.1a). The key is:

```
stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2
```

**Zero corpus-derived bytes.** Not `chunk_id`, not `corpus_version`, not `parse_artifact_sha256`, not the notebook slug. `make ingest-recover-preambles`, a chunker bump, an ar5iv re-render, a LaTeXML upgrade, an HTML→MinerU migration — none can invalidate a string they never contributed to.

`quote_sha256 = ebacfe5caa6c1df8229ec6bfbcf55f855a524a77cf78a9fb3171b81172d6f50d` **[COMPUTED]** — a real hash of the literal placeholder `PLACEHOLDER-QUOTE-NOT-YET-MINTED`. The arXMCP server was not running while this specification was authored, and fabricating a verbatim quote from a paper is precisely the failure this contract exists to prevent.

---

### HOP 4 — Lean declaration

`BridgelandStabLean/GroupAction/PreStabilityAction.lean:90`:

```lean
@[cites "stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2"
        relation one_way
        frontier ["gltilde-universal-cover", "stability-vs-prestability"]
        note "Acts on PreStabilityCondition.WithClassMap, not StabilityCondition. \
              Step 3c is blocked on an anchor-side local-finiteness restriction lemma."]
instance preMulAction : MulAction GLTilde (PreStabilityCondition.WithClassMap C v) where
  one_smul := …
  mul_smul := …
```

**The binding fails loudly, and that is the design working.** `relation_claimed: exact` is unavailable: rule `E-05` rejects `exact` with a non-empty frontier, and the entry has two open frontier items. `GLTilde`'s *name* asserts a universal cover the repo has not proved — the projection is not shown surjective, the fibre is not shown to be ℤ, simple connectedness is not addressed. The strongest honest claim is `one_way`.

`lake env lean --json scripts/Emit.lean` produces `attest/lean-emission.json` containing the `preMulAction` constant with `cites[0].relation_claimed = "one_way"`, its full sorted axiom closure `["Classical.choice","Quot.sound","propext"]`, its `local_deps = ["…GLTilde","…actPre"]`, and its range `L90–L109`.

---

### HOP 5 — arXMCP resolution (independent evidence)

```bash
make formal-resolve NOTEBOOK=bridgeland-stability \
     REGISTRY="…/bridgeland-stab-lean/registry" \
     OUT="…/bridgeland-stab-lean/attest/resolution.json"
```

Ladder rung 1 hits: `mint_resolution.chunk_id` fetches, the body is re-normalized and re-hashed, the hash matches.

```json
{ "key": "stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2",
  "resolution": "current",
  "matched_by": "quote_sha256",
  "chunk_id": "arxiv:math/0212237:a82c3230040fd724",
  "matched_body_sha256": "ebacfe5caa6c1df8229ec6bfbcf55f855a524a77cf78a9fb3171b81172d6f50d",
  "printed_number": "8.2", "similarity": null, "reason": null }
```

The file is committed **into the Lean repo**, carrying `registry_sha256`. From now on, editing the registry without re-running the resolver turns the Lean repo's CI red — one comparison, no clocks, no network.

---

### HOP 6 — Trust record (produced by Lean-repo CI, pinned by arXMCP)

```bash
# Lean repo CI
mfc bundle attest/ && mfc lint && git diff --exit-code attest/
git tag v0.1.0    # the first release in this repo's history

# arXMCP, offline
make formal-pin NOTEBOOK=bridgeland-stability \
     REPO="https://github.com/chris-dare-dev/bridgeland-stab-lean" TAG=v0.1.0
```

Axis values at first release:

| Axis | value | why |
|---|---|---|
| `elaborates` | **pass** | `lake_build_exit: 0`, `error_count: 0` |
| `kernel_replay` | **not_run** | `leanchecker`/`nanoda` availability unverified; not silently counted |
| `axiom_closure` | **pass** | observed `{Classical.choice, Quot.sound, propext}` = allowlist; `disallowed: []`; `contains_sorry_ax: false` |
| `statement_stable` | **not_applicable** | no review on file → no baseline to be stable against |
| `binding_resolves` | **pass** | arXMCP resolver, `self_attested: false` — the one axis with independent evidence |
| `frontier_discharged` | **fail** | two open items |
| `faithfulness` | **not_run** | absent from `review.yaml`; distinct from every present value |

Stored in `formal_releases` + `formal_records` (notebooks.db v6), written by the offline pinner, read by `server/formal_store.py` over a `mode=ro` connection.

---

### HOP 7 — An LLM agent reads it

```
resources/read  arxmcp://formal/bridgeland-stability/stmt:9f4c1a20b7d3:bridgeland2007.lem-8.2
```

Returns the payload of §1.9, wrapped `<retrieved_formal_record>…</retrieved_formal_record>`. **The first thing the model tokenizes is:**

```
"caveats": [
  "faithfulness: not_run — no human has compared this Lean statement to the paper. Typecheck is not fidelity.",
  "frontier: 2 undischarged items (gltilde-universal-cover, stability-vs-prestability) — this is a theorem about the interface, not yet about the object.",
  "relation_claimed: one_way — this is the AUTHOR'S claim about the binding strength. No reviewer has confirmed it.",
  "axiom_closure: pass — this says nothing about whether the statement is the paper's.",
  "kernel_replay: not_run — no independent checker result is on file for this release."
]
```

Then `axes`, then evidence, then `bindings` with `relation_claimed: "one_way"` and `relation_confirmed: null`, then `assumption_frontier`, then the permalink `…/blob/f166a3d…/BridgelandStabLean/GroupAction/PreStabilityAction.lean#L90-L109`.

**Four mechanical defences against over-reading, all active in this payload:**
1. No aggregate field exists — `additionalProperties: false` means the producer could not have added one.
2. `relation_claimed`, never `relation_confirmed`, in machine artifacts.
3. `caveats[]` first, generated by `mfc/caveats.py`, so it cannot drift from the axis values.
4. `required_axes` filtering is fail-closed: an agent asking `get formal targets where faithfulness=adequate` gets **nothing** for this entry, never a downgraded record.

---

### The three events the design is built to survive

**(a) A re-ingest rotates every `chunk_id`.** The key is unchanged. `statement_resolve.py` finds `a82c3230040fd724` gone, scans the paper, matches `quote_sha256` against the new chunk, writes `resolution: current, matched_by: quote_sha256, chunk_id: <new>, matched_body_sha256: ebacfe5c…`. The Lean repo commits the new `resolution.json`. **No Lean source changes, no key changes, no review goes stale, no axis moves.**

**(b) A LaTeXML upgrade rewrites the rendered text.** `resolution: drifted`. `mfc check-resolution` reddens the Lean repo's CI. A human adjudicates: the render changed (re-mint the quote; new entry with `supersedes`) or the paper changed (new arXiv version; new key). **Loud, not silent.**

**(c) `abbrev NumLattice` is redefined.** `local_deps` puts `NumLattice`'s digest inside every dependent theorem's `statement_digest`; the digest changes from `bee014f3…` to `483199…` **even though the theorem's own `type_pp` is byte-identical** [COMPUTED]; `statement_stable` flips to `fail` against `reviewed_statement_digest`; `faithfulness` renders `stale`; the caveat fires. A type-only digest — the obvious design — misses this entirely, in the one file CLAUDE.md §3 exists to protect.

---

### The honest limit, stated in the served record itself

A matching `statement_digest` means **unchanged since a human looked**. It never means **faithful to the paper**. No digest can detect that `Fin 2 → ℤ` was described as a Kuznetsov component; only a human reading both can. TheoremGraph's 22/24-typecheck versus 5/24-faithful is the reference gap, and `faithfulness` is the only axis that closes it — human-only, dated, named, never computed, never defaulted, and deliberately without an `agent_drafted` sub-state.

---

## Files this deliverable specifies, by repo (absolute paths)

**New repo `math-formal-contract`** — `contract.version`, `mfc/{digest,version,bundle,lint,registry,conformance,join,caveats,init}.py`, `schema/{registry,emission,environment,declarations,review,build,bundle,resolution,served-record}-1.0.schema.json`, `contract/predicate-types.json`, `lean/lakefile.toml`, `lean/MathFormalContract/{Cites,Emit}.lean`, `testdata/{valid,invalid,render,lean}/`, `template/` (copier), `migrations/`.

**`C:/Users/cedar/Documents/Personal Projects/Source Code/bridgeland-stab-lean/`** — new: `registry/bridgeland2007.yaml`, `attest/{environment,declarations,build,bundle,resolution}.json`, `attest/review.yaml`, `attest/lean-emission.json` (gitignored), `scripts/Emit.lean`, `contract.lock`, `contract/` (vendored), `.github/workflows/contract.yml`. Edited: `lakefile.toml` (add `[[require]] MathFormalContract` + `[[lean_lib]] Scripts`), `formalization.yaml` (`source.id` gains `v<n>`; delete the false "mirrors the anchor key-for-key" comment — seven shared keys differ in type and the anchor's first key `schema_version` is absent), `CLAUDE.md §8`.

**`C:/Users/cedar/Documents/Personal Projects/Source Code/arXMCP/`** — new: `tools/statement_resolve.py`, `tools/formal_release_pin.py`, `server/formal_store.py`, `tests/test_statement_resolve.py`, `tests/test_formal_release_pin.py`, `tests/test_formal_resource.py`, `.github/workflows/ci.yml`, `contract.lock`, `contract/` (vendored), `plans/formal-target-registry/roadmap.yaml`. Edited: `server/notebooks_store.py` (v5→v6 block + `SCHEMA_VERSION = 6`), `server/mcp_resources.py` (two resources), `server/tools.py` (`wrap_retrieved_text` kind `formal_record`), `tools/notebook_restore.py` (`user_version` handling), `Makefile` (`formal-resolve`, `formal-pin`), `AGENTS.md` (mirror §4.8/§4.9 — it has neither, and is untracked).

## Explicit uncertainties

1. **arXiv version of `math/0212237` is unknown on this machine** (`documents.db` records `arxiv_version = ''`). Written as `v?` throughout and refused by `mfc lint`.
2. **The verbatim `quote` is unfilled.** The arXMCP server was not running; the recorded `quote_sha256` is a real hash of a labelled placeholder.
3. **`@[cites]` attribute code is not compiled.** Modelled on `Mathlib/Tactic/StacksAttribute.lean` (verified present at the pin); syntax elaboration and `.olean` round-tripping need one build to confirm.
4. **`Expr.getUsedConstants` name at v4.29.0 is unverified.** `#check @Lean.Expr.getUsedConstants` settles it; the shape of `localConstsIn` does not otherwise change.
5. **`lean-action`'s `leanchecker` / `nanoda` / `nanoda-allow-sorry` inputs are unverified.** If absent, `kernel_replay` ships `not_run` and nothing counts it.
6. **The option name that disables pretty-printer elision is unverified.** Rule `E-07` (reject any `type_pp` containing `⋯`/`…`/`...`) is the guard that does not depend on knowing it.
7. **`[[lean_exe]] mfc-emit` via `importModules` is unverified.** The `lake env lean scripts/Emit.lean` path *is* verified, and CI uses it.
8. **The third-repo recommendation contradicts a recorded verdict** (`_pipeline/stage-1-discovery/synthesis/target-architecture.md:113-126`, "NOT NOW — create on trigger", contracts custody assigned to `math-research-orchestrator`). The schemas and fixtures above are byte-identical whether they live in `math-formal-contract/` or `arXMCP/contract/`; only the vendoring path in `contract.lock` changes.