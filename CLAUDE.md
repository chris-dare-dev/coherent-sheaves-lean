# CLAUDE.md — context for agents working in BridgelandStabLean

Read `README.md` first for the mathematical framing. GitHub milestones and issues hold the
current theorem inventory and dependencies. This file contains the working rules.

## 1. The pins are load-bearing

- `lean-toolchain` is `leanprover/lean4:v4.29.0`.
- `lakefile.toml` pins `BridgelandStability` to commit `9e48f23a382…` — an
  **exact commit, never a branch**.
- Mathlib (`8a178386ffc0…`) arrives **transitively** through the foundational library.
  Do not add a direct Mathlib `require`. A second pin is a second thing to
  drift, and the point of this repo is a citable, reproducible environment.

Bumping any pin is a deliberate act with a `formalization.yaml` update in the
same commit. Never bump one to make a build error go away.

### Named exceptions to the one-pin rule

Exactly one, and it is listed here so a second one cannot be added quietly.

**`MathFormalContract`** — the `@[cites]` attribute and the evidence emitter,
a `[[require]]` at an exact commit. Decided in
[`ADR-0008`](.claude/decisions/ADR-0008-cites-is-a-shared-lake-dependency.md).

Vendoring it is not an option rather than a worse option: `@[cites]` is a
`SimplePersistentEnvExtension`, and **duplicate attribute registration is an
import-time error**, so two vendored topic repos could never coexist in one
Lean environment.

The exception is bounded by the property that justifies it — **the package is a
leaf with zero transitive dependencies**, core Lean only, no Mathlib and no
foundational library. It cannot drag anything else in and cannot disagree with the foundational library
about a Mathlib revision. **If that ever stops being true, the exception
lapses** and the dependency comes out; it is not grandfathered.

Everything else in §1 applies to it unchanged: exact commit, never a branch,
bumped deliberately with a `formalization.yaml` update in the same commit.

Do **not** add a `[[require]]` on arXMCP to get this package. That repo's
`CLAUDE.md` §4.10 states the relationship is *"Sibling, never a subdirectory,
never a dependency"*, and a Lake require would make that false.

### Bumping the Mathlib pin: check `ForMathlib/` first

`BridgelandStabLean/ForMathlib/` holds results **Mathlib does not have at the
pin**. Every file in it is a shadow of something that may land upstream, so a
pin bump is the moment each one can become a duplicate.

Before bumping, for each file in `ForMathlib/`: check whether the upstream
version now exists, and if it does, **delete the local file in the same
commit** rather than keeping both. Two copies of `Matrix.polarFactor` in one
environment is an ambiguous name at best and a silent divergence at worst — and
the divergence is not hypothetical, see below.

Do **not** "sync" a local file from its upstream counterpart. They are written
against different Mathlib generations and the differences are real, not
cosmetic. Delete and use upstream, or keep the local one and don't bump.

Current contents:

| file | upstream | status |
|---|---|---|
| `PolarDecomposition.lean` | [mathlib4#42449](https://github.com/leanprover-community/mathlib4/pull/42449) | **closed, not merged** — keep. A maintainer is upstreaming a *more general* version (not matrix-specific); delete this file only once that lands **and is in the pin**. Do not pre-emptively delete on the strength of the promise — see below. |

**Do not treat "a maintainer has code for this" as a delivery date.** #42449 is
the *second* matrix polar decomposition closed this way. The first,
[mathlib4#33642](https://github.com/leanprover-community/mathlib4/pull/33642),
was closed by a different maintainer in January 2026 with the same reasoning
and the same offer — *"I have code for this somewhere"* — and as of August 2026
nothing general had landed; #42449's reviewer then said the same thing again,
adding *"I haven't had time to clean it up and upstream it yet."* Two people,
seven months apart, both holding unupstreamed work. That is not bad faith, it
is what volunteer capacity looks like, and the checklist above must not stall
waiting for it. The deletion condition is a `lake build` against the new pin
resolving `Matrix.polarFactor` (or its general replacement) from Mathlib — a
command, not a citation.

Two lessons from #42449 being closed, recorded so they are not repeated.
**Ask on Zulip before writing an upstream PR** — check not only whether Mathlib
*has* a result but whether anyone is *working* on it, and whether the
generality is right. The reviewer's point was that polar decomposition is not
matrix-specific, which the file's own implementation note had already
half-stated: the proof uses `CFC.sqrt_mul_sqrt_self` and nothing about
matrices. **And run the environment linters, not just `lake build` and
`lake exe lint-style`** — CI rejected an `@[simp]` on
`polarUnitary_mul_polarFactor` via `simpNF`, which neither local check runs.

The two versions already differ, which is the point of the rule. The upstream version is
in master's **module system** (`module` / `public import` /
`@[expose] public section`, none of which exist at v4.29.0) and needs
`Matrix.star_eq_conjTranspose` spelled out, because `star` on matrices no
longer simp-normalises to `ᴴ` there. Neither change can be back-ported to the
pin, and neither local form is valid upstream.

## 2. No `sorry`. Absent beats sorry-backed.

`fidelity.sorry_count` is `0` and should stay there.

When a result is not yet proved, **do not declare it with `sorry`** — leave it
undeclared and write the intent in a `TODO` comment. `StabilityCondition/Phase/NormalizedShift.lean`
demonstrates the pattern: the `Group` instance is described precisely and not
declared. A sorry-backed instance typechecks, gets imported, and silently
launders an unproved claim into everything downstream.

## 3. Never conflate the lattice model with geometry

`Lattice/Numerical/RankTwo.lean` uses `Fin 2 → ℤ` as a stand-in for `K_num(Ku(X))`.

A lemma proved there is a theorem about **any rank-2 torsion-free lattice**.
It is not a theorem about a Kuznetsov component, a surface, or any geometric
object. The identification requires `D^b(Coh X)`, which Mathlib does not have.

Do not name a declaration in a way that implies otherwise. Do not write
doc-comments claiming a geometric consequence. If a statement needs the
identification, it belongs in the assumption frontier, not in a proof.

## 4. The geometric lane is closed

Do not start work requiring coherent sheaves on a scheme, `D^b(Coh X)`, Serre
duality, Chern characters, HRR, numerical Grothendieck groups of varieties,
semiorthogonal decompositions, or Fourier–Mukai transforms. None exist in
Mathlib at the pinned commit. Building them is a multi-year Mathlib program,
not a task in this repo.

If a proposed target needs any of them, say so and stop rather than
axiomatizing the gap.

## 5. Order of work in lane 1 (§8)

1. ~~`Group` instance on `NormalizedShift`.~~ **Done** (2026-08-03) — via
   `toOrderIso_injective` + the `@[ext]` lemma `ext'`. Note `ext'`, not `ext`:
   Lean auto-generates `NormalizedShift.ext` for the structure, so the
   pointwise lemma needs a distinct name.
2. ~~Pair with `T ∈ GL⁺(2, ℝ)` under the shared-map-on-`S¹` condition.~~
   **Done** (2026-08-03) — `GLTilde`. The `Group` instance must be
   `noncomputable`: `GLPos` membership is a `0 < det` condition and `ℝ`'s
   `LinearOrder` is noncomputable. Invert via group multiplication
   (`inv_mul_cancel` on `GLPos`), never via `Matrix.inv` — the nonsingular
   inverse then never has to appear.
3. The action on stability conditions. **Read
   [`notes/dependencies/BridgelandStabilityAPI.md`](notes/dependencies/BridgelandStabilityAPI.md) first** — it maps every
   foundational library type this step touches, straight from the pinned checkout, and
   stages it 3a / 3b / 3c.
   - **3a — action on `Slicing`. Done** (2026-08-03),
     `StabilityCondition/Symmetry/GLTilde/Action/Slicing.lean`.
   - **3b — action on `PreStabilityCondition.WithClassMap`. Done**
     (2026-08-03), `StabilityCondition/Symmetry/GLTilde/Action/PreStability.lean` + `actC` in
     `StabilityCondition/Symmetry/GLTilde/ComplexRepresentation.lean`.
   - **3c — action on `StabilityCondition.WithClassMap`. Done** (2026-08-03),
     `StabilityCondition/Symmetry/GLTilde/Action/Stability.lean`. **The §8 `G̃L⁺(2, ℝ)` action is
     complete.**

   The topological track is also complete in the 2026-08-06 working tree.
   `StabilityCondition/Symmetry/GLTilde/Covering/SourceTopology.lean` supplies contractible global coordinates and simple
   connectedness; `StabilityCondition/Symmetry/GLTilde/Covering/Map.lean` proves the surjective covering-map
   property; and `StabilityCondition/Symmetry/GLTilde/Topology/Group.lean` proves continuous
   multiplication and inversion. `StabilityCondition/Symmetry/Combined/Topology.lean` and
   `StabilityCondition/Symmetry/GLTilde/Action/Continuous.lean` prove that fixed autoequivalence classes,
   fixed lifted matrices, and fixed pairs act by homeomorphisms on the
   Bridgeland stability space (`ContinuousConstSMul`).
   `StabilityCondition/Symmetry/GLTilde/Action/JointContinuous.lean` proves the stronger `ContinuousSMul`
   instances for `GLTilde`, for discretely topologized `AutPairQuot v`, and
   for their direct product. The algebraic `ℤ` fibre and exact sequence
   remain in `StabilityCondition/Symmetry/GLTilde/Covering/Fibre.lean` and `StabilityCondition/Symmetry/GLTilde/Covering/Surjectivity.lean`.

   The three post-topology symmetry milestones are complete as well.
   `StabilityCondition/Symmetry/Combined/Components.lean` transports connected components and restricts
   symmetries to component homeomorphisms; `StabilityCondition/Symmetry/Combined/PeriodMap.lean`
   proves equivariance of the central charge and the canonical component
   local-model chart; and `StabilityCondition/Symmetry/Combined/Effective.lean` quotients the combined
   symmetry group by its full action kernel. The shift convention is now
   theorem-pinned: `[2]` acts as `deck (-1)`, hence `(deck 1, [2])` is in the
   kernel. The quotient action is faithful. Do not strengthen this to a claim
   that the explicit diagonal pair generates the full kernel.

   The `Aut` groundwork is in `StabilityCondition/Symmetry/Autoequivalence/Slicing/Transport.lean`
   (`PostnikovTower.mapF`, `HNFiltration.mapF`, `Slicing.mapEquiv`). Two
   packagings of it exist **on slicings only** — the stability-condition action
   is `StabilityCondition/Symmetry/Autoequivalence/Stability/ClassMap.lean`, below:

   - `StabilityCondition/Symmetry/Autoequivalence/Slicing/Quotient.lean` — **the general one.** `AutQuot C` is
     triangulated auto-equivalences modulo natural isomorphism, a genuine
     `Group` with `MulAction (AutQuot C) (Slicing C)`. Excludes nothing.
     Prefer this. Note `AutQuot` is a plain `def`, so use `AutQuot.mk` — a
     bare `Quotient.mk` leaves `•` unable to find its instance.
   - `StabilityCondition/Symmetry/Autoequivalence/Slicing/Strict.lean` — the cheap special case, a group
     mapping *strictly* into `C ⥤ C`. Its `map_one`/`map_mul` are equalities
     of functors, so each `F g` is an **isomorphism of categories** and Serre
     functors and spherical twists are out of its scope.

   **`StabilityCondition/Symmetry/Autoequivalence/Stability/Transport.lean` now carries the action on stability
   conditions** (`actStabAut`, 2026-08-04) — `Φ` moves objects, a class-lattice
   datum `lam` carries it on `Λ`. Local finiteness survives with the **same
   `η`** (`mapEquiv_isLocallyFinite`); the endpoints do not move, so no
   `exists_radius`.

   **`StabilityCondition/Symmetry/Autoequivalence/Stability/ClassMap.lean` makes it a `MulAction`** (2026-08-04,
   later). The acting object is a *pair* `(Φ, lam)`, which `AutQuot` cannot
   group because it carries only the `Φ`s; `AutPair v` bundles both and
   `AutPairQuot v` is the quotient by natural isomorphism of `Φ` **with `lam`
   fixed on the nose**. Quotienting `lam` too would be wrong: two `lam`s over
   one `Φ` give genuinely different `σ.Z ∘ lam` whenever `v` is not surjective.

   Two consequences worth carrying:

   - **`lam` must be an `AddEquiv`, not an `AddMonoidHom`.** A group needs
     `lam⁻¹` and nothing produces one, since `v` is arbitrary. `actStabAut`
     still takes a bare `→+` and still applies to non-invertible data — that
     map is strictly more general than the group action.
   - The inverse's `compat` is the only place `Φ` being an *equivalence*
     matters: `unitIso` gives `Φ.functor ⋙ Φ.inverse ≅ 𝟭 C`, and
     `K₀.mapF_congr` promotes that isomorphism to an **equality** of maps on
     `K₀`. Without that upgrade `compat` cannot cross to `Φ⁻¹`.

   All three prerequisites are done: `K₀` functoriality (`StabilityCondition/Symmetry/Autoequivalence/Foundations/GrothendieckGroup.lean`), the
   class-lattice datum, and strict finite length under an *equivalence* of
   interval categories (`mapEquiv_isLocallyFinite`, on the general
   `isStrictArtinian_of_faithful_strict` in `StabilityCondition/Symmetry/Autoequivalence/Foundations/FiniteLength.lean` — the
   foundational library's `interval_thinFiniteLength_of_inclusion_strict` does **not** apply
   here, since it compares two `intervalProp`s on the same object).
   [`notes/dependencies/BridgelandStabilityAPI.md`](notes/dependencies/BridgelandStabilityAPI.md) §7.

   Facts worth having up front:

   - A non-`module` file imports the foundational library fine — no migration needed.
   - The foundational library is **not** covered by `lake exe cache get`; it is built now,
     keep it that way.
   - Inside a `MulAction` instance's own elaboration `•` is opaque, so `simp`
     needs a `show` to see through it.
   - The foundational library's `ext` lemmas live in `StabilityCondition/Basic.lean`, not
     `Defs.lean`. The auto-generated structure `ext` is useless — it demands
     equality of the `compat'` proofs.
   - On `ℂ`, `smul_smul` will not match `m • r • z` (different instance
     paths). Convert out with `Complex.real_smul`, then `push_cast; ring`.
   - **`Deformation/` is not only deformation theory.** It carries general
     interval-category infrastructure that `IntervalCategory/` does not — the
     whole `interval_*_of_inclusion_strict` family lives in
     `Deformation/IntervalSelection.lean`. Searching only `IntervalCategory/`
     and `QuasiAbelian/` once produced a false "the foundational library lacks this" finding.
     **Search the whole foundational library before concluding something is missing.**

Six claims to keep off the page.

- **"The formalized §8 symmetries are the full symmetry group"** — both halves
  act on stability conditions, `StabilityCondition/Symmetry/Combined/Action.lean` proves that they commute,
  and the direct product acts jointly continuously. What is *not* formalized
  is that these factors generate all symmetries. The `AutPairQuot v` factor is
  equipped with the discrete topology for this statement; no moduli topology
  on autoequivalences is being asserted.
- **"`Aut(D)` acts by isometries"** — still not literally the theorem proved
  here. `StabilityCondition/Metric/Mass/Basic.lean` defines the finite HN-factor mass sum
  and a choice-free `stabilityMass` envelope. `StabilityCondition/Metric/Mass/Uniqueness.lean` proves
  equality of all HN mass sums by head--tail octahedral induction and
  t-structure uniqueness, so the envelope equals every finite filtration mass
  and is never `⊤`. `StabilityCondition/Metric/Distance/Basic.lean` adds the ordinary logarithmic
  discrepancy to `φ⁺` and `φ⁻`, proving reflexivity, symmetry, the triangle
  inequality, and `slicingDist ≤ stabilityDist`. `StabilityCondition/Metric/Isometry/Full.lean` proves
  exact preservation by `AutPair` representatives and `AutPairQuot v`.
  `StabilityCondition/Metric/Distance/Separation.lean` proves that distance zero identifies the
  slicing and `Z.comp v`, hence the full stability condition when `v` is
  surjective; the ordinary `K₀ C` specialization is unconditional.

  `StabilityCondition/Metric/Distance/Topology.lean` proves the analytic charge/mass estimates,
  the full-distance-to-Section-6 cofinality direction, and the reverse
  direction conditional on the explicit proposition
  `StabilityMassTriangleInequality`. Its named `PseudoEMetricSpace` and
  `EMetricSpace` constructors go through `ofEDistOfTopology`, with regression
  theorems showing the inherited topology is definitionally the existing one;
  do not replace them with a raw global metric instance. Proposition 8.1
  remains `no_claim` until the mass-triangle proposition is discharged.
  Independently, `AutPairQuot v` carries a compatible lattice automorphism and
  is not identified with bare `Aut(D)`. Say "the compatible
  autoequivalence group preserves the three-coordinate HN-mass distance" and
  state the remaining group-level distinction.

  `StabilityCondition/Metric/Mass/Subadditivity/Triangle.lean` develops the missing categorical proof. It
  defines the ordinary observable condition by composing the central charge
  with `v`, reuses the heart-equivalence HN API, proves `‖Z(E)‖ ≤ mσ(E)`,
  proves mass invariance under `[1]` and `[-1]`, and closes the
  semistable-middle and same-phase-endpoint cases, including their heart
  short-exact forms. `HNFiltration.exists_headTail_mass` exposes a public
  head--tail mass split, and
  `stabilityMassTriangleInequality_of_semistable_obj₁` closes the
  arbitrary-left octahedral reduction conditional only on the semistable-left
  milestone. `StabilityCondition/Metric/Mass/Subadditivity/HNPolygon.lean` now defines the convex hull of all subobject
  charges, builds the distinguished HN path, proves edge-charge and
  length-equals-mass formulas, and supplies the endpoint chord inequality.
  `StabilityCondition/Metric/Mass/Subadditivity/CohomologyExactness.lean` proves that the heart-source `H⁰` complex is exact
  exactly when its canonical cokernel comparison is monic, and now proves the
  canonical `H⁰'` and `H⁰` functors homological unconditionally.
  `StabilityMassBoundaryHeartInequality` and
  `StabilityMassSemistableLeftTriangleInequality` are both inhabited. The
  second proof factors the six-term cohomology sequence into short exact
  pieces, proves the `(0, 2]` amplitude case, removes the lower and upper tails
  by exact HN cutoffs, and rotates an arbitrary semistable phase to one. The
  arbitrary-left reduction is also proved, but its final application has not
  yet been exposed as the named unconditional global triangle theorem.
  `StabilityMassHeartShortExactInequality` is a named uninhabited proposition,
  pending that global corollary.

  Two things this cost that are worth reusing. The foundational library had carried
  `slicingDist` since before this repo existed
  (`StabilityCondition/Defs.lean`), written for §7's deformation theory and
  never connected to §8 — the *third* time the "search the whole foundational library" rule
  above has paid. And `Slicing.phiPlus_congr` / `phiMinus_congr`,
  iso-invariance of the intrinsic phases, had to be stated here: the foundational library
  inlines that argument at four sites in `Deformation/DeformedGtLe.lean`
  without ever naming it.
- **"`AutPairQuot v` is `Aut(D)`"** — no, and it is further from it than
  `AutQuot` is. Its elements are *pairs*, and the forgetful map to `AutQuot C`
  is proved to be neither injective (different `lam` over one `Φ`, whenever `v`
  is not surjective) nor surjective (a `Φ` with no compatible `lam` has no
  preimage). Both failures are about `v`, which is arbitrary. Say "the group of
  autoequivalences carrying a compatible class-lattice automorphism".
- **"`GLTilde.universalCoverData` is a bundled Mathlib universal-cover
  object"** — no. Mathlib has no such bundled predicate at this pin. The
  theorem explicitly packages `IsCoveringMap GLTilde.mat`, surjectivity, and
  `SimplyConnectedSpace GLTilde`; `exact_deckHom_toMatHom` separately records
  the `ℤ` deck group. `GLTilde.isTopologicalGroup` supplies the group-topology
  compatibility. Cite those exact declarations rather than implying a larger
  bundled API.
- **"`AutPairQuot v` is just `Aut(D)` with notation changed"** — no. The
  autoequivalence relation itself is now the standard forward-functor natural
  isomorphism relation; inverse isomorphisms follow from right-adjoint
  uniqueness. But `AutPairQuot v` additionally carries `lam : Λ ≃+ Λ` and its
  compatibility with `v`, so it remains a different group from bare
  autoequivalences.
- **"The deck/double-shift overlap is the whole action kernel"** — not proved.
  `EffectiveCombinedSymmetry v` is deliberately the quotient by the full
  kernel of the permutation action, and `(deck 1, [2])` is proved to belong to
  it. Additional category-specific symmetries may act trivially. The theorem
  also fixes the sign convention: `[2] = deck (-1)` as actions, so the
  trivial diagonal representative is `(deck 1, [2])`.

Related: do not cite `StrictAut` as the `Aut` action either. Its `F g` are
isomorphisms of categories, not equivalences, so Serre functors and spherical
twists are outside it. `QuotAutAction` supersedes it for slicings.

Step 3 is the first declaration here that touches the foundational library's API. **Read
`BridgelandStability/Slicing/` and `BridgelandStability/StabilityCondition/`
end to end before attempting it.** Guessing at that API and iterating against
compile errors wastes a full Mathlib rebuild per guess.

## 6. `formalization.yaml` is a claim, not decoration

Its schema mirrors the foundational library's key-for-key so one parser reads both. Keep it
that way; do not rename keys.

Every field is a claim someone may cite. `human_review: none` stays `none`
until a human actually reviews. `builds_clean` is `pending` until a clean
build is observed, and carries the date when it is. Fields that cannot be
filled honestly say `none` or `pending` — never a flattering guess.

## 7. Build

```bash
lake exe cache get && lake build
```

`lake exe cache get` pulls prebuilt Mathlib oleans. Skipping it means
compiling Mathlib from source — hours, not minutes.

## 8. Relationship to arXMCP

Sibling repo, never a subdirectory. Never a `require`, never a submodule.
Nothing here imports anything from it, and nothing here runs while it does.

arXMCP is a local-first, loopback-only, **read-only** retrieval server over a
LanceDB corpus of parsed arXiv papers, organized into per-topic notebooks. The
`bridgeland-stability` notebook is the corpus behind this repo's sources.

### Three things this section used to assert that are false

Kept, because the corrections are the useful part.

- **Its R5 track does not pin released formalizations or serve trust records.**
  R5 is a brief with no `plans/` entry; `get_formal_targets` / `formal_targets`
  return zero hits in `server/`; and `find -iname "*formaliz*"` across arXMCP
  returns zero files. There is no parser.
- **arXMCP's `CLAUDE.md` §4.8 does not forbid hosting formalization work.** Its
  three rules are: the server never runs agents; writes enter only via offline
  ingest CLIs or operator-gated `/ui/` actions; the orchestrator loop lives in
  a separate repo. The prohibition on hosting formalization is in
  `.claude/roadmap-briefs/R5-formal-target-registry.md` — an unroadmapped
  brief, topic-scoped to geometry. Cite the brief, not §4.8.
- **`formalization.yaml` is not "the entire interface."** It has no reader, on
  either side.

### The rules that do bind

1. arXMCP is a read-only data plane. Nothing here may ask it to write, to run
   an agent, or to hold formalization source.
2. **An arXMCP Lean verdict is not evidence about this environment.** Its REPL
   runs v4.31.0 from a directory outside that repo; we pin v4.29.0. Its axiom
   audit fails open on `set_option … in theorem` and on `open … in theorem`.
   Do not quote a `lean_verify` result here as if it were a build result.
3. **No bare "verified."** arXMCP's §4.9 forbids any single token collapsing
   distinct trust questions, and no axis may be inferred from another. That
   binds anything this repo publishes for it to serve — see §2, which is the
   same rule pointed the other way.

### The contract that replaces the prose

Designed 2026-08-03; **not yet built.** A cold seam of versioned files
exchanged at git tags, with statement identity minted *here* and containing
zero corpus-derived bytes. Read [`.claude/decisions/`](.claude/decisions/) in
numeric order before touching anything that crosses the boundary — the ADRs
are short and they are the whole design. Work is tracked in
[`.claude/roadmap/contract-v1.yaml`](.claude/roadmap/contract-v1.yaml) and on
the GitHub issue tracker.

Until it ships the boundary is **unilateral**: arXMCP contains zero documents
mentioning this repo. Do not write text here that assumes otherwise, and do
not describe the contract in the present tense.
