# Fourier–Mukai lane — review and continuation handoff

**Audience:** a working session (autonomous or interactive) picking up the
Fourier–Mukai lane. Not a human summary.
**Baseline:** `origin/main` at `f4996a2` (merge of #530). Everything below
assumes that commit or later.
**Prior records:** round-1 and round-2 reviews plus the post-review handoff in
`.claude/reviews/2026-08-15-*`, `2026-08-16-*`. Read them before touching lane
files — they are why several designs look the way they do. This document
supersedes the 2026-08-16 handoff's work menu, not its mechanics.

## 0. Mechanics (unchanged, still non-negotiable)

```bash
cd /Users/chris.dare/Personal/SourceCode/derived-alg-geo-lean
git fetch origin
git worktree add -b agent/<branch> /tmp/<dir> origin/main
cp -c -R .lake /tmp/<dir>/.lake     # APFS clone, ~30s
cd /tmp/<dir> && lake build && scripts/gates.sh
```

- **Never work in the shared checkout.** Other sessions switch branches in it.
- **Gates are the definition of done:** 17 gates, `all gates passed (full)`.
- **Post-session ceilings: AlgebraicGeometry 1098, StabilityCondition 375,
  DGCategory 0.** SC moved 381 → 380 → 375 across this session; see §4.
- **Two registration points for a new module, not one.** The library umbrella
  *and* `scripts/StabilityConditionAudit.lean`'s own `import` list (near line
  136). Nothing points at the second until the audit fails with
  `Unknown constant`, and the surfaced error message misattributes it to
  truncation. This cost a debugging cycle; it will cost the next one too.
- **`gh pr merge --auto` does not update `BEHIND` branches here.** Branch
  protection requires up-to-date branches and auto-merge will sit forever. Run
  `gh pr update-branch <n>` each time `main` moves. Concurrent SF-track sessions
  merge continuously — `main` moved a dozen-plus times during this session — so
  automate the nudge or expect to babysit.
- **The audit file is a single append-point** and conflicts structurally with
  every concurrent PR (#480, still open). Both conflicts hit this session were
  pure append collisions: delete the three markers, keep both sides.

## 1. What changed this session

Nine PRs merged. The lane moved from *"a kernel functor transports a stability
condition, conditional on named data"* to a state where the entire **categorical**
side is constructed and the **geometric** gap is enumerated.

| PR | |
|---|---|
| #492 | `toAutPair` — kernel autoequivalences are elements of `AutPairQuot`; `UnitKernelData`, `KernelAutoequivalence.id` |
| #497 | `AdditiveMukaiData`, `mukaiForm`, `isometryOfPreservesEuler` — the Mukai isometry |
| #500 | `QuasiAbelian`/`ExtensionClosure` relocated out of `StabilityCondition/` (#488) |
| #501 | `K₀.mapF` retired for the generic `K₀.map` (#487); ratchet 381 → 380 |
| #505 | `ShiftSequence ℤ` for the `k`-linear Yoneda (#469); `LinearOpposite.lean` |
| #513 | `HomFiniteBounded`, `chiHom`, `chiK₀` — the Hom-built Euler form |
| #527 | `chiK₀_map`, `ofLinear_preservesCategoricalEuler` — preservation |
| #530 | `KernelCorrespondence.lean`, `KernelConvolution.lean` — two geometric ledgers |
| #494 | gate `/tmp` collision fix (spun off from a task chip) |

Three claims the review records explicitly denied are now theorems; one supplied
datum was retired; two false docstring claims were corrected.

## 2. File map — what is new

**Euler-form track** (all `CategoryTheory/Triangulated/`):

| file | content |
|---|---|
| `LinearOpposite.lean` | `Linear R Cᵒᵖ`, `Functor.op_linear`, `shiftFunctorOppositeLinear`, the two `ShiftedHom` `smul` lemmas. `ForMathlib` pattern — filed in place, audited under the existing `## ForMathlib` heading |
| `LinearYoneda.lean` | `linearYonedaShiftSequence` + three `homologySequence_exact` lemmas (first variable) |
| `LinearCoyoneda.lean` | same for the **second** variable; shift sequence is `tautological` |
| `GrothendieckGroup/EulerForm.lean` | `HomFiniteBounded`, `chiHom`, additivity both variables, `chiRight`, `chiK₀`, `chiK₀_map` |
| `LinearAlgebra/AlternatingFinsum.lean` | `finsum_altDim_middle` — ℤ-indexed, **no boundary hypotheses** |

**Geometric ledgers** (`.../StabilityCondition/Families/`):

| file | content |
|---|---|
| `KernelCorrespondence.lean` | `HasDerivedPushforward`, `HasDerivedTensor`, `geometricCorrespondence` |
| `KernelConvolution.lean` | `TripleProductGeometry`, `convKernel` (a **definition**), `HasProjectionFormula`, `HasFlatBaseChange`, `HasConvolutionComparison` |

## 3. Trust boundaries — what is still supplied

**Categorical, on the Hom → Mukai-isometry chain:** only `HomFiniteBounded`
(Hom-finiteness + finite Ext-amplitude) and `IsRiemannRoch` (bilinear HRR).
Both geometric. Everything else on that chain is now constructed.

**Geometric:** `HasDerivedTensor`, `HasDerivedPushforward` (where *properness*
lives), `HasCoherentPullback` (pre-existing contract), `TripleProductGeometry`,
`HasConvolutionComparison`, plus `NumericalRealization`/`Descends`/
`PreservesEuler`, `KernelAutoequivalence`, `DualKernel`.

**Nothing constructs a `Correspondence`, so there is still not one
Fourier–Mukai transform in the geometric sense.** Say this plainly in any
report; both ledgers' docstrings say it, and a clean axiom list on them is
explicitly *not* evidence to the contrary.

## 4. Decisions already litigated — do NOT reopen without new evidence

- **Indexing is ℤ, not ℕ, for the three-family alternating sum.**
  `AlternatingSum.lean`'s old claim that ℤ forces a transport does not survive
  inspection: spelled `ker (d (i+1)) = range (d i)` the indices agree on the
  nose and `(·+1)` is surjective on ℤ. ℕ is used *there* because a
  single-family sum is proved by induction, which needs a base case. The
  three-family form needs no induction and carries **no** injectivity,
  surjectivity or `Subsingleton` hypotheses — strictly weaker than either ℕ
  route. Corrected in place.
- **`AlternatingSum.lean` is not consumed by the Euler form and does not become
  consumed.** Deriving its ℕ statement from the ℤ one needs extension-by-zero of
  a dependent ℕ-family; worse than the duplication. Only
  `finrank_eq_range_add_range` is shared.
- **`k` is a `DivisionRing`, not a `Field`.** Rank–nullity is the only
  field-sensitive step and lives in a `section DivisionRing`; commutativity is
  used nowhere. `HasRankNullity` is weaker still but **declined** — it does not
  supply `StrongRankCondition`, which the support bounds need.
- **The two Euler-form variables carry different hypotheses, deliberately.**
  `linearCoyoneda` is covariant with source `C` and its shift sequence is
  tautological, so the second variable needs **no** `(shiftFunctor C n).Linear k`;
  `linearYoneda` crosses `op` and does. Documented in both files.
- **`chiHom` is junk-total.** `finrank` is 0 on non-finite modules and `finsum`
  is 0 on infinite support, so it is defined everywhere and returns nonsense
  without `HomFiniteBounded`. Deliberate; stated.
- **The first ledger does not require its middle scheme to be a product.**
  `Correspondence` does not consume it. The product is what `ConvolutionData`
  needs. Adding it there would be an unconsumed hypothesis.
- **Pushforward is stated on `Dᵇ(Coh)` while pullback is stated on `Coh`.**
  Mathematical, not stylistic: pullback of a coherent sheaf is coherent so the
  derived functor is induced; pushforward of one is not, so the derived functor
  is primitive.
- **`Mathlib` *does* have the alternating-sum vanishing statement**
  (`Module.sum_neg_one_pow_finrank_eq_zero_of_exact`). Only the
  partial-sum-as-rank identity is genuinely absent. The old docstring denied
  this; corrected.

## 5. Lean hazards found the hard way

Record these; each cost real time.

- **Give a second category its own universes.** Writing `[Category.{v} D]` in a
  section whose source category is `Category.{v} C` forces the two morphism
  universes equal. Any genuine two-category application is then unsatisfiable,
  and the elaborator *thrashes* rather than failing cleanly — a 200 000-heartbeat
  `whnf` timeout that became a **2.8-second** compile once `D` got `u' v'`.
  Four plausible other causes were tested and refuted first (variable shadowing,
  `@[reducible]` on the adapter, a global-instance projection with a
  metavariable-pattern head, a redundant `[Φ.Additive]` binder).
- **Large instance-heavy lemmas should take their categories explicitly.**
  `chiK₀_map` takes `k`, `C`, `D` explicitly; recovering two categories with
  full instance stacks by unification is not work to leave to the elaborator.
- **Section variables are included in order of first use.** An `[F.Linear R]`
  binder introduces `R` *after* `[Linear R C]` would have had to be included.
  Spell binders out rather than relying on a `variable` block.
- **Declaring into the `Functor` namespace makes bare `Linear` resolve to
  `Functor.Linear`.** Qualify category-level instances.
- **`CommShift` carries data**, so `…CommShift` instances are *definitions* and
  the `defsWithUnderscore` linter forbids underscores in their names.
  `Additive`/`IsTriangulated` are `Prop`s and keep the underscore form.
- **A stale olean silently lies.** A scratch `#check` reported three
  just-written declarations as nonexistent because the importing module's olean
  predated them. `lake build` the dependency before drawing conclusions.
- **`scripts/EnumDecls.lean`'s `libraryOf` returns `none` for unrecognised
  module prefixes, and `none` means invisible to the completeness sweep** — not
  "unclassified". `audit-complete` then passes vacuously. Filed as **#508**.
  Note `DerivedAlgGeo.CategoryTheory` itself is not a covered prefix; only its
  two named subdirectories are.

## 6. Open threads

- **#508** — `libraryOf` silently drops unrecognised directories. Filed this
  session, not started. Suggested fix: sentinel `Unclassified` bucket that fails
  the gate loudly.
- **#480** — split the per-library audit files. Still biting every concurrent PR.
- **#469, #487, #488** — closed this session.
- **`/tmp/compiso`, branch `agent/compiso-derivation`** — work in progress, see
  §7. Uncommitted. Nothing merged from it.

## 7. THE NEXT PIECE: deriving `compIso`

This is the immediate next task and it has a **validated design**. A 5-agent
design workflow settled the input set and skeleton; the design is trustworthy,
the Lean plumbing is not yet done.

### Status

- Design: **settled** (below).
- The five new classes: **compile**.
- The derivation: **not closed.** Failing on section-variable ordering across
  the stage definitions, on top of whiskering depth.
- **Nothing was landed**, deliberately: the five classes only earn their place
  if `geometricCompIso` consumes them. Merging them unconsumed would be strictly
  worse than the `HasConvolutionComparison` they replace.

### Seven inputs, not two

The 2026-08-16 handoff and this session's earlier notes said `compIso` needs the
projection formula and flat base change. **That is wrong** — it needs seven
inputs. Two already exist and become consumed; five are new.

Existing, become consumed: `HasFlatBaseChange q₁ πYW πXY p₂`,
`HasProjectionFormula πYW`.

New:

1. `HasDerivedPullbackTensor πXY` — `Lf^*(K ⊗ −) ≅ Lf^*K ⊗ Lf^*(−)`, a family
   in the twist, natural in the other slot. Not a `MonoidalFunctor`: there is no
   monoidal structure on `Dᵇ(Coh)` to be lax over.
2. `HasDerivedTensorAssoc triple` — plain associativity. **No braiding needed**,
   because `transform` pins the kernel to bifunctor slot 1 and `convKernel` puts
   `πYW^*Q` in that same slot. Flipping either convention forces a braiding —
   comment both sites.
3. `HasProjectionFormulaRight πXW` — **must be a separate class**, not a second
   field on `HasProjectionFormula`: the two are consumed at *different*
   morphisms, so merging leaves an unconsumed field at each instance. Also not a
   consequence of the left version plus a braiding (one is a family in the
   target natural in the source, the other the reverse).
4. `HasCommonPullbackRoute p₁ πXY p₃ πXW` — bundles pullback functoriality with
   the commuting triangle. **Do not reuse `GeometricDerivedPullbackComposition`**:
   it is stated at the literal `f ≫ g` (so bridging two composites needs
   `eqToHom` transport) and drags three `PreservesPerfectPullback` instances and
   a `perfectIso` field that nothing here touches.
5. `HasCommonPushforwardRoute πYW q₂ πXW q₃` — no existing analogue at all;
   nothing in the repo names `R(g∘f)_* ≅ Rf_* ⋙ Rg_*`.

Each route class carries a `comm` **guard** that is deliberately *not* consumed —
it is what makes the `iso` the right thing to ask for. Say so in the docstring.

`HasConvolutionComparison` is **deleted** once the derivation lands; nothing
consumes it. Remove its audit lines too.

### Naturality — get the claim right

`ConvolutionData.compIso` is a **bare family**; every consumer evaluates it at a
point. The correct claim is **natural in `E`, uniform in `P` and `Q`**.
Naturality in `E` is *free* — all eight intermediates are functors
`Dᵇ(Coh X) ⥤ Dᵇ(Coh W)` and every step is an iso of such functors. Asserting
naturality in `P` or `Q` would be an unconsumed strengthening. An earlier
framing of this task said "naturally and uniformly in P and Q"; that is wrong.

### The skeleton

Write `f^*` for `boundedCoherentDerivedPullback f`, `f_*` for
`derivedPushforward f`, `(⊗K)` for `(derivedTensor _).obj K`;
`a := πXY^*P`, `b := πYW^*Q`, `M := b ⊗ a`.

```
E₀ = p₁^* ⋙ (⊗P)  ⋙ q₁_*  ⋙ p₂^*  ⋙ (⊗Q) ⋙ q₂_*
E₁ = p₁^* ⋙ (⊗P)  ⋙ πXY^* ⋙ πYW_* ⋙ (⊗Q) ⋙ q₂_*
E₂ = p₁^* ⋙ πXY^* ⋙ (⊗a)  ⋙ πYW_* ⋙ (⊗Q) ⋙ q₂_*
E₃ = p₁^* ⋙ πXY^* ⋙ (⊗a)  ⋙ (⊗b)  ⋙ πYW_* ⋙ q₂_*
E₄ = p₁^* ⋙ πXY^* ⋙ (⊗M)  ⋙ πYW_* ⋙ q₂_*
E₅ = p₁^* ⋙ πXY^* ⋙ (⊗M)  ⋙ πXW_* ⋙ q₃_*
E₆ = p₃^* ⋙ πXW^* ⋙ (⊗M)  ⋙ πXW_* ⋙ q₃_*
E₇ = p₃^* ⋙ (⊗ convKernel) ⋙ q₃_*
```

| step | input |
|---|---|
| 0 | reassociation only — `transform` is an `abbrev`, so `E₀` is defeq |
| 1 | `HasFlatBaseChange.iso` at `(q₁, πYW, πXY, p₂)` |
| 2 | `HasDerivedPullbackTensor.iso P` at `πXY` |
| 3 | `(HasProjectionFormula.iso Q).symm` at `πYW` |
| 4 | `HasDerivedTensorAssoc.iso b a` on `triple` |
| 5 | `HasCommonPushforwardRoute.iso` — tail whisker only |
| 6 | `HasCommonPullbackRoute.iso` — head whisker only |
| 7 | `HasProjectionFormulaRight.iso M` at `πXW`, landing on `convKernel` by one delta unfold |

### Two things to do differently

The failure mode is *elaboration*, not logic. `Functor.assoc` is `rfl`, but
Mathlib's own note at `Functor/Category.lean:182-184` warns that relying on it
"tends to make Lean slow" and advises explicit associators — and this repo
already carries seven `set_option backward.isDefEq.respectTransparency false`
in `DerivedPullbackLaws`/`DerivedPullbackShift` for exactly this regime.

1. **Inline each step's full functor type** rather than naming stages via
   section variables. The verbosity is the point: it removes the argument-order
   ambiguity that consumed the iterations. Do not write one big term with
   inferred intermediates — that hands the unifier eight ambiguous higher-order
   splits.
2. **Build from the middle outward**, compiling each step in isolation against
   an explicitly ascribed type, before assembling.

If the seam at step 0 proves intractable, the fallback is **not** to weaken the
theorem — restate the five classes in pre-whiskered form (quantified over the
ambient head/tail functors). An elaboration problem must not change the ledger.

## 8. Work menu after `compIso`

1. **`HomFiniteBounded` for a concrete category.** The obligation #513 moved
   rather than removed. Needs the geometric substrate.
2. **Associativity of convolution** — a second comparison layer relating the two
   bracketings; `Convolution.lean` names it as absent.
3. **`UnitKernelData` geometrically** (`𝒪_Δ`) and **`DualKernel`**
   (`P^∨ ⊗ p^*ω[dim]`). Both geometric, both absent.
4. **#508**, **#480** — infra, both scoped in their issues.

## 9. Report and PR expectations

Unchanged, and this session met them: state what is claimed vs delivered, name
every supplied datum added, and pre-empt the two standard attacks
(provable-datum, overclaiming-name) in the PR body. Two further habits earned
their keep this session and should continue:

- **Attribute ratchet movements.** #530 lowered SC 380 → 375, but its own delta
  was zero — the slack was pre-existing on `main`. Say so, or it reads as a
  saving the PR made.
- **Re-derive audit numbers privately after a gate run.** Concurrent worktrees
  used to clobber the shared `/tmp` artifacts; #494 fixed that, but re-deriving
  on the merged base after a rebase is still the only way to know the ceiling
  carried.
