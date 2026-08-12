---
authorship: agent-generated
type: adversarial-coordination-audit
issue: 84
date: 2026-08-11
repository: chris-dare-dev/bridgeland-stab-lean
status: ready-for-owner-review
---

# Issue #84 geometry/moduli coordination audit

## Verdict

**KEEP PARKED. The unpark trigger is not met.**

The coherent-sheaf repository has completed the B1 coherent-category and affine-comparison
foundation and substantial B2/B3 infrastructure. It has not proved projective Serre finiteness
for arbitrary coherent sheaves, and its B5 duality/Riemann--Roch gate is explicitly incomplete.
There is also no recorded ownership/API decision, repository, or linked implementation issue for
Quot spaces, algebraic stacks, semistable reduction, or good moduli spaces.

This audit found no honest Lean theorem that can be added to `bridgeland-stab-lean` for #84. No
source or coverage-registry status should change: Parts I, II, IV, and VI remain targets, and the
geometric realization work remains foreign to this repository.

## Audit basis

The audit used these public snapshots on 2026-08-11:

- `bridgeland-stab-lean` `origin/main` at `18c57f8` (PR #137 merged);
- `coherent-sheaves-lean` `origin/main` at `3b48095`;
- `coherent-sheaves-lean`'s pinned Mathlib `v4.32.1`, commit
  `520045ab14e26149ee970e2e617ca04b09bde5d6`;
- the live bodies, labels, states, and comments of the linked GitHub issues and PRs below;
- local sibling repositories under `/Users/chris.dare/Personal/SourceCode`.

Negative search evidence is recorded as such, not promoted to a theorem about all present or
future upstream work. At the pinned Mathlib revision, generic derived-category machinery exists,
as do scheme pullbacks and flat-descent files, but repository searches found no declarations or
files named `PerfectComplex`, `AlgebraicStack`, `QuotScheme`, `GoodModuli`, or
`DualizingComplex`. Searches of current public Mathlib code/issues/PRs found no matching active
implementation either. No local sibling repository owns reusable Lean Quot/stack/good-moduli
infrastructure. `stability-mflds` is a Python exact-arithmetic/numerical package, not such an
owner.

## Dependency matrix

| Boundary | Intended owner | Current evidence | Gate status |
|---|---|---|---|
| Abstract stability-in-families contract | `bridgeland-stab-lean` | [#83](https://github.com/chris-dare-dev/bridgeland-stab-lean/issues/83) is open and blocked, including on #84's cross-repository interfaces | **open** |
| B1: `Coh(X)` abelian, exact inclusion | `coherent-sheaves-lean` | [#10](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/10), commit [`d5b00ad`](https://github.com/chris-dare-dev/coherent-sheaves-lean/commit/d5b00ad) | **met** |
| B1: affine comparison/equivalence | `coherent-sheaves-lean` | [#11](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/11), main commits [`93d8b3c`](https://github.com/chris-dare-dev/coherent-sheaves-lean/commit/93d8b3c) and [`dfedb08`](https://github.com/chris-dare-dev/coherent-sheaves-lean/commit/dfedb08) | **met** |
| B2: divisors, Picard tensor, effective sequence, determinant | `coherent-sheaves-lean` | [#21--#25](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/21), [#36](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/36), and [#79](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/79) are closed with implementations on main | **met for the named B2 milestone** |
| Derived/perfect complexes and geometric pull/push/tensor/base change | Mathlib-shaped foundations plus a geometric owner | Generic categorical infrastructure exists, but no project issue or owner contract covers the geometric package required by #84 | **missing owner and issue** |
| B3: affine derived vanishing and finite-cover boundedness | `coherent-sheaves-lean` | [#28](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/28) and [#30](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/30); implementations are on main | **met** |
| B3: finite-dimensional `H^i(X,F)` for arbitrary projective coherent `F` | `coherent-sheaves-lean` | [#29](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/29) is closed as `completed`, but its body explicitly leaves four central deliverables unchecked: finite graded/twist resolutions, finite-dimensional Cech homology, the projective theorem, and construction of `FiniteDimensionalCohomology` | **not met; tracker inconsistency** |
| B3: Euler characteristic and additivity | `coherent-sheaves-lean` | [#31](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/31) and [#32](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/32) construct results relative to explicit finite-cohomology data | **conditional, not a discharge of #29** |
| B5: canonical/dualizing object | `coherent-sheaves-lean` plus upstream-shaped foundations | [#39](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/39) remains open/blocked after its first slice; it explicitly lacks scheme-relative differentials, determinant descent, a genuine dualizing complex, and #29 | **not met** |
| B5: Serre duality and geometric surface Riemann--Roch | `coherent-sheaves-lean` | [#40--#45](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues/40) are all open/blocked. Draft [PR #114](https://github.com/chris-dare-dev/coherent-sheaves-lean/pull/114) is an honest conditional interface/first slice and explicitly does not construct the geometric duality realization | **not met** |
| BG/BMT inputs required by later applications | `coherent-sheaves-lean` or a dedicated geometric package | No linked Lean issue or theorem was found. Numerical Python checks in `stability-mflds` are not geometric Lean proofs | **missing issue and owner contract** |
| Semiorthogonal decompositions and relative/local t-structures | abstract API in `bridgeland-stab-lean`; geometric adapters elsewhere | #83 asks for a reviewed abstract SOD decision, but no child/design issue is linked; no geometric realization issue was found | **missing design issue** |
| Quot functor/space and moduli of complexes | reusable moduli package, Mathlib-shaped namespaces | No repository, API decision, linked issue, commit, or upstream implementation was found | **missing** |
| Algebraic stacks, semistable reduction, good moduli spaces | reusable moduli package, with upstreamable foundations | No repository, API decision, linked issue, commit, or upstream implementation was found | **missing** |
| Theorems 22.2, 24.1, then 29.2 applications | adapter layer after all preceding rows | Registry remains `target`; no geometric prerequisites exist | **parked** |

## Adversarial findings

### 1. B3 cannot be treated as complete merely because #29 is closed

The live #29 body is stronger evidence than its state label: it says the geometric theorem is
still missing and lists the remaining construction explicitly. No successor issue was found for
that work. Therefore a dependency link to closed #29 would currently hide, rather than resolve,
the blocker.

Recommended correction: reopen #29, or create and link a successor issue whose acceptance
criterion is the actual construction of `FiniteDimensionalCohomology` for arbitrary coherent
sheaves on the selected projective class. If a successor is created, #29 should state that its
closure covered interfaces/reconnaissance rather than the theorem in its title.

### 2. PR #114 is useful but does not flip B5 green

PR #114 deliberately makes derived Serre duality and perfect pairings explicit input data. That
is a sound interface boundary and should not be relabelled as the geometric existence theorem.
Even after it merges, #39--#45 must remain open until the dualizing complex, the comparison with
`omega_X[n]`, finite cohomology, and the geometric realization are constructed.

### 3. The ownership trigger is wholly absent

Issue #84 says that an ownership/API decision for Quot/stacks/good-moduli must exist before
unparking, but it links no decision issue and names no selected package. The audit found no
candidate Lean repository already doing this work. This half of the trigger therefore fails
independently of the incomplete B3/B5 gates.

### 4. “Mathlib has derived categories” is not a six-functor or moduli substrate

The generic derived-category API cannot be cited as a construction of perfect complexes on a
scheme, derived pull/push/tensor, base change, relative `RHom`, dualizing complexes, algebraic
stacks, or Quot representability. Each bridge needs a separately owned API and theorem.

## Recommended ownership decision

Record the following dependency direction before implementation begins:

1. **Mathlib-shaped foundations:** category fibred in groupoids/descent, scheme-relative
   derived/perfect APIs, and generic representability/property lemmas should use upstreamable
   `CategoryTheory`/`AlgebraicGeometry` namespaces. They may incubate out of tree, but no
   project-specific stability notion should enter them.
2. **`coherent-sheaves-lean`:** owns coherent sheaves, projective finiteness, perfect/derived
   geometric inputs, characteristic classes, duality, and BG/BMT statements. It must not depend
   on `bridgeland-stab-lean`.
3. **A new reusable moduli package:** owns moduli of perfect complexes, Quot, boundedness,
   semistable reduction, algebraic stacks, and good moduli spaces. It should depend on Mathlib
   and, where genuinely needed, `coherent-sheaves-lean`. It must not live inside
   `bridgeland-stab-lean` and must not introduce a dependency back from `coherent-sheaves-lean`.
4. **`bridgeland-stab-lean`:** owns abstract stability/family/SOD interfaces and adapter theorems
   consuming the geometric/moduli packages. It does not own their construction.

The package name is intentionally not fixed by this audit. The first executable item is a
reviewed ownership/API spike, not an empty repository or placeholder declarations.

## Next executable cross-repository actions

Perform these in order:

1. **Repair the B3 tracker.** Reopen #29 or create its explicit Serre-finiteness successor, link
   it from #29, #39, and #84, and keep its theorem-level acceptance criteria.
2. **Review PR #114 at its stated scope.** It may land as a conditional interface slice, but do
   not close #40/#41 or call B5 complete from that merge.
3. **Open a CohLean ownership/API issue for derived geometry.** Its deliverable is the exact
   minimal API for perfect complexes, derived pull/push/tensor, base change, `RHom`, and the
   dualizing-complex bridge, together with an upstream-gap inventory at the current pin.
4. **Open the SOD/local-t-structure design issue linked from #83.** Separate the abstract
   triangulated API (this repository) from geometric base-change realizations (foreign owner).
5. **Open one moduli ownership spike before creating implementation tickets.** It must choose the
   reusable package and dependency graph, then split Quot, stacks/descent, moduli of complexes,
   boundedness/semistable reduction, and good-moduli infrastructure into linked issues.
6. **Add BG/BMT theorem issues to their geometric owner.** Numerical surrogates or executable
   checks are not substitutes for the coherent-sheaf theorems required downstream.
7. **Keep #84 labelled `parked`.** Re-audit only when B3 finiteness and the relevant B5 existence
   results land and the moduli ownership spike has a reviewed decision with linked issues.

## Exact recommended issue #84 comment

```markdown
### 2026-08-11 cross-repository gate audit

**Unpark decision: KEEP PARKED. The trigger is not met.**

Audited against `bridgeland-stab-lean` main at `18c57f8`,
`coherent-sheaves-lean` main at `3b48095`, its pinned Mathlib `v4.32.1`, the live
CohLean issues/PRs, and local sibling repositories.

| Gate | Status | Evidence |
|---|---|---|
| B1: `Coh(X)` abelian/exact + affine comparison | met | CohLean #10/#11; commits `d5b00ad`, `93d8b3c`, `dfedb08` |
| B2 divisor/Picard/determinant foundation | met for the named B2 milestone | CohLean #21--#25, #36, #79 |
| B3 affine vanishing/boundedness | met | CohLean #28/#30 |
| B3 projective finite-dimensional cohomology | **not met** | CohLean #29 is closed as completed, but its body still leaves the projective theorem, finite twist resolution, finite-dimensional Cech homology, and `FiniteDimensionalCohomology` construction unchecked; no successor issue is linked |
| B5 dualizing/Serre/HRR existence | **not met** | CohLean #39--#45 remain open/blocked. Draft PR #114 is explicitly a conditional first slice, not a construction of the geometric duality realization |
| Perfect/derived pull-push-tensor/base-change ownership | **missing** | no linked design/implementation issue |
| SOD and relative/local t-structure ownership | **missing** | #83 requests a design decision but links no child/design issue |
| Quot/stacks/semistable-reduction/good-moduli ownership | **missing** | no selected package, issue, commit, or upstream implementation found |
| BG/BMT geometric inputs | **missing** | no linked Lean theorem issue found |

The B3 tracker must be repaired first: reopen CohLean #29 or create and link a successor that
actually constructs projective `FiniteDimensionalCohomology`. PR #114 can be reviewed and merged
at its honest conditional scope without changing the B5 gate.

Recommended ownership direction: Mathlib-shaped categorical/geometric foundations;
`coherent-sheaves-lean` for coherent/perfect/duality/BG-BMT inputs; a new reusable moduli package
for Quot, stacks, boundedness, semistable reduction, and good moduli; and
`bridgeland-stab-lean` only for abstract family/SOD contracts and adapters. Before creating that
package, open a reviewed ownership/API spike fixing its dependency graph and minimal public API.

Next linked actions: (1) repair #29; (2) review PR #114 without closing B5; (3) open a CohLean
derived/perfect/base-change API issue; (4) open #83's abstract SOD design issue; (5) open the moduli
ownership spike and then split Quot/stacks/good-moduli tickets; (6) open geometric BG/BMT issues.

No source theorem or coverage promotion is warranted in this repository. Parts I, II, IV, and
VI remain `target`.
```

## Reviewer challenges

An adversarial reviewer should reject this packet if any of the following can be supplied:

1. a linked theorem that actually constructs B3 projective finite-dimensional cohomology for
   arbitrary coherent sheaves, rather than only an interface or special line-bundle case;
2. a geometric construction behind PR #114's explicit Serre-duality input structures;
3. an existing selected repository and reviewed API decision for Quot/stacks/good-moduli;
4. a current Mathlib declaration for algebraic stacks, Quot representability, or good moduli
   spaces missed by both the pinned-tree and GitHub searches;
5. a dependency graph that places the geometric implementation in `bridgeland-stab-lean`
   without violating its documented no-geometry boundary.
