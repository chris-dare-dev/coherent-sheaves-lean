# Fourier–Mukai lane — post-review work handoff

**Audience:** a working session (autonomous or interactive) picking up the
Fourier–Mukai lane. Not a human summary.
**Baseline:** `origin/main` after PR #486 merges (branch `fix/fm-review-round2`,
built on `91ac407`). Everything below assumes that merge; if #486 is not yet in
your `origin/main`, stop and rebase onto its branch.
**Prior records:** round-1 review + response in
`.claude/reviews/2026-08-15-fourier-mukai-kernel-lane-handoff.md`; round-2
review + remediation addendum in
`.claude/reviews/2026-08-16-fm-lane-round2-review.md`. Read both before
touching lane files — they are the reason several designs look the way they do.

## 0. How to work (non-negotiable mechanics)

```bash
cd /Users/chris.dare/Personal/SourceCode/derived-alg-geo-lean
git fetch origin
git worktree add -b agent/<your-branch> /tmp/<your-dir> origin/main
cp -c -R .lake /tmp/<your-dir>/.lake     # APFS clone, ~20s; avoids a Mathlib rebuild
cd /tmp/<your-dir> && lake build && scripts/gates.sh
```

- **Never work in the shared checkout itself.** Autonomous `formalize-issue`
  sessions switch branches in it mid-run; a verification pass there was
  silently invalidated once already.
- **Gates are the definition of done:** `scripts/gates.sh` must print
  `all gates passed (full)` — 17 gates. Post-#486 baseline:
  ratchet ceilings AlgebraicGeometry **1098**, StabilityCondition **381**,
  DGCategory **0** (`scripts/check_audit_complete.py:CEILINGS`); axiom closure
  of every lane declaration exactly `[propext, Classical.choice, Quot.sound]`.
- **Every new public declaration must be appended to the matching audit file**
  (`scripts/StabilityConditionAudit.lean` / `AlgebraicGeometryAudit.lean` /
  `DGCategoryAudit.lean`) or the `audit-complete` gate fails — the ceilings are
  exact, so a single unaudited decl breaks CI. Deleting a declaration that the
  audit lists requires deleting its `#print axioms` line too (the audit file
  otherwise fails to elaborate). If your change *improves* a ceiling, lower it
  (`check_audit_complete.py --relax` prints the new block).
- The audit files are a single append-point; concurrent PRs conflict there
  structurally (#480, open). Expect to rebase that hunk.
- **Signature changes:** grep for callers with `-A2`; this repo has multiline
  call sites (`HNFiltration.prefix` had two spellings across five files, and
  the one-line grep missed `Weak/HarderNarasimhan/Heart.lean` and
  `Weak/Tilting/HarderNarasimhan.lean`).
- The unused-arguments linter is a gate. If removing a hypothesis orphans an
  argument somewhere, remove that argument too (that is how `prefix` lost
  `hk₀`), don't `@[nolint]` it.
- House docstring style: every lane file carries a "What this file does not
  assert" section, and it is load-bearing — two review rounds were largely
  about keeping those sections exactly true. If your change makes any
  docstring sentence false — including sentences in *other* files about your
  files — fix the sentence in the same PR. Claims of the form "X does not
  exist in this repository" are the highest-risk sentences; grep before
  writing one and grep when landing anything that might invalidate one
  (that exact staleness was the round-2 escape).
- Eager instance inclusion is active: `theorem`s auto-include instance
  variables whose types mention used variables; prune with `omit [...] in`
  (see `Stability/Composition.lean`'s Charge section for the idiom).
  `def`s don't need this.
- PRs: branch from `origin/main`, merge commits (not squash), PR body explains
  per-file intent. CI is the single `build` check (`ci.yml`, runs the gates).

## 1. What the lane is, post-review

End-to-end claim (unchanged, now twice-reviewed): *a kernel functor transports
a Bridgeland stability condition; both directions are computed by kernels; and
composing two transports is the transport by the convolved kernel.* Everything
is conditional on named supplied data; the named-obligation discipline is the
design, not an accident.

### File map (all on main, all gates-clean)

Generic triangulated layer (imports Mathlib only, never the stability track):

| File | Content |
|---|---|
| `CategoryTheory/Triangulated/FourierMukai/Basic.lean` | `Correspondence` (pull/tensor/push), `transform`, `IsKernelFunctor`; transform triangulated when constituents are |
| `CategoryTheory/Triangulated/FourierMukai/Convolution.lean` | `ConvolutionData` (conv + `compIso`, Prop. 5.10 as data), closure of kernel functors under composition |
| `CategoryTheory/Triangulated/FourierMukai/GrothendieckGroup.lean` | `transformK₀`, `K₀_map_eq_transformK₀`, `transformK₀_conv` |
| `CategoryTheory/Triangulated/GrothendieckGroup/{Basic,Functorial,Presentation}.lean` | repo-owned `K₀` (free abelian / triangle relations), `K₀.map` + `map_congr`/`map_comp`/`mapAddEquiv`, presentation machinery |
| `CategoryTheory/Triangulated/PostnikovTower.lean` | finite filtrations; `K₀.of_postnikovTower_eq_sum`; post-#486 the zero-length fact is the theorem `isZero_of_length_zero`, not a field |
| `CategoryTheory/Triangulated/LinearYoneda.lean` | `linearYoneda_isHomological` (ModuleCat k-valued homological functor) |
| `LinearAlgebra/AlternatingSum.lean` | alternating-sum-of-dims vanishing along bounded exact sequences (ℕ-indexed by design) |
| `LinearAlgebra/Lattice/Mukai/Basic.lean` | abstract Mukai extension ℤ×Λ×ℤ, pairing, IsSpherical/IsIsotropic/expectedDim |

Stability track (imports the generic layer, never the reverse):

| File | Content |
|---|---|
| `StabilityCondition/Symmetry/Autoequivalence/FourierMukai.lean` | `KernelAutoequivalence` (corr+kernel+equiv+iso), `DualKernel`, `mapF_eq_transformK₀`, `transformK₀_dual_comp` (mutual inverses from the unit, no convolution), `actStab`/`actStabOfDual`, `trans` (@[reducible], needs `ConvolutionData`), `actStab_trans` |
| `StabilityCondition/Symmetry/Autoequivalence/Stability/Composition.lean` | `Slicing.mapEquiv_trans` (ext-on-rfl; pin-fragility note in place), `hlam_trans`, `actStabAut_trans` |
| `StabilityCondition/Symmetry/Autoequivalence/Stability/Transport.lean` | `actStabAut` — the transport itself (predates lane) |
| `StabilityCondition/Symmetry/Autoequivalence/Stability/ClassMap.lean` | **predates lane, easy to miss:** `AutPair`, `AutPairQuot : Group`, full `MulAction` on `WithClassMap C v` for invertible `lam` |

Numerical / K3 layer:

| File | Content |
|---|---|
| `AlgebraicGeometry/Numerical/GrothendieckGroup/MukaiVector.lean` | `IntegralMukaiData` (post-#486: `c₁`, `b`, `b_spec` — no `b_comm`), `mukaiSInt` as a *def*, `mukaiVector`, pairing identification, sphericity-of-vector iff χ=2 |
| `.../Realization.lean` | `NumericalRealization` (bare `cl`), `Descends`, `PreservesEuler`, `pairing_mukaiVector_eq_of_preservesEuler`, `..._eq_on_realized` |
| `.../EulerTransfer.lean` | `CategoricalEulerForm` (supplied), `IsRiemannRoch` (bilinear HRR, assumed), `PreservesCategoricalEuler`, `preservesEuler_of_descends`, `pairing_mukaiVector_eq_on_realized_of_categorical` |

### Trust boundaries — current supplied data, all verified genuinely unprovable

`Correspondence`, `ConvolutionData`, `IntegralMukaiData` (three fields),
`NumericalRealization`, `Descends`, `PreservesEuler`, `CategoricalEulerForm`,
`IsRiemannRoch`, `PreservesCategoricalEuler`, `KernelAutoequivalence`
(`iso` must stay data — `trans` consumes it to construct the composite's iso),
`DualKernel`. Round 2 attacked each; the two that fell (`zero_isZero`,
`b_comm`) are gone. If you add a supplied datum, expect the next review to
attack it the same way: *is it provable at the pin, and does anything consume
it?* Prove what is provable, demand only what is consumed.

## 2. Decisions already litigated — do NOT reopen without new evidence

- `b_spec` constrains `b` only on the image of `c₁` — accepted, documented.
- Symmetry of `b` on the image is the theorem `b_comm_on_realized`; total
  symmetry is deliberately not demanded.
- Surjectivity of the source realization is the right hypothesis for global
  `PreservesEuler` (round 1).
- The ℕ-indexed `AlternatingSum` interface is correct; a ℤ-indexed LES
  reindexes once at the boundary, with zero tails making `hex : ∀ i` free
  (round 2 re-verified against a synthetic LES walkthrough).
- `@[reducible]` on `KernelAutoequivalence.trans` is load-bearing:
  `Functor.IsTriangulated` is indexed by the `CommShift` instance term, so
  hand-rolled composite instances don't unify. Verified no instance-search
  blowup; the six `Equivalence.trans` instances carry only the args they need.
- `Slicing.mapEquiv_trans`'s 12 instance arguments are all required to *state*
  it (`Slicing.mapEquiv` demands the full package per equivalence).
- `hlam` is stated for the quasi-inverse; `lam₁.comp lam₂` order in
  `hlam_trans` is forced by `(Φ.trans Ψ).inverse = Ψ.inverse ⋙ Φ.inverse`.
- Adjunction is NOT the hypothesis for Euler preservation; full faithfulness
  + `k`-linearity + shift-compatibility is. Serre duality is not needed for
  that step. Do not reintroduce either framing.
- Nothing may be named a Hodge or isometry result: no Hodge structure exists in
  the repo, and no map of Mukai lattices is constructed anywhere. The
  `..._eq_of_preservesEuler` / `..._eq_on_realized` naming is the enforced
  standard (round 1 P1). See §4-D for what would make "isometry" earnable.
- `NumericalRealization` / `CategoricalEulerForm` as one-field structures:
  deliberate named-obligation convention, matching `Families`.

## 3. Open threads with issue numbers

- **#469** — `ShiftSequence ℤ` for the k-linear Yoneda. Three Mathlib gaps,
  file-and-line precise in the issue and mirrored in `LinearYoneda.lean` /
  `EulerTransfer.lean` docstrings: `Linear R Cᵒᵖ` does not exist;
  `ShiftedHom.opEquiv_symm_smul` / `opEquiv'_symm_smul` do not exist; then the
  instance itself. This is the gate on the entire Hom-built Euler form (§4-A).
  `upstream-candidate`: the right fix is Mathlib PRs, with repo-local stubs
  acceptable in the interim if clearly quarantined.
- **#487** — retire `K₀.mapF` in favor of `K₀.map` (mechanical; scope written
  in the issue; audit + ceiling notes included).
- **#488** — relocate `Foundation/QuasiAbelian.lean` and
  `Foundation/ExtensionClosure.lean` out of `StabilityCondition/` (latent
  layering hazard; same shape as #454, including its watch-for-extra-files
  warning).
- **#480** — split the per-library audit files (infra; will keep biting every
  concurrent PR until done).
- **Closed and available:** #460/#461/#462 landed the geometric substrate —
  `Families/BoundedGeometry.lean` has `SchemeBoundedCoherentDerivedCategory X`
  (= Dᵇ(Coh X) over the repo-owned `Coh X`), `Perf(X)` as the thick envelope,
  a structure-sheaf perfect generator, fiber/base-change exposure, and named
  pullback-restriction contracts; `GeometricBaseChange.lean` /
  `FiniteTypeGeometry.lean` build the base-change witness and openness/relative
  HN on top. The FM lane has not yet touched any of it (§4-B).

## 4. The work menu, ranked

Each item is scoped so a session can take exactly one and land a reviewable PR.

### A. Build the categorical Euler form from Hom (flagship; blocked on #469)

The designed path, with every prepared input already merged:

1. (#469, or Mathlib-bump) `ShiftSequence ℤ` for `(linearYoneda k C).obj B`,
   mirroring Mathlib's `preadditiveYoneda` version with
   `LinearEquiv.toModuleIso`.
2. From `linearYoneda_isHomological` + the shift sequence: the long exact
   `Hom(E, F⟦i⟧)` sequence of a distinguished triangle, in `ModuleCat k`.
3. New supplied-data structure for finiteness — Hom-finiteness
   (`FiniteDimensional k (Hom(E, F⟦i⟧))`) and boundedness (vanishing outside
   `[a,b]` per pair). Genuine data at this level of abstraction; name it,
   don't smuggle it.
4. Define `homEulerForm : K₀ 𝒯 →+ K₀ 𝒯 →+ ℤ` as the alternating sum.
   Biadditivity in each argument = the vanishing of the alternating sum along
   the LES of a triangle = `DerivedAlgGeo.LinearAlgebra.sum_range_succ_smul_finrank_eq_zero`
   after the one boundary reindex (the ℕ-interface was shaped for exactly this
   caller; see its docstring before fighting it).
5. Show it discharges `CategoricalEulerForm 𝒯` — at which point that structure
   stops being supplied for Hom-finite 𝒯, and its docstring (and
   `EulerTransfer.lean`'s) must be updated in the same PR.
6. Then the second named obligation: `PreservesCategoricalEuler` for a fully
   faithful `k`-linear shift-compatible functor — the term-by-term dimension
   match. This is where the `k`-linearity caveat that round 1 added becomes an
   actual hypothesis of an actual theorem.

### B. Connect the FM skeleton to the landed geometric substrate (large; start with a ledger)

`Correspondence` needs pull / tensor / push on `Dᵇ(Coh (X × Y))`-like
categories. What exists after #460–462: the bounded coherent and perfect
categories per scheme, pullback-restriction *contracts* (obligations named,
functors lifted once objectwise preservation is supplied), base-change
witnesses, and the `Families` derived-pullback coherence stack. What does not
exist: a derived tensor product, a derived pushforward, products of schemes
exposed for this purpose, or any projection formula. Do not attempt the full
geometric `Correspondence` in one issue. The right first PR is a dependency
ledger in the `Families` style: a file that names, as supplied data with
docstrings, exactly the functor package on the product that a geometric
`Correspondence 𝒳 𝒴 𝒵` needs — then instantiates the abstract lane against
it, so the remaining gap is enumerated instead of implicit. (Pattern:
`SchemeDerived`'s inhabitant-free ledgers, or #217.)

### C. Kernel-tracked group entry point (small, self-contained, no new geometry)

With a `DualKernel`, `transformK₀_dual_comp` + `transformK₀_comp_dual` make
the two class maps mutually inverse `AddMonoidHom`s. So: given `A`, `D`, a
class map `v`, and a compat hypothesis in kernel terms, the lattice map is an
`AddEquiv`, and `(A, lam)` yields a `GroupAction.AutPair v`. Write
`KernelAutoequivalence.toAutPair (A) (D : DualKernel A) (v) (lam : Λ ≃+ Λ)
(hlam : ...) : AutPair v` and the lemma that its `AutPairQuot` action agrees
with `actStabOfDual`. This is the bridge the round-2 review noted was missing
when the docstrings denied the group existed; after #486 the docstrings point
at it — this item makes the pointer a theorem. Also natural here, same PR or
next: a `UnitKernelData` structure (a kernel presenting `𝟭` as a transform —
classically `𝒪_Δ`, here supplied) and `KernelAutoequivalence.id` from it,
which is the identity-law half the composition story deliberately lacks; and
the associativity-of-convolution data layer `Convolution.lean`'s docstring
names as absent. None of these need geometry; all extend the supplied-data
frontier, so write the "not asserted" sections first.

### D. Earn the isometry name (algebra only, no geometry)

The reviews barred "isometry" because no lattice map exists. The unlock is
additivity of `c₁`: define `AdditiveMukaiData extends IntegralMukaiData` with
`c₁ : N →+ Λ` (supplied — genuinely stronger geometry), then `mukaiVector`
becomes an `AddMonoidHom N →+ Mukai.MukaiLattice Λ`, and given `φ : N →+ N'`
plus a compatible lattice map `Λ →+ Λ'` the actual map of Mukai extensions can
be written and `pairing_mukaiVector_eq_of_preservesEuler` upgrades to a
genuine isometry-on-a-map statement. Keep both layers: the bare version stays
(weaker data, already consumed), the additive version earns the name.

### E. Mechanical debt (good warm-up issues)

#487 (mapF migration) and #488 (relocation) — both fully scoped in their
issue bodies, both expected to touch the audit files (see §0), #487 expected
to *lower* the StabilityCondition ceiling again.

## 5. Verification baseline to reproduce before and after your change

```
lake build                  clean
scripts/gates.sh            17/17 pass (full)
AlgebraicGeometry ratchet   ceiling 1098
StabilityCondition ratchet  ceiling 381
DGCategory ratchet          ceiling 0
axiom closure               [propext, Classical.choice, Quot.sound]; grep audits for sorryAx
```

If a ceiling rises under your change, that is a bug in your change (an
unaudited new declaration), not a number to bump. If one falls, lower it.

## 6. Report and PR expectations

Follow the two review records' format when handing off: state what is claimed
vs delivered, name every supplied datum you add, and pre-empt the two standard
attacks (provable-datum, overclaiming-name) in the PR body. The lane has now
survived two adversarial rounds clean of both; keep it that way.
