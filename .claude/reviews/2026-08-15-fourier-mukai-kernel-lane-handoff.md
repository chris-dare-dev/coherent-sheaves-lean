# Fourier–Mukai kernel functor lane review handoff

Branch: `agent/fourier-mukai-kernel-interface`

Base: `main` @ `801a9d7` (no divergence at branch time; nothing pushed, nothing merged)

Worktree: `/Users/chris.dare/Personal/SourceCode/derived-alg-geo-lean-fm-gate`
(a `git worktree` of the main checkout, created because the main checkout is
shared with autonomous sessions — see "Operational hazards" below)

Scope: Fourier–Mukai transforms as abstract kernel functors between
triangulated categories, carried through K₀ and the Mukai vector to
preservation of the Mukai pairing on realized classes, plus the linear algebra
that a Hom-built Euler form would need.

Commits: 7 + 1 review-fix commit. Files: 14. New public declarations: 82.

**Status: review round 1 applied.** Findings 1, 2, 4, 5, 6, 7 are fixed;
finding 3 needs an owner decision and is recorded below. Full
`scripts/gates.sh` is green after the fixes.

---

## Review round 1 — what changed

| # | Finding | Disposition |
|---|---|---|
| 1 | `s` derivable under `IsK3`, not a trust boundary | **Fixed.** `s` and `s_spec` removed as fields; `K3.mukaiSInt E := χ E − r E` is now a `def` and `mukaiSInt_spec` a theorem from `chi_eq_rank_add_mukaiS`. `IntegralMukaiData` requires `[IsK3 A N]` and carries only `c₁`, `b`, `b_comm`, `b_spec`. |
| 2 | "isometry of Mukai lattices" overclaims | **Fixed by renaming.** Old → new: `pairing_mukaiVector_map` → `..._eq_of_preservesEuler`; `selfPairing_mukaiVector_map` → `..._eq_of_preservesEuler`; `isSpherical_mukaiVector_map_iff` → `..._iff_of_preservesEuler`; `pairing_mukaiVector_transform` → `pairing_mukaiVector_eq_on_realized`; `..._transform_of_categorical` → `..._eq_on_realized_of_categorical`. Every "isometry" / "acts on Mukai lattices" claim is gone; docstrings now state that no lattice map is built, `mukaiVector` is not additive, and nothing is claimed off the image of `mukaiVector ∘ R.cl`. |
| 3 | Generic layer imports `StabilityCondition` | **Open — owner decision.** See below. |
| 4 | Full-faithfulness explanation omits `k`-linearity | **Fixed.** `EulerTransfer` now says the functor must be fully faithful **and `k`-linear** and shift-compatible, and that Serre duality is unnecessary once full faithfulness is known. `Realization`'s `PreservesEuler` docstring corrected the same way. |
| 5 | Branch cites unpinned Huybrechts coordinates | **Fixed.** Owner chose to strip. All five "Huybrechts, Prop. 5.10" citations removed; the docstrings now say "the classical composition law". No Lean file on this branch names a Huybrechts coordinate. (The handoff's earlier claim that none did was wrong at the time — it is true now.) |
| 6 | Spherical disclaimer incomplete | **Fixed.** Now states the graded self-Ext algebra is `k ⊕ k[-2]` including `Ext¹ = 0`, and that the converse from `χ = 2` needs simplicity and Serre duality. |
| 7 | Broken reference `transform_conv_congr` | **Fixed** → `transformMapConvIso`. |

The reviewer's non-findings are accepted as stated: `b_spec` constrains `b` only
on the image of `c₁` (now said explicitly in its docstring), surjectivity of
`R.cl` is the right hypothesis, no instance-search blowup from the `abbrev`, and
the `ℕ`-indexed alternating-sum interface is appropriate. The choice-sensitivity
of the exactness obligations on `h.kernel` is noted and left as-is; see question
6 below.

---

## The review question

Every theorem in this lane is conditional, and the branch is built so the
conditions are **named declarations** rather than gaps inside proofs. The axiom
audit already answers "are the proofs closed" mechanically: all 82 new
declarations depend on exactly `[propext, Classical.choice, Quot.sound]`, and
none depends on `sorryAx`.

So the review question is:

> **Are these the right hypotheses, and does each docstring claim exactly what
> the code delivers — no more?**

A defect here looks like one of: a supplied datum that was actually provable at
the pin; a docstring that understates what a declaration assumes; a theorem
whose name suggests a geometric conclusion it does not reach.

---

## Trust boundaries — every supplied datum

Nothing in the repository constructs any of these. Each is the named form of a
geometric obligation.

| Declaration | File | What it assumes | Why it is not proved here |
|---|---|---|---|
| `FourierMukai.Correspondence` | `CategoryTheory/Triangulated/FourierMukai/Basic.lean` | Three functors in the roles of `Lp^*`, `-⊗^L-`, `Rq_*` | Mathlib has scheme fibre products but `AlgebraicGeometry/Modules/` has no pushforward functor and no derived functors; `Families.SchemeDerivedCategory` disclaims any bounded-coherent subcategory |
| `FourierMukai.ConvolutionData` | `.../FourierMukai/Convolution.lean` | Kernel convolution `conv` and the comparison iso `compIso` | This is Huybrechts Prop. 5.10; proving it needs the projection formula and base change, neither available |
| `K3.IntegralMukaiData` | `AlgebraicGeometry/Numerical/GrothendieckGroup/MukaiVector.lean` | `Λ` with an integral symmetric form, a lattice-valued `c₁`, and `b_spec` | Needs `NS(X)` with its intersection form; Layer B. **The third Mukai coordinate is no longer assumed** — `mukaiSInt` derives it |
| `NumericalRealization` | `.../GrothendieckGroup/Realization.lean` | The class map `K₀ 𝒯 →+ N` | Geometrically `K₀(D^b(Coh X)) → N(X)`; `D^b(Coh X)`, the Chern character of a complex, and the radical quotient on the categorical side are all absent at the pin |
| `Descends` | `.../GrothendieckGroup/Realization.lean` | `cl' ∘ K₀.map Φ = φ ∘ cl` | No functor is shown to descend |
| `PreservesEuler` | `.../GrothendieckGroup/Realization.lean` | `χ(φE, φF) = χ(E, F)` | Reduced (not discharged) by `preservesEuler_of_descends` |
| `CategoricalEulerForm` | `.../GrothendieckGroup/EulerTransfer.lean` | A biadditive `K₀ 𝒯 →+ K₀ 𝒯 →+ ℤ` | Building it from `Hom` is blocked — see "Known blocker" |
| `IsRiemannRoch` | `.../GrothendieckGroup/EulerTransfer.lean` | `(χ_cat x y : ℚ) = chi₂ (cl x) (cl y)` | Bilinear HRR. The one-variable `hirzebruch_riemannRoch` is already an axiom of the Layer A interface |
| `PreservesCategoricalEuler` | `.../GrothendieckGroup/EulerTransfer.lean` | `χ_cat` is preserved by `Φ` | What full faithfulness would give; full faithfulness is **nowhere used**, because with the form abstract there is no `Hom` for it to act on |

Total: 8 supplied data (was 9 before review finding 1).

### Two claims a reviewer should specifically not find

- **No Hodge structure exists anywhere in this repository.** The classical
  statement that a Fourier–Mukai equivalence induces a *Hodge* isometry is
  therefore not what `pairing_mukaiVector_eq_on_realized` proves. It concerns the
  lattice form alone. Check the docstring says so.
- **Adjunction is not the hypothesis for Euler preservation.** Full
  faithfulness is. `EulerTransfer.lean`'s module docstring argues this
  explicitly; verify the argument is right rather than convenient.

---

## Commit chain

Each commit depends on the previous. Order is dependency order.

1. `bcef7f4` **The abstract kernel functor** (+228)
   `FourierMukai/Basic.lean`, 18 decls.
   `Correspondence`, `transform`, `IsKernelFunctor`. That every functor in a
   suitable setting is a kernel functor is stated nowhere.
2. `f0792f7` **Convolution of kernels is supplied data** (+153)
   `FourierMukai/Convolution.lean`, 9 decls.
3. `e264911` **Kernel functors on K₀** (+184)
   `FourierMukai/GrothendieckGroup.lean`, 6 decls.
   First result not reachable by unfolding definitions.
4. `19262ca` **The Mukai vector** (+206)
   `Numerical/GrothendieckGroup/MukaiVector.lean`, 20 decls.
5. `1b2c0df` **The K₀ bridge** (+268)
   `Numerical/GrothendieckGroup/Realization.lean`, 12 decls.
6. `40fd294` **Reduce Euler preservation** (+245)
   `Numerical/GrothendieckGroup/EulerTransfer.lean` (8 decls) and
   `StabilityCondition/Foundation/TriangulatedGrothendieckFunctorial.lean`
   (3 decls).
7. `2490c5a` **The alternating sum** (+141)
   `LinearAlgebra/AlternatingSum.lean`, 6 decls.

---

## Complete declaration inventory (82)

### `CategoryTheory.Triangulated.FourierMukai` (33)

`Correspondence`, `Correspondence.mk.inj`, `Correspondence.mk.sizeOf_spec`,
`Correspondence.pull`, `Correspondence.tensor`, `Correspondence.push`,
`Correspondence.transform`, `Correspondence.transform_obj`,
`Correspondence.transform_map`, `Correspondence.transformMapIso`,
`Correspondence.transformMapIso_refl`, `Correspondence.IsKernelFunctor`,
`Correspondence.isKernelFunctor_transform`,
`Correspondence.IsKernelFunctor.of_natIso`,
`Correspondence.IsKernelFunctor.kernel`, `Correspondence.IsKernelFunctor.iso`,
`transform_isTriangulated`, `transform_additive`,
`ConvolutionData`, `ConvolutionData.mk.inj`,
`ConvolutionData.mk.sizeOf_spec`, `ConvolutionData.conv`,
`ConvolutionData.compIso`, `ConvolutionData.isKernelFunctor_transform_comp`,
`ConvolutionData.isKernelFunctor_comp`, `ConvolutionData.transformMapConvIso`,
`ConvolutionData.transformMapConvIso_refl`,
`Correspondence.transformK₀`, `Correspondence.transformK₀_eq`,
`Correspondence.transformK₀_of`, `Correspondence.K₀_map_eq_transformK₀`,
`Correspondence.K₀_map_eq_transformK₀_kernel`,
`ConvolutionData.transformK₀_conv`

### `AlgebraicGeometry.Numerical` (40)

`K3.IntegralMukaiData`, `K3.IntegralMukaiData.mk.inj`,
`K3.IntegralMukaiData.mk.sizeOf_spec`, `K3.IntegralMukaiData.c₁`,
`K3.IntegralMukaiData.s`, `K3.IntegralMukaiData.b`,
`K3.IntegralMukaiData.b_comm`, `K3.IntegralMukaiData.b_spec`,
`K3.mukaiSInt`, `K3.mukaiSInt_spec`, `K3.IntegralMukaiData.mukaiVector`,
`K3.IntegralMukaiData.mukaiVector_fst`,
`K3.IntegralMukaiData.mukaiVector_snd_fst`,
`K3.IntegralMukaiData.mukaiVector_snd_snd`,
`K3.IntegralMukaiData.pairing_mukaiVector`,
`K3.IntegralMukaiData.selfPairing_mukaiVector`,
`K3.IntegralMukaiData.chi₂_eq_neg_pairing`,
`K3.IntegralMukaiData.selfPairing_mukaiVector_eq_neg_chi₂`,
`K3.IntegralMukaiData.isSpherical_mukaiVector_iff`,
`K3.IntegralMukaiData.isIsotropic_mukaiVector_iff`,
`K3.IntegralMukaiData.expectedDim_mukaiVector`,
`NumericalRealization`, `NumericalRealization.mk.inj`,
`NumericalRealization.mk.sizeOf_spec`, `NumericalRealization.cl`,
`Descends`, `Descends.apply_of`, `Descends.of_natIso`, `PreservesEuler`,
`pairing_mukaiVector_eq_of_preservesEuler`, `selfPairing_mukaiVector_eq_of_preservesEuler`,
`isSpherical_mukaiVector_iff_of_preservesEuler`, `pairing_mukaiVector_eq_on_realized`,
`CategoricalEulerForm`, `CategoricalEulerForm.mk.inj`,
`CategoricalEulerForm.mk.sizeOf_spec`, `CategoricalEulerForm.chi`,
`IsRiemannRoch`, `PreservesCategoricalEuler`, `preservesEuler_of_descends`,
`pairing_mukaiVector_eq_on_realized_of_categorical`

### `CategoryTheory.Triangulated.K₀` (3)

`K₀.map_comp_map_eq_id`, `K₀.mapAddEquiv`, `K₀.mapAddEquiv_apply`

### `DerivedAlgGeo.LinearAlgebra` (6)

`diffRank`, `finrank_eq_finrank_ker_add_diffRank`,
`finrank_eq_diffRank_add_diffRank`, `sum_range_succ_smul_finrank`,
`sum_range_succ_smul_finrank_eq_zero`, `diffRank_eq_zero_of_subsingleton`

---

## Verification state

Run in the isolated worktree, not the shared checkout.

```bash
cd /Users/chris.dare/Personal/SourceCode/derived-alg-geo-lean-fm-gate
scripts/gates.sh
lake env lean scripts/EnumDecls.lean > /tmp/enum.txt
python3 scripts/check_audit_complete.py /tmp/enum.txt
```

`scripts/gates.sh` (full): **17 / 17 pass** — workflows, mathlib-style, build,
algebraic-geometry-audit, stability-condition-audit, dg-audit, runLinter,
nolints-ratchet, lint-style, pin, source-independence, coverage-map,
audit-complete, emit-build, emit, emission-coverage, exe-sorry.

Completeness ratchets — **no ceiling moved**:

| Library | Public | Audited | Missing | Ceiling |
|---|---:|---:|---:|---:|
| AlgebraicGeometry | 2294 | 1196 | 1098 | 1098 |
| StabilityCondition | 2967 | 2584 | 383 | 383 |
| DGCategory | 202 | 202 | 0 | 0 |

Audit registration: 57 new records in `scripts/AlgebraicGeometryAudit.lean`,
82 lines added to `scripts/StabilityConditionAudit.lean` (the sweep assigns
`DerivedAlgGeo.LinearAlgebra.*` to the StabilityCondition audit).

---

## Adversarial questions

1. Does any declaration reach a geometric conclusion its hypotheses do not
   support — in particular, does `pairing_mukaiVector_eq_on_realized` read as a
   Hodge-isometry claim anywhere it should not?
2. `EulerTransfer.lean` argues that adjunction is the wrong hypothesis and full
   faithfulness is the right one, and that neither reaches `chi₂` without
   bilinear HRR. Is that argument correct, or is there a route from adjunction
   at this layer that it misses?
3. `IntegralMukaiData.b_spec` and `.s_spec` are stated as `ℚ`-valued equations.
   Are they exactly the integrality facts a K3 supplies, or do they assume more
   (e.g. that `b` is the *full* intersection form rather than its restriction)?
4. `preservesEuler_of_descends` requires `Function.Surjective R.cl`. Is
   surjectivity of the class map the right strengthening, or does it silently
   exclude realizations that a caller would want?
5. `Correspondence.transform` is an `abbrev`, so instance search derives
   `CommShift` and `IsTriangulated` from the composite. Does that cause
   instance-search blowup at any use site, and is the unfolded goal display
   acceptable?
6. `IsKernelFunctor.kernel` uses `Exists.choose`. Does any downstream statement
   depend on *which* kernel is chosen in a way that is not invariant?
7. `sum_range_succ_smul_finrank` carries the partial sum as a rank rather than
   proving it zero. Are `hzero : ker (d 0) = ⊥` and the `ℕ` indexing the right
   interface for the eventual LES caller, or will the caller need the `ℤ`-indexed
   form after all?
8. *(Answered by review: yes, it violates it.)* See "Owner decision: the K₀
   layering" below.

---

## Known blocker: constructing `CategoricalEulerForm` from `Hom`

Investigated 2026-08-15; not attempted. Two Mathlib-level instances are missing.

| Functor | Target | `IsHomological` | `ShiftSequence ℤ` |
|---|---|---|---|
| `preadditiveYoneda` | `AddCommGrpCat` | yes | yes |
| `linearYoneda k C` | `ModuleCat k` | **absent** | **absent** |

`preadditiveYoneda : C ⥤ Cᵒᵖ ⥤ AddCommGrpCat` lands in abelian groups, so
`finrank k` is not statable. `linearYoneda R C : C ⥤ Cᵒᵖ ⥤ ModuleCat R` has the
right target but neither instance exists anywhere in Mathlib — it appears only
in `CategoryTheory/Linear/Yoneda.lean`, `CategoryTheory/Abelian/Ext.lean`, and
four `RepresentationTheory` files.

Work required, in order:

1. `((linearYoneda k C).obj B).IsHomological` — plausibly via
   `IsHomological.mk'` reflecting exactness along the faithful exact forgetful
   `ModuleCat k ⥤ AddCommGrp`, borrowing `preadditiveYoneda`'s instance.
2. `((linearYoneda k C).obj B).ShiftSequence ℤ` — the expensive one. Mathlib's
   `preadditiveYoneda` analogue (`CategoryTheory/Triangulated/Yoneda.lean:78`)
   is ~12 lines of `ShiftedHom.opEquiv'` plumbing; the k-linear version must
   redo it in `ModuleCat k` and prove k-linearity of each equivalence.
3. Collapse the 3-periodic ℤ-graded LES (Mathlib gives
   `homologySequence_exact₁/₂/₃` per index) into the ℕ-indexed family
   `V : ℕ → Type` with `d i : V i →ₗ[k] V (i+1)` that
   `LinearAlgebra/AlternatingSum.lean` consumes. Needs `V` by cases on `i % 3`
   and `ShortComplex.Exact` in `ModuleCat` converted to
   `LinearMap.ker = LinearMap.range`.
4. Hom-finiteness and boundedness hypotheses, triangle-additivity in each
   variable, then `K₀.lift` twice.

Items 1 and 2 are generally useful and arguably belong upstream in Mathlib
rather than in this repository. Recommend deciding that before starting.

---

## Owner decision: the K₀ layering (review finding 3)

`CategoryTheory/Triangulated/FourierMukai/GrothendieckGroup.lean:6` imports
`StabilityCondition/Foundation/TriangulatedGrothendieckFunctorial`. The reviewer
is right that confining and documenting the dependency does not change its
direction: a generic module points at a specialized one, against the CLAUDE.md
rule.

This was **not** fixed, because the honest fix is a `main`-owned refactor and the
shared checkout has active concurrent branches. The concrete plan, should the
owner want it:

Move `Foundation/TriangulatedGrothendieck.lean` and
`Foundation/TriangulatedGrothendieckFunctorial.lean` to
`CategoryTheory/Triangulated/GrothendieckGroup/`. Blast radius is 6 importing
files:

- `FourierMukai/GrothendieckGroup.lean` (this branch)
- `StabilityCondition/Foundation.lean`
- `StabilityCondition/Foundation/TriangulatedGrothendieckFunctorial.lean`
- `StabilityCondition/Foundation/PreStabilityCondition.lean`
- `StabilityCondition/Foundation/Deformation/PhaseSum.lean`
- `StabilityCondition/Families/BaseChange.lean`

Declaration names do not change, so both audits keep resolving. The risk is
collision: `Families/BaseChange.lean` sits in the area issue #429 is currently
working. Recommend sequencing this after #429 lands, as its own commit.

The cheaper alternative the reviewer offered — moving the bridge into the
specialized layer — was rejected as conceptually wrong: `transformK₀` is
categorical, not stability-specific, and burying it under `StabilityCondition`
would misfile it to satisfy a lint.

---

## Owner decision: pinning Huybrechts

`registry/` pins every source as an arXiv ID with a version, and
`registry/README.md` states that `bridgeland2007.json` is the only mint
surface. The source behind this lane is *Fourier–Mukai Transforms in Algebraic
Geometry* (Huybrechts, Oxford Mathematical Monographs, 2006) — a copyrighted
monograph, not an arXiv preprint.

**Correction (review finding 5).** An earlier draft of this handoff claimed no
Lean file on this branch cites Huybrechts. That was wrong. Five docstrings cite
"Huybrechts, Prop. 5.10":

- `FourierMukai/Basic.lean` (module docstring, in the not-asserted list)
- `FourierMukai/Convolution.lean` (module docstring and `conv` field doc)
- `FourierMukai/GrothendieckGroup.lean` (module docstring and `transformK₀_conv`)

No coverage map was added and no registry key was minted, so no *coverage* is
claimed — but the coordinates are in the source tree.

Relevant precedent: `Numerical/Core/Definitions.lean` on `main` already cites
Huybrechts–Lehn §1.1 and §2.1 in a References section, unpinned. So informal
docstring references to textbooks are existing practice, and `registry/` governs
coverage claims rather than bibliography.

**Resolved: the owner chose to strip.** All five coordinates are removed; the
docstrings now refer to "the classical composition law" without a citation. No
Lean file on this branch names a Huybrechts coordinate, so no pin is needed for
this branch to merge.

The general question is untouched and will return with the next textbook-sourced
lane: whether `registry/` should gain a non-arXiv pin kind (ISBN + edition + PDF
sha256), or whether unpinned docstring bibliography stays acceptable as the
`main` precedent suggests.

For reference: the full text has been ingested into the `bridgeland-stability`
arXMCP notebook as `paper_id: textbook:huybrechts-fm`, 692 chunks, retrievable
with `filters.source_kind="textbook"`. That corpus is a search aid only —
per `registry/README.md`'s existing discipline, quotes must be checked against
the pinned artifact, never against the corpus.

---

## Operational hazards

1. **Uncommitted work is parked in a stash.** `stash@{0}` — "divisor-probe WIP
   (parked by FM branch split)", 4 files, 76 deletions, belonging to
   `agent/retire-divisor-api-probe`. It was stashed to gate this branch in
   isolation and deliberately not restored: the main checkout had moved to
   another branch, and popping would have dropped those changes into a
   different session's working tree. Restore with `git stash pop` from
   `agent/retire-divisor-api-probe` when the checkout is free.

2. **The main checkout is shared with autonomous sessions.** During this work a
   `formalize-issue` run switched the shared checkout from this branch to
   `main` to `agent/issue-340-cech-differential` mid-verification, invalidating
   a gate run and producing a spurious `audit-complete` failure (it was
   measuring `main`'s tree, not this branch's). Every figure in this handoff
   was re-established afterwards in the dedicated worktree. Per-agent
   worktrees would remove this class of failure entirely.
