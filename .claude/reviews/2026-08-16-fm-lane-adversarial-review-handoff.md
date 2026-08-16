# Fourier–Mukai lane — adversarial review handoff

**Audience:** a reviewing agent. Not a human summary.
**Target:** `origin/main` @ `aaa3cfe` (repo `chris-dare-dev/derived-alg-geo-lean`).
**Task:** find shortcomings and inconsistencies. Everything below is merged, so
a finding is a defect in `main`, not a PR comment.

## How to check out and build

```bash
cd /Users/chris.dare/Personal/SourceCode/derived-alg-geo-lean
git fetch origin
git worktree add -b review/fm-lane /tmp/fm-review origin/main
cp -c -R .lake /tmp/fm-review/.lake     # APFS clone, ~20s; avoids a Mathlib rebuild
cd /tmp/fm-review && lake build && scripts/gates.sh
```

Do **not** work in `/Users/chris.dare/Personal/SourceCode/derived-alg-geo-lean`
itself. It is a shared checkout that autonomous `formalize-issue` sessions
switch branches in mid-run; a verification pass there was silently invalidated
during development of this lane. Use your own worktree.

## What the lane claims

Six merged PRs, in dependency order:

| PR | Merge | Content |
|---|---|---|
| #449 | `cefc244` | Kernel functor, convolution, K₀, Mukai vector, realization, Euler transfer, alternating sum |
| #454 | — | Generic Grothendieck-group API relocated out of `StabilityCondition/` (closes #453) |
| #457 | `5a20019` | Kernel functors act on stability conditions; dual kernel |
| #466 | `0149ef6` | Composition: two transports = one, by the convolved kernel |
| #470 | `aaa3cfe` | The k-linear Yoneda functor is homological |

End-to-end claim: *a kernel functor transports a Bridgeland stability
condition; both directions are computed by kernels; composing two transports is
the transport by the convolved kernel.*

## Files

```
CategoryTheory/Triangulated/FourierMukai/{Basic,Convolution,GrothendieckGroup}.lean
CategoryTheory/Triangulated/GrothendieckGroup/{Basic,Functorial,Presentation}.lean
CategoryTheory/Triangulated/PostnikovTower.lean
CategoryTheory/Triangulated/LinearYoneda.lean
CategoryTheory/Triangulated/StabilityCondition/Symmetry/Autoequivalence/FourierMukai.lean
CategoryTheory/Triangulated/StabilityCondition/Symmetry/Autoequivalence/Stability/Composition.lean
AlgebraicGeometry/Numerical/GrothendieckGroup/{MukaiVector,Realization,EulerTransfer}.lean
LinearAlgebra/AlternatingSum.lean
```

Approximate new declaration counts: `FourierMukai.*` 33, `KernelAutoequivalence.*`
27, `IntegralMukaiData.*` 18, `DerivedAlgGeo.LinearAlgebra.*` 6,
`linearYoneda_*` 2.

## The review question

Every theorem here is conditional. The design intent is that each condition is
a **named declaration** rather than a gap inside a proof. Axiom closure is
already settled mechanically — every declaration in the lane depends on exactly
`[propext, Classical.choice, Quot.sound]`, none on `sorryAx`; re-verify with

```bash
lake env lean scripts/StabilityConditionAudit.lean 2>&1 | grep -i sorryAx
lake env lean scripts/AlgebraicGeometryAudit.lean  2>&1 | grep -i sorryAx
```

So the question is **not** "do the proofs close". It is:

> Are these the right hypotheses, and does each docstring and each declaration
> name claim exactly what the code delivers — no more?

## Known defect classes — round 1 found one of each

A first review (before #466/#470) requested changes and found seven items.
Five were fixed, two became owner decisions. **The two P1s are the pattern to
hunt for again**:

1. **A supplied datum that was actually provable at the pin.**
   `IntegralMukaiData` carried `s : N → ℤ` and `s_spec` as fields. Under
   `[IsK3]`, the repo's own `chi_eq_rank_add_mukaiS` already proves
   `χ(E) = r(E) + mukaiS E`, so the third Mukai coordinate was a theorem
   dressed as geometry. Now `K3.mukaiSInt` is a `def` and `mukaiSInt_spec` a
   theorem. **Check the remaining supplied data the same way.**

2. **A name claiming more than the statement.** Results were called isometries
   of Mukai lattices. They are equalities of *pairings*; no map
   `MukaiLattice Λ → MukaiLattice Λ'` is constructed, `mukaiVector` and `c₁`
   are bare functions (not additive), and nothing is claimed off the image.
   Renamed to `..._eq_of_preservesEuler` / `..._eq_on_realized`. **Check every
   remaining name against its statement.**

Also fixed in round 1: a missing `k`-linearity caveat in the full-faithfulness
argument; an incomplete spherical-object disclaimer (`Ext¹ = 0` was omitted);
a dangling docstring reference.

Round 1's non-findings, accepted and *not* worth re-deriving: `b_spec`
constrains `b` only on the image of `c₁` (now said explicitly); surjectivity of
`R.cl` is the right hypothesis for global `PreservesEuler`; no instance-search
blowup from the `transform` abbrev; the ℕ-indexed alternating-sum interface is
appropriate after reindexing.

## Trust boundaries — every supplied datum, verify none is provable

Nothing in the repository constructs any of these.

| Declaration | File |
|---|---|
| `FourierMukai.Correspondence` | `FourierMukai/Basic.lean:68` |
| `FourierMukai.ConvolutionData` | `FourierMukai/Convolution.lean:76` |
| `K3.IntegralMukaiData` | `Numerical/GrothendieckGroup/MukaiVector.lean:106` |
| `NumericalRealization` | `Numerical/GrothendieckGroup/Realization.lean:103` |
| `Descends` | `Realization.lean:121` |
| `PreservesEuler` | `Realization.lean:160` |
| `CategoricalEulerForm` | `EulerTransfer.lean:92` |
| `IsRiemannRoch` | `EulerTransfer.lean:118` |
| `PreservesCategoricalEuler` | `EulerTransfer.lean:129` |
| `KernelAutoequivalence` | `Symmetry/Autoequivalence/FourierMukai.lean:74` |
| `DualKernel` | `Symmetry/Autoequivalence/FourierMukai.lean:135` |

For each: **is it genuinely unprovable at the pin, or is it another `s`?**
`IntegralMukaiData.b_spec` and `KernelAutoequivalence.iso` are the two I would
attack first.

## Specific claims to attack

1. **`transformK₀_dual_comp` provenance.** The docstring insists the
   mutual-inverse result follows from the *supplied equivalence*, not from an
   identity-kernel relation `conv P P^∨ ≅ 𝒪_Δ`, and that no `ConvolutionData`
   is involved. Verify by inspecting the proof term.
2. **`actStab_trans` is claimed to be only the associativity clause** of an
   action — no identity law, no group. Confirm nothing elsewhere implies a
   `MulAction` is nearly present.
3. **`@[reducible] KernelAutoequivalence.trans`.** Justified by a dependent
   instance mismatch (`IsTriangulated` is indexed by the `CommShift` term).
   Check that reducibility does not cause instance-search blowup at use sites,
   and that the stated reason is the real one.
4. **`Slicing.mapEquiv_trans` is `Slicing.ext` on `rfl`.** Depends on
   `(Φ.trans Ψ).inverse` being `Ψ.inverse ⋙ Φ.inverse` definitionally. If that
   is fragile across a Mathlib bump, say so.
5. **`LinearYoneda.lean` claims `finrank` is not statable in `AddCommGrpCat`**
   and therefore that `preadditiveYoneda` cannot feed a `k`-dimension count.
   Verify that framing.
6. **`AlternatingSum.lean` boundary hypotheses.** `hzero : ker (d 0) = ⊥` plus
   exactness at every positive index plus `hstop`. Check the ℕ-indexing
   rationale in the docstring survives contact with a real ℤ-indexed LES; the
   claim is that a caller reindexes once at the boundary.
7. **Two claims that should appear nowhere.** No Hodge structure exists in this
   repository, so nothing may be a Hodge-isometry result; and adjunction is
   *not* the hypothesis for Euler preservation (full faithfulness plus
   `k`-linearity is). Grep for backsliding.

## Layering

#454 relocated `K₀` and friends out of `StabilityCondition/Foundation/` so that
generic modules stop importing a specialized one. Verify the invariant now
holds:

```bash
grep -rn "import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition" \
  DerivedAlgGeo/CategoryTheory/ | grep -v "/StabilityCondition/"
```

Expected: only `Symmetry/Autoequivalence/FourierMukai.lean` and
`Stability/Composition.lean`, both of which *are* stability-track files, plus
the `StabilityCondition` umbrella. Anything else is a regression.

Note the scope correction #454 had to make: the issue scoped two files, the
real answer was four — `TriangulatedGrothendieck` also pulled in
`GrothendieckPresentation` and `PostnikovTower`, both generic and both
misfiled. Check nothing else in `Foundation/` is similarly misfiled.

## Open, documented, not defects

- **#469** — `ShiftSequence ℤ` for the k-linear Yoneda. Three Mathlib gaps,
  file-and-line precise: `Linear R Cᵒᵖ` does not exist; `opEquiv_symm_smul` /
  `opEquiv'_symm_smul` do not exist; then the instance. Until these land,
  `CategoricalEulerForm` stays supplied. Both `LinearYoneda.lean` and
  `EulerTransfer.lean` say so.
- **#480** — the audit files are a single append-point; concurrent PRs conflict
  there structurally. #466/#470 collided exactly this way.
- **Geometry** — `D^b(Coh X)`, the Chern character of a complex, the class map
  `K₀(D^b Coh X) → N(X)`. Issues #460/#461/#462 are in flight on that substrate.

## Verification baseline to reproduce

```
scripts/gates.sh            17/17 pass
AlgebraicGeometry ratchet   2351 public, 1253 audited, 1098 missing, ceiling 1098
StabilityCondition ratchet  3265 public, 2882 audited,  383 missing, ceiling  383
DGCategory ratchet           202 public,  202 audited,    0 missing, ceiling    0
```

Ratchet ceilings must not have moved. If your changes raise one, that is the
finding.

## Report format

Rank findings P1/P2/P3. For each: file and line, what is claimed, what is
delivered, and the smallest change that closes the gap. Prefer "this name
overclaims" and "this datum is provable" over stylistic notes — round 1's two
P1s were both of those kinds, and both were real.
