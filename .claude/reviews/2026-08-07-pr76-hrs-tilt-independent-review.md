# Independent review — PR #76's Hom-orthogonal HRS tilt (issue #86)

**Reviewer:** Claude (Fable 5), a Claude Code session with no overlap with PR
#76's authoring session. Machine review, not human review: this document does
**not** move any `human_review` field, and it does not substitute for the
registry-faithfulness review in #51 (`faithfulness` is the human-only axis,
ADR-0005). Owner sign-off is a separate, explicit act — see the last section.

**Date:** 2026-08-07.

## What exactly was reviewed

| pin | value |
|---|---|
| PR #76 merge commit | `a3bfb8af33741b8b7fe195828cae39f63259816e` |
| `main` at review time | `418d423333e022ab720a5d6ddb7fed966d05c656` |
| blob of `BridgelandStabLean/Tilting/HeartTorsionPair.lean` | `3d79b754ed496e28c16fc0133c60fcdfb45ada43` |

The blob is byte-identical at the merge commit and at current `main` (last
touched by `aefd57b`, inside the PR), so every statement below binds to both.
Mathlib conventions were checked against the pinned checkout under
`.lake/packages/mathlib` (the `8a178386ffc0…` revision that arrives through the
anchor), by reading the source, not from memory.

## Verdict up front

**Every declaration in the module is mathematically correct, and the assembled
`tilt` is the Happel–Reiten–Smalø t-structure it claims to be.** The shift and
sign conventions are right, both octahedra are the right flavour and are
applied to the right triangles, and the Hom-orthogonal aisles agree with the
textbook `H⁰` aisles wherever the latter can be stated. Three findings, none
of which is an error in a Lean statement: two are prose/disclosure gaps
(F1, F2), one is an upstream boundary worth recording (F3). Dispositions:
one fixed-in-flight elsewhere, one separately tracked, one accepted boundary.

## Axis 1 — shift and sign conventions in `tiltLEAt` / `tiltGEAt`

Checked against the pin's `TStructure` (`Triangulated/TStructure/Basic.lean`)
and `ObjectProperty.shift` (`ObjectProperty/Shift.lean`):

- `ObjectProperty.shift a P = fun X => P (X⟦a⟧)`, and `TStructure.shift_le`
  gives `t.le n X ⟺ t.le 0 (X⟦n⟧)`. So the ambient convention is
  `X ∈ D^{≤n} ⟺ X⟦n⟧ ∈ D^{≤0}`, and dually for `ge`.
- `tiltLEAt n X := t.IsLE X n ∧ P.torsOrth (X⟦n⟧)` — both conjuncts express
  `X⟦n⟧ ∈ tiltLE` under that convention. **Consistent.**
- `tiltGEAt n X := t.IsGE X (n-1) ∧ P.freeOrth (X⟦n-1⟧)` — both conjuncts
  express `X⟦n-1⟧ ∈ tiltGE`, and `tiltGE` is the level-**one** member, which
  `tiltGEAt_one_iff` states and proves. The `n-1` offset is exactly the
  textbook `D†^{≥0} = {X ∈ D^{≥-1} : H^{-1}X ∈ F}` re-indexed. **Consistent.**
- The two shift theorems transport the orthogonality clause with
  `shiftFunctorAdd' C a n' n h : shiftFunctor C n ≅ shiftFunctor C a ⋙ shiftFunctor C n'`
  applied in the correct direction (`X⟦n⟧ ≅ X⟦a⟧⟦n'⟧`, then
  `prop_of_iso`); the degree conjunct uses Mathlib's `isLE_shift`/`isGE_shift`
  with the same `a + n' = n` bookkeeping the `TStructure` field demands.
- Every field signature of `tilt` was compared one-for-one against the
  structure fields of `TStructure` at the pin: `le`, `ge`, both
  isomorphism-closure fields, `le_shift`, `ge_shift`, `zero'`, `le_zero_le`,
  `ge_one_le`, `exists_triangle_zero_one`. All match, including the
  strict-implicit binders on `zero'`.

## Axis 2 — the two octahedra in `exists_tilt_triangle`

Traced by hand against the pin's `Octahedron` and `Octahedron'`
(`Triangulated/Triangulated.lean`). The `mem` fields there are:

- `Octahedron'` (fibres): given `u₁₂ : X₁ ⟶ X₂`, `u₂₃ : X₂ ⟶ X₃` with fibres
  `Z₁₂, Z₂₃, Z₁₃` of `u₁₂`, `u₂₃`, `u₁₂ ≫ u₂₃`, its `mem` is
  `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧` distinguished.
- `Octahedron` (cones): dually, `mem` is the triangle of cones
  `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃ ⟶ Z₁₂⟦1⟧`.

In `exists_tilt_triangle_of_data`:

1. `someOctahedron' rfl hZBH hTHF hXBF` instantiates `u₁₂ = bh : B ⟶ H`,
   `u₂₃ = hf : H ⟶ F₀`, with fibres `Z` (of `bh`), `T₀` (of `hf`), `X` (of
   `bh ≫ hf`, produced by `distinguished_cocone_triangle₁`). Its `mem` is
   therefore `Z ⟶ X ⟶ T₀ ⟶ Z⟦1⟧` — **exactly** the shape
   `tiltLEAt_zero_of_triangle` consumes with `hZ : IsLE Z (-1)`,
   `hT : tors T₀`. No desuspension, as the module comment claims.
2. `someOctahedron rfl hXBF hBAW hXAY` instantiates `u₁₂ = xb : X ⟶ B`,
   `u₂₃ = ba : B ⟶ A`, with cones `F₀` (of `xb`), `W` (of `ba`), `Y` (of
   `xb ≫ ba`, produced by `distinguished_cocone_triangle`). Its `mem` is
   `F₀ ⟶ Y ⟶ W ⟶ F₀⟦1⟧` — **exactly** what `tiltGEAt_one_of_triangle`
   consumes with `hF : free F₀`, `hW : IsGE W 1`.
3. The returned truncation triangle is `hXAY : X ⟶ A ⟶ Y ⟶ X⟦1⟧` with
   `f = xb ≫ ba`, matching `exists_triangle_zero_one`'s shape.

In `exists_tilt_triangle` the data are `B = τ^{<1}A` (with `IsLE B 0`),
`W = τ^{≥1}A`, `Z = τ^{<0}B` (with `IsLE Z (-1)`), `H = τ^{≥0}B` — in the
heart because the octahedral axiom makes `τ^{≥0}` preserve `D^{≤0}`, which is
one of the three uses of `[IsTriangulated C]` the docstring enumerates; I
confirmed all three (that instance, plus the two `someOctahedron` calls) and
found no fourth. The torsion decomposition of `H` is `P.exists_triangle`.
All hypotheses line up; the construction is the standard HRS truncation,
built in the fibre-flavoured order that avoids sign bookkeeping.

The "correction I got wrong twice" narrative in the module was also checked
mathematically: cutting `X` as the fibre of `τ^{≤0}A ⟶ F₀` genuinely does
require `H⁰(A) ⟶ F₀` epi for `IsLE X 0` (the degree count alone leaves
`Hom(X,Z) ↪ Hom(F₀⟦-1⟧, Z)`, which does not vanish for degree reasons), while
the extension-of-`T₀`-by-`τ^{≤-1}A` shape puts both ends in `D^{≤0}` and
closes with `isLE₂`. The recorded reasoning is sound.

## Axis 3 — aisle-recognition lemmas, closure and orthogonality fields

Each verified against the pin's lemma statements (`yoneda_exact₂/₃`,
`coyoneda_exact₂` in `Pretriangulated.lean`; `isLE₂`/`isGE₂` in
`TruncLTGE.lean`; `zero_of_isLE_of_isGE` in `TStructure/Basic.lean`):

- `tiltLE_of_triangle`: degree half by `isLE₂` (both ends in `D^{≤0}`);
  orthogonality half factors `u : X ⟶ F'` through `T₀` via `yoneda_exact₂`
  (the `Z ⟶ F'` leg dies by degrees, `(-1) < 0`), then kills it with
  `hom_eq_zero`. Correct, and the correct direction of the torsion axiom
  (torsion → torsion-free).
- `tiltGE_of_triangle`: exact dual via `coyoneda_exact₂`; the `T ⟶ W` leg
  dies by degrees (`0 < 1`). Correct.
- `tors_of_orthogonal`: decomposes `A`, notes the map to the free part is
  zero by hypothesis, extracts `𝟙 Y = d ≫ k` from `yoneda_exact₃`, kills `k`
  by degrees (`T⟦1⟧ ∈ D^{≤-1}` vs `Y ∈ D^{≥0}`), concludes `Y ≅ 0`, hence
  `i` iso by `isZero₃_iff_isIso₁`, hence `A` torsion by isomorphism-closure.
  This is the correct "the torsion class is the left orthogonal of `F`
  inside the heart" converse, and it is where the decomposition axiom earns
  its place, as the section comment says.
- `exists_factor_truncGE` / `factor_truncGE_unique`: together these are
  exactly the counit bijection `Hom(τ^{≥0}X, F) ≅ Hom(X, F)` for
  `F ∈ D^{≥0}` — existence from `yoneda_exact₂` (the `τ^{<0}X` leg dies by
  degrees), uniqueness from `yoneda_exact₃` (the `(τ^{<0}X)⟦1⟧` leg dies by
  degrees). The docstring's claim that no hypothesis on `X` is needed is
  correct.
- `hom_eq_zero_of_tiltLE_of_tiltGE`: factors `f` through `τ^{≥0}X`,
  transports orthogonality along the factorisation (using uniqueness), lands
  it in the torsion class via `tors_of_orthogonal`, kills it with the
  aisle's own orthogonality. Correct, and genuinely cohomology-functor-free.
- All six isomorphism-closure instances (`tiltLE`, `tiltGE`, `torsOrth`,
  `freeOrth`, `tiltLEAt`, `tiltGEAt`): mechanical conjugation by `e.hom`/
  `e.inv`, the indexed ones mapping the iso through the shift functor.
  Correct.
- The two inclusions (`tiltLEAt_zero_le`, `tiltGEAt_one_le`): pure degree
  counts, and the module's observation that neither uses the orthogonality
  hypothesis it discards is true — mathematically because `H¹` (resp.
  `H^{-1}`) of an object of `D^{≤0}` (resp. `D^{≥0}`) vanishes, so the
  membership clause is automatic one level out.
- `HeartTorsionPair` itself: a faithful in-`C` rendering of a torsion pair on
  the heart — both classes inside the heart, isomorphism-closed,
  `Hom(T,F) = 0`, decomposition triangle oriented torsion-subobject-first,
  matching the textbook SES orientation.

## Axis 4 — Hom-orthogonality vs the textbook `H⁰` formulation

The mathematical claim ("the two agree wherever the textbook one can be
stated") is **true**, and at the pin the textbook side is statable with
`τ^{≥0}` standing in for `H⁰` (Mathlib has no cohomology functor for a
t-structure at the pin; the anchor's `H0Functor` has its homological property
only as fragments — both accurately described in the module docstring).

For the co-aisle: for `X ∈ D^{≤0}`, `τ^{≥0}X` is in the heart, the counit
bijection is `exists_factor_truncGE` + `factor_truncGE_unique`, and
`tors_of_orthogonal` + `hom_eq_zero` give
`P.tors (τ^{≥0}X) ⟺ P.torsOrth X`. Every ingredient is in the file; the
proof of `hom_eq_zero_of_tiltLE_of_tiltGE` literally walks through the
forward half. **See F1**: the equivalence itself is not stated as a named
theorem, and on the aisle side the dual ingredients are absent.

## Axis 5 — the missing extension-closure description of the tilted heart

Confirmed genuinely absent, and confirmed disclosed in all three places a
reader would look: the module's "What is still not here" section, README lane
4 ("Nothing … identifies the tilted heart with the extension closure of `T`
and `F⟦1⟧`"), and the PR body. No Lean statement implies otherwise. The
related disclosed absence of `free_of_orthogonal` is also real (checked: the
name does not exist in the repo) and is correctly described as not being a
`TStructure` field obligation.

## Axis 6 — axiom output and dependency boundary

- The module imports `Mathlib.CategoryTheory.Triangulated.TStructure.Heart`,
  `….TruncLEGT`, and `Mathlib.Tactic` — **no anchor import**. The tilt is a
  pure-Mathlib construction; nothing in it can disagree with the anchor about
  anything.
- `scripts/Audit.lean` gained exactly the 8 records PR #76 claims
  (`tiltLEAt_isClosedUnderIsomorphisms`, `tiltGEAt_isClosedUnderIsomorphisms`,
  `exists_tilt_triangle_of_data`, `exists_tilt_triangle`, `tilt`, `tilt_le`,
  `tilt_ge`, `tilt_le_zero_iff`), matching the file's declaration diff
  one-for-one. The audit caveat that `tilt` is a `def` whose clean axiom line
  reports the closure of a construction is correctly recorded in
  `scripts/Audit.lean` and `formalization.yaml`.
- Audit run at review time: **ok, 667 declarations, all within
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`** — matching the
  PR's post-merge claim of 667.
- No `sorry` anywhere in the module (checked; also enforced repo-wide by the
  audit's `sorryAx` gate).

## Every declaration inspected

All 34 declarations of `BridgelandStabLean.Tilting.HeartTorsionPair`, in file
order. ✔ = read line-by-line and checked mathematically against the pin's
Mathlib API. Bracketed tags: [76] = added by PR #76; the rest predate the PR
in the same module and are inside this review's scope because the tilt is
assembled from them.

| declaration | verdict |
|---|---|
| `HeartTorsionPair` (structure, 10 fields) | ✔ faithful torsion-pair-on-heart datum |
| `tiltLE` | ✔ correct `D†^{≤0}` |
| `tiltGE` | ✔ correct `D†^{≥1}` (level-one member, as documented) |
| `tiltLE_isClosedUnderIsomorphisms` | ✔ |
| `tiltGE_isClosedUnderIsomorphisms` | ✔ |
| `exists_factor_truncGE` | ✔ counit surjectivity, no hypothesis on `X` needed |
| `factor_truncGE_unique` | ✔ counit injectivity |
| `tors_of_orthogonal` | ✔ orthogonal-implies-torsion converse |
| `hom_eq_zero_of_tiltLE_of_tiltGE` | ✔ the `zero'` content |
| `torsOrth` | ✔ |
| `freeOrth` | ✔ |
| `torsOrth_isClosedUnderIsomorphisms` | ✔ |
| `freeOrth_isClosedUnderIsomorphisms` | ✔ |
| `tiltLEAt` | ✔ convention-consistent (Axis 1) |
| `tiltGEAt` | ✔ convention-consistent, `n-1` offset correct |
| `tiltLEAt_zero_iff` | ✔ |
| `tiltGEAt_one_iff` | ✔ |
| `tiltLEAt_shift` | ✔ correct `shiftFunctorAdd'` direction |
| `tiltGEAt_shift` | ✔ correct `shiftFunctorAdd'` direction |
| `tiltLEAt_zero_le` | ✔ degree count; orthogonality hypothesis genuinely unused |
| `tiltGEAt_one_le` | ✔ degree count; orthogonality hypothesis genuinely unused |
| `tiltAt_zero'` | ✔ transport of `zero'` to the indexed families |
| `tiltLE_of_triangle` | ✔ co-aisle recognition |
| `tiltGE_of_triangle` | ✔ aisle recognition |
| `tiltLEAt_zero_of_triangle` | ✔ |
| `tiltGEAt_one_of_triangle` | ✔ |
| `exists_tilt_triangle_of_data` [76] | ✔ both octahedra correct (Axis 2) |
| `exists_tilt_triangle` [76] | ✔ correct instantiation, `IsTriangulated` earned 3× |
| `tiltLEAt_isClosedUnderIsomorphisms` [76] | ✔ |
| `tiltGEAt_isClosedUnderIsomorphisms` [76] | ✔ |
| `tilt` [76] | ✔ all ten `TStructure` fields matched against the pin |
| `tilt_le` [76] | ✔ `rfl` |
| `tilt_ge` [76] | ✔ `rfl` |
| `tilt_le_zero_iff` [76] | ✔ `Iff.rfl` sanity check, honestly labelled |

## Findings and dispositions

**F1 — the aisle-side textbook agreement is prose-only, and one of its two
missing ingredients is undisclosed.** The module and README claim both aisles
agree with the textbook `H⁰` formulation wherever statable. For the co-aisle
this is fully backed by formalized ingredients (Axis 4), though the
equivalence `t.IsLE X 0 → (P.torsOrth X ↔ P.tors ((t.truncGE 0).obj X))` is
statable at the pin and not stated. For the aisle side (`H⁰(X) ∈ F` for
`X ∈ D^{≥0}`), the two ingredients — the dual factorisation through
`τ^{≤0}` and `free_of_orthogonal` — are both absent; the absence of
`free_of_orthogonal` is disclosed, the absence of the dual factorisation is
not. No Lean statement overclaims; the gap is between prose and formalized
support. *Severity: low. Disposition: **separately tracked** — issue #94, for the
named agreement lemma and, optionally, the dual pair.*

**F2 — live trust text on `main` still denies the tilt exists.**
`formalization.yaml` at `418d423`, scope note (~line 35): "The Tilting lane
does NOT contain the Happel-Reiten-Smalo tilt." This contradicts merged PR
#76, whose body claims all such text was removed. *Severity: medium for
trust-record coherence, zero for the mathematics. Disposition: **separately
tracked and already in flight** — issue #85 (reconcile trust prose after
#71/#76/#78) covers exactly this line, and a working session on branch
`trust/audit-count-670` was actively editing `formalization.yaml` during this
review.*

**F3 — the SES ↔ triangle gloss is not formalizable at the pin.** The
`HeartTorsionPair` docstring says the decomposition triangle "for objects of
the heart is the same thing as a short exact sequence there." True (BBD), but
not statable at the pin: Mathlib's own `TStructure/Basic.lean` header lists
"show that the heart of `t` is an abelian category" as TODO, so there is no
abelian structure on the heart to state an SES in. This is precisely why
phrasing the datum inside `C` is not just convenient but forced — the
docstring could say so, and the stronger justification is worth having.
*Severity: cosmetic. Disposition: **accepted boundary** (upstream gap;
recorded here).*

No finding touches the correctness of any Lean statement or proof. Nothing
in the module connects the tilt to stability conditions or geometry, matching
the issue's non-goals; I looked for implicit claims of that kind and found
none.

## Nonvacuity check

`HeartTorsionPair` had no instance anywhere in the repo, so the review built
one: the degenerate pair on the heart of **any** t-structure (`tors` = the
whole heart, `free` = the zero objects), with the contractible triangle as
decomposition. Its tilt exists, and its co-aisle is proved to be the original
`t.le` at every level, through the assembled `tilt` itself.

Source: [`2026-08-07-TiltNonvacuity.lean`](2026-08-07-TiltNonvacuity.lean)
(kept beside this review because `/scratch/` is deliberately gitignored).
Reproduce with:

```
cp .claude/reviews/2026-08-07-TiltNonvacuity.lean scratch/TiltNonvacuity.lean
lake env lean scratch/TiltNonvacuity.lean
```

Observed at review time: exit 0, no output. Scope stated honestly: this
certifies the datum and the construction are nonvacuous for every
t-structure; it does not exhibit a *nontrivial* torsion pair, and none is
available at the pin (that would need a concrete heart, which is behind the
closed geometric lane).

## Build/CI evidence — separate from the mathematics

Recorded separately, per the acceptance criteria; none of these can tell
whether a statement says what it should.

| gate | result | where |
|---|---|---|
| CI on merge commit `a3bfb8a` | success | run 31219222510 |
| CI on `main` `418d423` | success | run 31225686077 |
| `lake build` (local, review day) | exit 0, 3786 jobs | this machine |
| `lake exe runLinter BridgelandStabLean` (local) | clean | this machine |
| audit + `check_audit.py` (local) | ok: 667 declarations, allowlist only, no `sorryAx` | this machine |
| nonvacuity example elaboration (local) | exit 0 | this machine |

Local-run caveat, recorded for honesty: a concurrent session was moving the
same checkout between commits during this review (all between `a3bfb8a` and
`418d423`+docs). The reviewed module's blob and its import closure are
identical across that range, so the per-module evidence binds; the
authoritative whole-tree evidence is the two CI runs above.

## Owner sign-off

This review is machine-produced and does not constitute owner sign-off.

- [x] Owner has read the findings and accepts the dispositions of F1–F3.
  Sign-off given by the owner on 2026-08-07: first as the instruction to merge
  PR #93 and close #86, then as the explicit instruction to tick this box
  (recorded in the #86 closing comment).

`reviewer: claude-fable-5 (Claude Code), session independent of PR #76`
`reviewed_at: 2026-08-07`
