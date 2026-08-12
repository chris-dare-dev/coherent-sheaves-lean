# Handoff — the isometry clause, the nested wall theorem, and two ways I broke things

**Written:** 2026-08-07 @ `6941c85` · **Updated:** 2026-08-07 (later) @ `1149c52`

Read this if you are picking up the **Lean formalization** lanes. It is written
for a session with no memory of the one that produced it, and it assumes you
will verify rather than believe. Several sections below are corrections of
things a session got wrong in ways that reached `main`.

If you are picking up the **contract / registry / arXMCP** work instead, read
[`2026-08-05-mfc-cli-handoff.md`](2026-08-05-mfc-cli-handoff.md) first — it is
still current and this note does not supersede it.

> ## UPDATE 2026-08-07 (later) — read this before §1
>
> A second session picked this note up, and **§1 was wrong in five places within
> hours of being written.** What changed:
>
> - **PR #76 merged.** §1 listed it as the open PR. There were then zero open
>   PRs; by the time this update was committed there were **two** again, both
>   another session's. Do not read any PR count here as current.
> - **Audit records: 659 → 667 (the tilt) → 670 (Support openness).**
> - **The shared checkout was not on `main`.** It sat on `agent/tilt-complete`,
>   a merged and dead branch, with `.lake` artefacts to match.
> - **A ` M CLAUDE.md` that looks like another session's edit is a phantom.**
>   Its blob hash equals the index (`88be71d5`); the `obsidian-strip`
>   clean/smudge filter makes the file permanently un-stat-cacheable, so
>   `git status` always shows it modified while `git diff` shows nothing.
>   **Do not stage it, and do not read it as evidence that someone is working.**
> - **`Support/` is no longer quiet** and the §4.2 lane ranking moved.
>
> **The lesson is the shape, not the numbers.** A state table in a handoff rots
> in hours in this repo. §1 has been rewritten to give the *commands* first and
> the snapshot second, pinned to a commit. Run the commands; treat the table as
> archaeology.
>
> New findings from that session are in **§3.5–§3.7** and its work in **§2.3**.

---

## 1. State — commands first, snapshot second

**Run these. Do not trust the table below it.**

```bash
git show origin/main:scripts/Audit.lean | grep -c '^#print axioms '
```

```bash
lake build && lake env lean scripts/Audit.lean > audit.txt 2>&1 && python scripts/check_audit.py audit.txt
```

```bash
lake exe runLinter BridgelandStabLean
```

```bash
lake build && lake env lean scripts/Census.lean
```

The first is the audit count pinned to a commit — the *only* honest way to
quote one, and `formalization.yaml` has now been burned twice by carrying a
number forward instead. The second and third are CI gates. The fourth is new
(2026-08-07) and reports how much of the library the audit actually covers.

Snapshot, **pinned to `1149c52`** and stale the moment another session pushes:

| | |
|---|---|
| `main` | `1149c52`, CI green |
| Lean modules | **44**, across 8 lanes |
| Audit records | **670** (`scripts/Audit.lean`) |
| Environment census | **814** authored → **144 outside the gate** |
| ↳ of those | 44 private (unlistable) · 41 structure projections · **59 real gap** |
| `sorry_count` | **0** |
| Registry entries | **9** (`registry/bridgeland2007.json`) |
| `@[cites]` bindings | **11** — 8 on `lem-8.2`, 2 on `prop-8.1`, 1 on `def-5.7` |
| `human_review` | **`none`** — no statement has ever had one |
| Open PRs / issues | 2 / 57 — **both moved during the writing of this line** |

**The census numbers are not the ones this note first carried.** It said "713
top-level declarations → 54 outside the gate", from a regex over source text.
The environment sweep says 814 → 144, and the difference is not drift: a regex
cannot see private names, and it counts structure projections it should not.
See §3.6.

### The lanes, and which are hot

| lane | files | last touched | who |
|---|---|---|---|
| `GroupAction/` | 34 | 2026-08-07 | **hot** — the §8 programme |
| `Tilting/` | 2 | 2026-08-07 | **hot** — merged, then reviewed; issue #94 open |
| `Support/` | 1 | 2026-08-07 | **openness added**; quiet again now |
| `Wall/` | 1 | 2026-08-07 | quiet |
| `Mukai/` | 2 | 2026-08-06 | quiet |
| `FiniteLength/` | 1 | 2026-08-06 | quiet |
| `Lattice/` | 2 | 2026-08-04 | dormant |
| `ForMathlib/` | 1 | 2026-08-04 | dormant, and see CLAUDE.md §1 |

Regenerate that column rather than trusting it:

```bash
for d in GroupAction Tilting Mukai Support FiniteLength Wall Lattice ForMathlib; do
  echo "$d $(git log -1 --format=%ad --date=short origin/main -- BridgelandStabLean/$d)"
done
```

**Multiple sessions work this repo concurrently and share one checkout.** That
is not a hypothetical; it broke `main` on 2026-08-07, and on the same day the
tree silently sat on a dead branch through an entire session's work. See §3.1
before you commit anything.

---

## 2. What was added

**§2.1–2.2 are the first session's** (the one that wrote this note): two
theorems in two lanes, both chosen because nobody else was in them.
**§2.3–2.4 are the second session's**, on the same day, added when it picked
this note up. All four merged to `main` and are CI-green.

### 2.1 The isometry clause of Lemma 8.2 — `GroupAction/AutIsometry.lean`

Merged as #63 (`6ce0d0f`), bench extended in #65.

```
mapEquiv_slicingDist          slicingDist (Φ·s₁) (Φ·s₂) = slicingDist s₁ s₂
actStabAut_slicingDist        …carried to stability conditions
AutPairQuot_smul_slicingDist  …and to the MulAction
```

Plus four supporting lemmas the anchor never named:
`Slicing.phiPlus_congr` / `phiMinus_congr` (iso-invariance of the intrinsic
phases — the anchor inlines that argument at **four** sites in
`Deformation/DeformedGtLe.lean` without ever stating it), and
`isZero_functor_iff` / `isZero_inverse_iff` (`Functor.map_isZero` goes one
direction only).

**The finding, which is worth more than the theorem.** `actStabAut`'s own
`@[cites]` note used to say *"no metric is constructed here, so isometry is not
proved."* Literally true, and it invited the wrong inference. **The anchor has
carried `slicingDist` since before this repo existed** —
`StabilityCondition/Defs.lean:168`, written for §7's deformation theory and
never connected to §8. CLAUDE.md's "search the whole anchor before concluding
something is missing" rule has now paid **three** times.

**All three bindings are `no_claim`, deliberately.** `slicingDist` carries two
of the three terms in Bridgeland's `d` and omits `|log(m₂/m₁)|`, the mass
ratio — the only term that reads the central charge. A sup of three being
preserved does not give that each term is, so the paper's claim does not imply
ours either. **The anchor defines no mass function**, checked rather than
assumed, so the gap is not closable at this pin.

### 2.2 Bertram's nested wall theorem — `Wall/Numerical.lean`

Merged as #71 (`aefda82`), trust record in #75.

The file's own docstring had said this was out of reach: *"needs the extra
input that both minor vectors are cross products against a common `v`, and a
rank argument in `ℝ³`. Neither is done."*

**The first half is a one-line `ring` identity and the second half is not
needed at all.**

```lean
theorem minor_orth (v w : NumClass) :
    v.ch2 * minA v w + v.deg * minB v w + v.rk * minC v w = 0
```

With it, two walls through one point give two circle equations and two
orthogonality relations; eliminating pairwise leaves

```
(deg − s·rk)·crossAB = 0     and     (ch₂ − ((s²+t²)/2)·rk)·crossAB = 0
```

and the file's own `charge_eq_zero_iff` already says those two coefficients
vanish *together* exactly where `v`'s charge does. The `ℝ³` rank argument never
appears — the orthogonality relations do its work, and what would have been a
genericity assumption becomes an explicit hypothesis.

**That hypothesis is proved necessary, not asserted.**
`wall_eq_of_meet_needs_charge` exhibits `v = (2,0,1)`, whose charge vanishes at
`(0,1)`. There the wall equation collapses to `minA + 2·minC = 0`, which
`minor_orth` makes automatic for *every* `w` — so at that one point **all**
walls of `v` meet. `w₁ = (0,1,0)` gives the unit circle, `w₂ = (1,0,0)` the
line `s = 0`, and `(0,2)` separates them.

**It is not the geometric nested wall theorem.** The geometric statement also
asserts the walls it orders are walls of *actual stability*, which needs
`NumClass = ch(E)` — CLAUDE.md §4. Say "numerical walls for a fixed class are
disjoint" and stop there.

---

### 2.3 The support property is open in the charge — `Support/SupportProperty.lean`

Added by the second session, merged as #78 (`418d423`).

```
hasSupportProperty_of_norm_sub_le    perturbed constant C / (1 - Cε)
HasSupportProperty.exists_tolerance  openness, no topology on charges
isOpen_hasSupportProperty            IsOpen {Z : V →L[ℝ] W | …}
```

**§4.2 below predicted this would need "linear algebra plus compactness, and
the file already has the compactness argument." It needs neither compactness
nor finite-dimensionality** — the triangle inequality and one division. The
compactness in that file belongs to the *quadratic-form* direction
(`hasSupportProperty_of_isCompatible`); carrying it into perturbation would
have weakened all three statements for nothing. All three are stated with
`omit [FiniteDimensional ℝ V]`.

`exists_tolerance` must *choose* the tolerance from `C` rather than accept one:
the admissible perturbation depends on how tight the estimate already is, and
the constant degrades as `Cε → 1`. `isOpen_` is then a corollary whose only new
step is `le_opNorm`.

`S` stays an arbitrary subset. No anchor import, no triangulated category, no
geometry — CLAUDE.md §3 and §4 untouched by construction. **No `@[cites]`
binding**: this corresponds to no numbered claim in Bridgeland 2007, so the
review bench is unchanged.

### 2.4 The audit's coverage claim, re-measured — `scripts/Census.lean`

Merged as #92 (`0b19f9d`). This is §4.4 of this note, which the first session
left undone because the tree was being written by someone else.

The figures in `scripts/Audit.lean` and in `formalization.yaml` were **wrong in
kind, not only in size**:

| | was | now |
|---|---|---|
| audit names | 497 | **670** |
| authored declarations | 569 | **814** |
| outside the gate | 72 | **144** |
| private | 42 | **44** (42 of them theorems) |
| structure projections | *uncounted* | **41** |
| real gap | 29 | **59** |
| not theorems | 167/497 | **189/670** |

`20 in GLTildeSurj.lean` is the one old figure that was right and has not moved.
It is still the largest single block of the real gap.

---

## 3. The findings that matter

### 3.1 Do not `git add` a whole file in this repo

**This broke `main` for about ninety minutes today** and it will happen again
to whoever forgets.

Multiple agent sessions run against **one shared checkout**. During this
session the working tree switched branches under me twice
(`main` → `review/opus5-first-pass-fixes` → `agent/tilt-recognition`) and files
I had never touched went dirty. That is normal here, not an incident.

The failure: I ran `git add scripts/Audit.lean` when `git status` showed it
modified, read that as *my* edit, and swept in four `#print axioms` lines
belonging to another session's **uncommitted** `Tilting/HeartTorsionPair.lean`.
`#print axioms` on an unknown constant is a hard error, so the axiom gate could
not elaborate. Fixed in #74 (`2ab9a9b`); the four arrived properly with their
own file in #72.

**The tell was there and I ignored it.** The same file's `#print axioms` count
read **642** and then **659** minutes apart. I said so out loud and carried on.
A count that disagrees with itself between two reads means someone else is
writing.

What to do instead:

- Stage **hunks** (`git add -p`), or stage only files you created.
- Before committing, run `git show <sha> --stat` and `git show <sha> -- <file>`
  on your own commit and read every line you are about to publish.
- If you must work in the shared tree: create your branch, commit only your
  files, then **switch back to the branch you found and clear the index**
  (`git restore --staged <files>`). Leave the tree as you found it.
- Better: `git worktree add` somewhere short and work there. Note **path
  length** — CLAUDE.md §7 documents that a worktree under `.claude/worktrees/`
  is too deep to *build* (MAX_PATH), but a worktree used only for editing,
  committing and pushing is fine at any depth. `C:/Users/cedar/AppData/Local/Temp/claude/wtfix`
  worked for exactly that today.

### 3.2 The environment linters catch things `lake build` cannot, including mine

`lake exe runLinter BridgelandStabLean` became a CI gate in #64 on 2026-08-05.
It earned its place **one day later, on code written by the session that had
reviewed it.**

I marked three antisymmetry lemmas `@[simp]`:

```lean
@[simp] theorem crossAB_swap : crossAB v w₂ w₁ = -crossAB v w₁ w₂
```

An antisymmetry lemma whose two sides share a head symbol with permuted
arguments **rewrites forever**. `runLinter` failed all three with `maximum
recursion depth has been reached`. `lake build` was green throughout, because
nothing in the file happened to call `simp` on one.

**Run the linters locally before you push.** They are the only check that reads
the elaborated environment: `simpNF` replays the simp set, `impossibleInstance`
asks whether an instance can actually be found. Neither is expressible at
source level.

### 3.3 A pipeline throws away the exit status you were gating on

This is how the red commit reached `main`, and it is subtle enough to repeat.

```bash
gh run watch <id> --exit-status 2>&1 | tail -20 && gh pr merge <n> --rebase
```

**A pipeline exits with the status of its last command.** `tail` returned 0, so
the merge fired over a failed run. I had used the same shape on #65, where it
passed only because that run happened to be green — so the bug was already
there and invisible.

This is `2026-08-05-mfc-cli-handoff.md` §2.6 — *"do not report a CI conclusion
you have not read"* — in a new costume. The conclusion was fetched, printed,
and then discarded by the pipe.

What works:

```bash
gh run view <id> --json conclusion,jobs \
  --jq '"conclusion=" + .conclusion, (.jobs[].steps[] | "   " + .name + " = " + (.conclusion // "?"))'
```

Read `conclusion` **and the per-step list**. An overall `success` with steps
showing `-` (skipped) is not the same as everything passing, and the red run
here showed exactly that: `no sorry in the build log` and `emit, and fail on
sorryAx` never ran because the gate before them died.

If you want to chain, redirect rather than pipe and check `$?`:

```bash
gh run watch <id> --exit-status > out.txt 2>&1; rc=$?; [ $rc -eq 0 ] && gh pr merge <n> --rebase
```

### 3.4 CI is slower and wider than it was

A run is now **~25–30 minutes**, up from ~4. The library tripled and the
emitter builds too. Steps, in order:

```
lean-action (lake build) → axiom gate → environment linters
→ no sorry in the build log → emit, and fail on sorryAx
→ upload the emission → upload audit output
```

`emit` is real now — `exe/Emit.lean` sweeps `Environment.constants`, so it sees
the private and unlisted names `scripts/Audit.lean` structurally cannot.

**CI does not run on a plain branch push.** Triggers are `push: branches:
[main]` and `pull_request`. Pushing a branch fires nothing; you need a PR.

---

### 3.5 `--auto` gated on nothing — until `main` was protected on 2026-08-07

> **RESOLVED 2026-08-07 (later).** `main` is now branch-protected: the `build`
> check is **required** and **`enforce_admins` is `true`**. The hazard below is
> history. It is kept because the *shape* of the mistake recurs, and because the
> first fix proposed for it would not have worked.

**What was wrong.** `gh pr merge --auto` waits only on *required status checks*.
With no protection rule there were none, so it **merged immediately** and
reported success. A session used it specifically to avoid merging before CI
finished, and it merged before CI finished. The run happened to be green — luck,
not verification.

That was §3.3 in a second costume: a construct trusted to enforce something it
was not enforcing. A third followed within the hour — a PR's latest run was
`success`, but for its *first* commit, while the second had triggered no run at
all. Three mechanisms, one outcome, and the prose fix for each did not prevent
the next.

**`enforce_admins` is the part that matters, and the first fix missed it.**
"Require the `build` check" is not sufficient on its own: with
`enforce_admins: false`, administrators **bypass required checks**. The token
these sessions run under has `admin: true`, so protection configured that way
would have been decorative for exactly the actor that caused every incident.
It is set to `true` here, which also means **direct pushes to `main` are
blocked** — everything goes through a PR, including the owner's.

Verify the current state rather than trusting this paragraph:

```bash
gh api repos/chris-dare-dev/bridgeland-stab-lean/branches/main/protection \
  --jq '{contexts: .required_status_checks.contexts, enforce_admins: .enforce_admins.enabled}'
```

Expect `{"contexts": ["build"], "enforce_admins": true}`. **If it ever returns
404 again, the protection was removed and every hazard above is live.**

**The discipline has not changed, only its backstop.** Protection stops a merge
over a red or missing run; it does not tell you what failed, and it does not read
the per-step list for you. An overall `success` with steps showing `-` (skipped)
is still not everything passing — §3.3. Still: wait, read the steps, confirm the
run's `headSha` matches the PR head, then merge.

**One claim here is documented, not measured.** That `enforce_admins: false`
lets admins bypass is GitHub's documented behaviour; nobody on this repo has
observed it. What *was* measured is the settings reading back correctly after
they were applied. Tracking in **#98**, which stays open until a merge is
actually refused over a failing or unfinished check.

### 3.6 The environment sweep works on Windows even though the emitter does not

`exe/Emit.lean` records that `lake exe emit` **cannot be linked** on Windows —
`supportInterpreter` pushes the PE export table past 65535 symbols — and both
that file and `formalization.yaml` treat this as "no environment-level check on
this platform."

**Linking is not what the sweep needs.** `lake env lean scripts/Census.lean`
walks the same `ModuleData` through the interpreter and links nothing, so it
runs where the executable cannot. That is the only reason §4.4 was closable at
all on the owner's workstation.

Be precise about what this does and does not change: **Census reports, it does
not gate, and it does not check axiom closures.** The emitter is exactly as
unlinkable as before. Do not describe the emitter gate as available on Windows.

**One trap inside it, which cost real time.** `isPrivateName` must be tested
**before** `Name.isInternal`. Lean mangles a private name to
`_private.<Module>.<n>.<Name>`, whose first component starts with `_`, so
`isInternal` swallows every private declaration and the census cheerfully
reports **`private: 0`**. That number looks entirely plausible. If it had been
believed, the corrected docstring would have carried a fresh error in place of
the stale one.

Also: `String.trim` and `String.drop` are mid-deprecation at v4.29.0 and return
`String` in one position and `String.Slice` in another. `Census.lean` carries
its own trim and tokenises rather than fighting it.

### 3.7 ` M CLAUDE.md` is a phantom, not another session

`git status` in this checkout permanently shows `CLAUDE.md` modified while
`git diff` shows nothing. It is not someone's uncommitted work:

```bash
git hash-object CLAUDE.md          # 88be71d5…
git ls-files -s CLAUDE.md          # same blob
git check-attr -a CLAUDE.md        # filter: obsidian-strip
```

A file with a clean/smudge filter cannot be stat-cached, so it is re-checked
and reported as possibly-modified forever. `git update-index --really-refresh`
says `needs update` and changes nothing.

Two consequences. **Never stage it** — that is exactly the §3.1 accident.
And **do not read it as a signal that another session is live in the tree**;
use `git log`, `gh pr list`, and the branch the tree is actually on instead.

---

## 4. Where to pick up

### 4.1 The live front is the mass-triangle obligation — and it is someone else's

`GroupAction/` had 54 commits since 2026-08-05. The open obligation is
`StabilityMassTriangleInequality` (`StabilityDistanceTopology.lean:515`),
reduced by `StabilityMassTriangle.lean` to
`StabilityMassSemistableTriangleInequality` (`:78`).

Exactly **two** registry frontier items are open, and they are unrelated to
each other — do not read the second as part of the mass-triangle work:

| frontier id | on | what it is |
|---|---|---|
| `stability-mass-triangle` | `prop-8.1`, `obl-stability-mass-triangle` | the obligation above |
| `autpairquot-not-aut-d` | `lem-8.2` | `AutPairQuot v` is not `Aut(D)`; its elements are pairs |

The second is not a proof gap you can close by proving something. It is a
statement about what the formalized group *is*, and closing it means either
identifying `AutPairQuot v` with `Aut(D)` (false in general — the forgetful map
is proved neither injective nor surjective) or reformulating.

`gltilde-universal-cover` was **discharged** on 2026-08-07 (`0684fdc`). Do not
re-open it, and read its discharge note before citing it: the discharge was an
explicit **human judgement** by the owner that
`GLTilde.universalCoverData` + `exact_deckHom_toMatHom` is what the paper's
phrase means here, recorded precisely because Mathlib has no bundled
universal-cover predicate at the pin to instantiate mechanically. The note also
scopes itself: it closes the covering-space gap **only**, Lemma 8.2 stays
non-`exact` under `E-05` while `autpairquot-not-aut-d` is open, and
`fidelity.human_review` stays `none`.

What remains on the mass triangle is the analytic half: a heart-level
short-exact mass inequality, then the semistable-left case through cohomology
in the heart. CLAUDE.md is explicit that the reduction is progress on *the
shape of what is owed*, not on Proposition 8.1, which stays `no_claim`.

**Check whether a session is already in it before starting.** `git log -5`,
`gh pr list`, and `git status` in the shared tree.

### 4.2 Quiet lanes with real headroom

Ranked by how much is reachable without touching the geometric lane:

1. ~~**`Support/SupportProperty.lean`** — the openness/deformation
   consequence.~~ **Done** 2026-08-07, §2.3 above, merged as #78. Note the
   prediction in this entry was wrong twice over: it needs neither compactness
   nor finite-dimensionality. What is left in this lane is smaller — the
   *quantitative* direction (how the constant `C` degrades along a path of
   charges) is stated pointwise but never integrated, and nothing yet connects
   `HasSupportProperty` to `Lattice/`.
2. **`Mukai/`** (2 files). Rank-two subpairs are done. Spherical and isotropic
   classes are defined but nothing computes with them yet.
3. **`Wall/`** — now has the nesting theorem. Natural next: the **totally
   ordered** structure (nested circles for a fixed `v` are linearly ordered by
   radius), or the vertical-line case as a degenerate member of that order.
   Everything stays real arithmetic.
4. **`FiniteLength/SimpleCharge.lean`** — the lattice half of Bridgeland §5 is
   done. The other half needs Jordan–Hölder for abelian categories, which
   **neither Mathlib nor the anchor has**. Do not start it.
5. **`Lattice/`** — dormant since 2026-08-04 and the smallest lane. Probably
   finished for what it is.

### 4.3 Lean-side issues actually worth doing

Most of the open issues (**57** at `1149c52`, up from 44) are
contract/registry/arXMCP, not Lean. The ones that are Lean:

- **#94 The co-aisle textbook-agreement lemma** — *new, 2026-08-07*, from the
  independent review of the HRS tilt (`.claude/reviews/2026-08-07-pr76-hrs-tilt-independent-review.md`).
  Discloses an aisle-side gap. Freshest and most specific item on this list.
- **#41 `@[discharges]`** — anchor frontier discharge in the environment rather
  than in prose. Directly useful now that `gltilde-universal-cover` was
  discharged by hand.
- **#38 Mechanize CLAUDE.md §3** — import allowlist + forbidden vocabulary. Would
  have caught nothing so far, but it is the rule most likely to erode.
- **#46 Cut v0.1.0** — the first release. Blocked on nothing technical.
- **#25 Sort every emitted array** — `agent-ready`, small, in the emitter.

Not an issue yet, and worth one: **branch protection on `main`** with the CI
check required. §3.5 — merges can currently land over a red or unfinished run,
which is the mechanism behind the 2026-08-07 breakage. Owner's call; an agent
should not change repo settings.

### 4.4 ~~The one thing I left undone~~ — done 2026-08-07

`scripts/Audit.lean`'s docstring was stale and is now re-measured, along with
the same claim in `formalization.yaml`. See §2.4 for the figures and
`scripts/Census.lean` for the command that regenerates them.

**Two things worth keeping from how it went.**

The instruction in this section was *"measure rather than arithmetic — the
private/public split and the theorem/construction split both need recounting,
not adjusting."* That was right, and it was not enough: the *first* measurement
was also wrong. A regex over source text cannot see private names and
overcounts by including structure projections, and the first environment sweep
reported `private: 0` because of the `isInternal` trap in §3.6. **Measuring is
not one step. Check the measurement against something that would notice if it
were wrong** — here, that the parts sum to the whole:
`670 gated + 41 projections + 59 gap = 770 public`, and `770 + 44 private = 814`.

And the numbers here were themselves stale within hours — **659/713/54** in the
original text, against **670/814/144** measured. The lesson §1 now leads with:
ship the command, not the figure.

---

## 5. Standing constraints — do not rediscover these

From `CLAUDE.md` and the owner's own rules. Not suggestions.

- **§2: no `sorry`, unconditional.** Absent beats sorry-backed. A result not yet
  proved is left *undeclared* with a `TODO`.
- **§4: the geometric lane is closed.** No `D^b(Coh X)`, no Chern characters, no
  Serre duality, no Bogomolov–Gieseker. Say so and stop rather than
  axiomatising the gap. Every new lane this week complies by construction and
  says so in its own module docstring — keep that habit.
- **§3: never conflate a lattice model with geometry.** `Fin 2 → ℤ`,
  `NumClass = ℝ × ℝ × ℝ`, `Fin n → ℤ` are **not** `K_num`, `ch(E)`, or `K₀(A)`.
- **§1: the pins are load-bearing.** Exact commits, never branches. One named
  exception (`MathFormalContract`), bounded by being a zero-dependency leaf.
- **Never `mkdir` + `git init` a repository anywhere** without an explicit OK for
  that specific repo.
- **Push is per-event authorization.** One "yes, push" does not authorize the
  next. Re-ask. Same for merge. **`--auto` now has something real to wait on** —
  `main` was protected on 2026-08-07 with `build` required and `enforce_admins`
  true — but that is a backstop, not a substitute for reading the run. §3.5.
- **Never `--no-verify`, never `--no-gpg-sign`.**
- **No bare "verified."** No single token may collapse distinct trust axes.
- **Local-LLM policy:** qwen produces, Claude reviews. Claude is always the
  quality gate.

---

## 6. Things a fresh session will want to know about the code

- **The anchor is not covered by `lake exe cache get`.** It compiles from source.
  Keep it built.
- **Search the *whole* anchor before concluding something is missing.** Three
  separate findings this week came from not doing so —
  `interval_thinFiniteLength_of_inclusion_strict` in `Deformation/`,
  `slicingDist` in `StabilityCondition/Defs.lean`, and the anchor's own
  `phiPlus_eq` machinery. `Deformation/` in particular holds general
  interval-category infrastructure that `IntervalCategory/` does not.
- **21+ dot-notation extensions on anchor types** live in this repo
  (`Slicing.mapEquiv`, `K₀.mapF`, `HNFiltration.mass`, …). CLAUDE.md §1 carries
  the regeneration command. Each is a name an anchor bump could collide with.
  This session added `Slicing.phiPlus_congr` and `phiMinus_congr` to that list.
- **`@[cites]` is verified by sweeping the built environment, not by trusting the
  attribute parsed.** The pattern:
  ```lean
  import BridgelandStabLean
  import MathFormalContract
  open Lean MathFormalContract
  run_cmd do
    for e in citesEntries (← Lean.getEnv) do
      Lean.logInfo s!"{e.declName} | {e.key} | {repr e.relation}"
  ```
- **`relation := no_claim` requires a note** (`E-06`). Two of this session's
  three new bindings would have been rejected without one.
- **`no_claim` vs `one_way` is a real distinction, not modesty.** Use `one_way`
  only when the paper's statement genuinely implies yours. If the two are about
  *different functions* or *different carriers*, it is `no_claim` — that is the
  precedent `gltildeSlicingMulAction` set and the isometry bindings follow it.
- **The review bench** (`.claude/reviews/2026-08-05-first-faithfulness-review.md`)
  now covers 7 bindings. Every verdict box is empty and **an agent may not fill
  one** — ADR-0005 makes `faithfulness` human-only. If you add a binding, add
  its bench entry: quote, `reviewed_quote_sha256`, elaborated type at
  `pp.proofs true`, author's note.
- **Lemma 8.2 makes four assertions and nothing binds to the fourth** — that the
  two actions commute. `CombinedAction.lean` proves they commute, but no
  `@[cites]` points at that clause. An absent binding has no bench section, so
  it is invisible to an entry-by-entry reviewer. Recorded in the bench's
  coverage note.
- **`formalization.yaml` is the highest-contention file in the repo.** Expect to
  race. Write it last, from a worktree, and pin every count to a commit.

  **It has now been burned twice by counts pinned to the wrong commit.** The
  second, found 2026-08-07: it recorded 667 audit records observed "on main at
  `3ca176b`", but `3ca176b` carries 659 — 667 first appears at `a3bfb8a`. The
  first is recorded at the end of its own `axiom_details` chain and closes with
  *"a paragraph whose whole point is 'do not quote a stale number' had quoted
  three of them."* Pin a count by **running the command against the commit**,
  never by carrying it forward from the branch you observed it on:
  ```bash
  git show <commit>:scripts/Audit.lean | grep -c '^#print axioms '
  ```
- **The review directory is now two files, and one is a real independent
  review.** `.claude/reviews/2026-08-07-pr76-hrs-tilt-independent-review.md`
  (332 lines) with `2026-08-07-TiltNonvacuity.lean` beside it, from a review of
  the merged HRS tilt. Its finding F1 became **issue #94**. If you touch
  `Tilting/`, read that review before the source.
- **A reviewer's checkbox is not an agent's to tick.** The sign-off box in that
  review was ticked in its own commit — *"at the owner's explicit instruction"*
  — and the commit message says so precisely because the alternative reads as
  an agent self-certifying. ADR-0005 keeps `faithfulness` human-only; the same
  logic covers any box that stands for a human judgement.
