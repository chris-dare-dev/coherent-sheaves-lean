# Handoff

Written 2026-08-07, at commit `17937fd`. For a session picking this repo up cold.

Read §1 and §7. Everything else is reference.

---

## 1. Sixty seconds

```bash
git clone git@github.com:chris-dare-dev/coherent-sheaves-lean.git
cd coherent-sheaves-lean
lake exe cache get      # ~5 min, downloads Mathlib oleans. A cache MISS is a real failure --
                        # building Mathlib from source takes hours.
lake build              # ~1 min warm
lake env lean scripts/Audit.lean
```

The audit must print `[propext, Classical.choice, Quot.sound]` on every line and never
`sorryAx`. There is no `sorry` in this library and there never has been.

**State:** 19 commits, 14 Lean files, ~1600 lines. CI and Docs both green. Docs live at
<https://chris-dare-dev.github.io/coherent-sheaves-lean/>. 44 issues, 6 closed.

**Layer A is done.** **Layer B is 2 lemmas past its definitions.** The live piece of work is
issue #11, §7 below.

---

## 2. What this is

Coherent sheaves, Chern classes and Riemann–Roch for smooth projective varieties over a field,
in Lean 4 / Mathlib. As of August 2026 no proof assistant has any of it — the survey behind
that claim is in `README.md`, and it still holds.

Dimension-general throughout. Surfaces are the near-term target but nothing is stated only for
`n = 2`; threefolds and fourfolds are meant to be specialisations, not rewrites.

### Two layers, and why

**Layer A — `CohLean.Numerical`.** The numerical interface, as typeclasses, with no schemes
anywhere. `NumericalRing n A` is the intersection ring `A^•(X)_ℚ` graded by codimension with a
degree map in top codimension; `NumericalVariety n A N` adds `N(X)`, the Chern character by
graded components, the Todd class and `χ`, subject to Hirzebruch–Riemann–Roch.

Its fields are **axioms**. `hirzebruch_riemannRoch` in particular is assumed. That is the trust
boundary, it is visible in the type, and Layer B exists to discharge it. Nothing downstream may
treat those fields as proved, and no new axiom goes into Layer A without a line in `ROADMAP.md`
naming the Layer B stage that will discharge it.

**Layer B — `CohLean.Coh`.** The real construction from Mathlib's scheme theory.

### The design decision that makes Layer B tractable

**No Chow rings.** Intersection numbers come from Snapper's theorem: for proper `X` over a
field, `(n₁,…,n_r) ↦ χ(F ⊗ L₁^{n₁} ⊗ ⋯ ⊗ L_r^{n_r})` is a numerical polynomial, and
intersection numbers are its coefficients. So `c₁` is a Cartier divisor class, `D · D'` is a
polynomial coefficient, and `ch₂` is read off `χ`. No cycles, no rational equivalence, no Chow
group. (Kleiman's numerical-ampleness route; Bădescu, *Algebraic Surfaces*, ch. 1.)

If you find yourself about to build a Chow ring, stop and re-read this.

---

## 3. What is proved

### Layer A — complete and audited

| File | Content |
|---|---|
| `Numerical/Defs.lean` | `NumericalRing n A`, `NumericalVariety n A N` |
| `Numerical/RiemannRoch.lean` | `degree_ch_mul_todd` — the RR expansion, proved once **for all `n`** |
| `Numerical/Surface.lean` | `chi_eq` at `n = 2`, *derived* from the above; `discriminant`; `degree_discriminant` |
| `Numerical/K3.lean` | `IsK3` (asserts only `td₁ = 0` and `∫td₂ = 2`), `chi_eq`, Mukai self-pairing, `⟨v,v⟩ = ∫Δ − 2r²` |
| `Numerical/OfGradedBasis.lean` | `NumericalRing.ofGradedBasis` — builds the graded ring from a basis, discharging the internality obligation once |

Three models, so nothing is vacuous:

| Model | Why it exists |
|---|---|
| `Examples/Point.lean` | dimension zero; proves the axiom set is consistent |
| `Examples/K3Model.lean` | K3 of degree `H² = 2d`; `IsK3` is **proved**, not assumed |
| `Examples/ProjectivePlaneModel.lean` | `ℙ²`, and it earns its keep: `td₁ = (3/2)H ≠ 0`, so it tests the `c₁·td₁` term of `Surface.chi_eq` that the K3 model multiplies by zero. `p2Chi_lineBundle` recovers `χ(O(nH)) = (n+1)(n+2)/2` |

`Examples/RankOneSurface.lean` holds what the two surface models share — every Picard-rank-one
surface has the same ring `ℚ[t]/(t³)` up to the single number `∫H²`. A new rank-one model costs
a Todd class and nothing else.

### Layer B — definitions plus two upstream-bound lemmas

| File | Content |
|---|---|
| `Coh/Defs.lean` | `IsCoherent` (= finite presentation; correct on locally noetherian schemes, documented as strictly stronger elsewhere), the `coherent` `ObjectProperty`, `Coh X`, the inclusion `ι` |
| `ForMathlib/PresentationIsFinite.lean` | `Presentation.isFinite_of_isIso`, `Presentation.isFinite_map` |
| `ForMathlib/FinitePresentationOfPresentation.lean` | `Presentation.isFinitePresentation_quasicoherentData`, `IsFinitePresentation.of_presentation` |

The two `ForMathlib` files fill a real Mathlib gap: Mathlib has `IsQuasicoherent.of_coversTop`
but **no finite-presentation analogue**, because nothing said that transporting a presentation
preserves `Presentation.IsFinite`. Both files are in Mathlib namespaces so upstreaming is a
file move.

**Not proved:** `Coh X` closed under kernels/cokernels/extensions, `Coh X` abelian, the affine
comparison, and everything in B2–B5.

---

## 4. Invariants — do not break these

1. **No `sorry`.** Work not done is written up as not done in the module docstring. There are
   no stubs and there should never be.
2. **Every new public theorem goes into `scripts/Audit.lean`.** CI fails on `sorryAx` and on any
   `declaration uses 'sorry'` warning. A green `lake build` proves nothing on its own — it
   succeeds on sorry-backed declarations.
3. **Mathlib-style namespaces** (`AlgebraicGeometry.*`, `SheafOfModules.*`), never `CohLean.*`,
   so upstreaming a stage is a file move rather than a rename.
4. **Toolchain pinned to `leanprover/lean4:v4.29.0`** to match `bridgeland-stab-lean` and
   `bstab`, which are meant to `require` this package. A bump forces bumps there, so it needs a
   reason — the first real one is the divisor work (#21), which wants upstream
   `AlgebraicGeometry/AlgebraicCycle/`.

---

## 5. Working agreements

**Stage by path. Never `git add -A` or `git commit -a`.** More than one session works this
clone. This has already gone wrong once: commit `5317c4b`, whose message is about the
affine-local criterion, actually carries `CONTRIBUTING.md` and all of `docbuild/` — another
session's in-flight work, swept up by my `git add -A`. `/scratch/` is now gitignored so that
throwaway probes cannot be swept, but that only covers probes. Stage the files you touched.

**Probes go in `/scratch/`** and are ignored. Nothing there ships. A probe worth keeping belongs
in `CohLean/` with a docstring; a probe that was a dead end gets written up as prose in the file
it came from.

**Record dead ends in the file, not just in your head.** `PresentationIsFinite.lean` documents
what its failed retry ruled out. That is why the next attempt was cheap.

---

## 6. Where the work is

7 milestones, 38 open issues. Every issue names the exact file it creates, so `ready` issues can
be worked simultaneously without merge conflicts. `lakefile.toml` is the one genuinely shared
file.

| Milestone | Open | Gist |
|---|---|---|
| A7 | 2 | Threefold (`n = 3`) and fourfold (`n = 4`) RR — both pure specialisations of `degree_ch_mul_todd`, both startable now |
| A8 | 2 | Dual involution, Euler pairing `χ(E,F)`, numerical lattice |
| B1 | 9 | `Coh X` abelian; the affine comparison |
| B2 | 6 | Divisors, `Pic X`, `O_X(D)` |
| B3 | 8 | Cohomology and `χ` — **the real gate** |
| B4 | 5 | Snapper polynomials → intersection numbers |
| B5 | 7 | Serre duality → RR for surfaces → discharge `hirzebruch_riemannRoch` |

**Startable today** (`ready`): #4, #5 (threefold/fourfold RR — genuinely easy, good warm-up),
#6 (Euler pairing), #11 (see §7), #13, #21, #26, #27, #33.

**#4 or #5 is the right first task for a fresh session.** They are short, they are pure Layer A,
they need none of the plumbing that has been eating time, and they exercise the claim that
`degree_ch_mul_todd` really is dimension-general.

---

## 7. In flight: #11, the tilde step

This is where the last session stopped, and the state of knowledge matters more than the code.

### The goal

`M~` is coherent when `M` is a finitely presented `R`-module — the affine half of
`Coh (Spec R) ≌ finitely generated R-modules`.

### It is not a theorem to prove. It is a call to make.

Mathlib already does the mathematics:

* `AlgebraicGeometry.presentationTilde` (`Mathlib/AlgebraicGeometry/Modules/Tilde.lean`) builds
  a global `SheafOfModules.Presentation (tilde M)` from a generating set `s` for `M` and a
  generating set `t` for the kernel of `R^s → M`. Mathlib uses it to prove
  `(tilde M).IsQuasicoherent`.
* `Module.FinitePresentation.out` is
  `∃ s : Finset M, span R s = ⊤ ∧ (ker (Finsupp.linearCombination R ((↑) : s → M))).FG`
  — exactly that input.
* `IsFinitePresentation.of_presentation`, in this repo, converts a finite presentation into
  `IsFinitePresentation`.

So the proof is: unpack `out`, feed `presentationTilde`, observe that its index types **are**
`t` and `s`, apply `of_presentation`.

Earlier plans that routed through `Module.FinitePresentation.exists_fin` and
`presentationOfIsCokernelFree` by hand are **wrong** — that work is already written. Ignore
those comments on the issue; the later ones supersede them.

### What stopped it — both plumbing, neither mathematics

**1. Universe defaulting.** `Presentation.IsFinite` and `of_presentation` carry universe
parameters that a goal phrased as `Scheme.Modules.IsCoherent …` does not pin. Lean defaults them
to `0` and reports

```
has type  Presentation.{u, u, u} (tilde Mod)
expected  Presentation.{0, 0, 0} ?m
```

`(M := tilde Mod)` does **not** help — the universes bind before `M`.
`Presentation.IsFinite.{u, u, u}` fixes that occurrence; after it, the site `J` inside the
ambient `WEqualsLocallyBijective` instance is still a metavariable. I did not get past that.

**2. `Finset` vs `Set`.** `out` yields `s : Finset M`; `presentationTilde` wants `s : Set M` and
`t : Set (↥s →₀ R)`. The subtypes are defeq but not syntactically equal, and the coercion has to
be threaded through `t`'s type too.

### How to actually do it

**In an editor, with the goal state visible.** Not through build logs. Every failure here is an
elaboration-order problem whose error message names something other than the cause. Eighteen
build iterations went into this across two sittings and did not converge; reading the goal
interactively is worth more than any amount of reasoning from error text. See §9.

---

## 8. Gotchas — the expensive part of this repo's history

Each of these cost real time. None is recoverable from reading the code.

### Instance resolution and universes

**A metavariable in an instance argument fails loudly and misleadingly.**
`Presentation.isFinite_map` is stated over a *second* sheaf of rings `S` on a second site `J'`.
Apply it without pinning `S` and `J'` stays a metavariable; Lean then tries to synthesise
`HasSheafify J' AddCommGrpCat` **against that metavariable** and fails outright rather than
postponing. The error names a missing `HasSheafify (J.over x) AddCommGrpCat` even though
`[∀ X, HasSheafify (J.over X) AddCommGrpCat]` is in scope and prints *identically* under
`pp.universes`. Fix: `exact Presentation.isFinite_map (S := R.over x) P _ _`.

This one hypothesis cost ten attempts, during which I wrongly blamed universe annotation,
section contamination, `variable` auto-inclusion, and `∀`-quantified instance binders — all four
disproved by a three-line probe. See §9.

**Universes default to `0` when nothing pins them.** Symptom is always a type mismatch at
`Type 1`. Annotate explicitly (`Foo.{u, u, u}`); named-argument pinning does not work when the
universes bind before the argument.

**`preservesColimitsOfSize_shrink` is not a global instance** — it loops. `pushforward (𝟙 _)` is
a left adjoint (`Sheaf/PushforwardContinuous.lean:275`) but only at its own hom universe, so
supply `haveI : PreservesColimitsOfSize.{u, u} … := preservesColimitsOfSize_shrink _` by hand.

**`choose D hD using …`, not `have D := (…).choose`.** With `have`, `D i` is opaque and
`choose_spec` types against `_.choose` rather than `D i` — an error with nothing to do with your
actual problem.

### Elaboration

**Dependent `Fin` rewrites fail.** You cannot `rw [pb_dim]` inside a hypothesis mentioning
`i : Fin pb.dim` — the motive does not typecheck. Feed the equation to `omega` as a fact about
naturals instead: `have hd := pb_dim; omega`.

**`letI` in a theorem *statement* is zeta-reduced away.** Re-establish the instance in the
tactic block: `letI := k3NumericalVariety d hd` as the first line of the proof.

**`omit [Inst] in` goes before the docstring**, not between the docstring and the theorem.

**A `def` whose type is a class needs `@[reducible]`**, or instance search cannot see through it.

**`rw` only closes goals by `rfl` at reducible transparency.** After unfolding a
pattern-matching `def`, an explicit `rfl` is often needed.

### Mathlib specifics at v4.29.0

* It is `Module.Basis`, not `Basis`.
* `Submodule` lives in `Mathlib.Algebra.Module.Submodule.Basic`; `DirectSum.IsInternal` in
  `Algebra/DirectSum/Basic.lean`; the `iSupIndep`-and-`iSup = ⊤` characterisation in
  `Algebra/DirectSum/Module.lean`.
* `LinearIndependent.disjoint_span_image` handles **blocks**, not just single vectors. That is
  why `ofGradedBasis` supports non-injective weights, which is what makes Picard rank > 1
  reachable. Do not restrict to injective weights.
* `simp` is the wrong tool near `PowerBasis`: `coe_basis` fires first and rewrites `basis i` to
  `gen ^ i`, after which `Basis.repr_self` no longer matches. Rewrite by hand.

### Modelling

**`χ` must land in `ℤ`, and that constrains the lattice.** On a K3 this forces the degree
parameter `d` to be a natural number. On `ℙ²` it is sharper: `ch₂ = (c₁² − 2c₂)/2` is a
half-integer whenever `c₁` is odd, so `N` cannot be `ℤ³` with `ch₂` third. The numerical
Grothendieck group is the sublattice where `3c₁ + 2ch₂` is even; substituting `2ch₂ = c₁ + 2v`
reparametrises it by `ℤ³`, and the `ℙ²` model uses those coordinates.

**A model that cannot detect a bug is not a test.** The K3 model has `td₁ = 0` and so multiplies
the `c₁·td₁` term of `Surface.chi_eq` by zero. That is precisely why `ℙ²` exists in the repo.
When you add a model, ask what it can falsify.

### Tooling

* `gh issue comment --body "…"` in bash **command-substitutes backticks**. Use `--body-file`
  with a quoted heredoc (`<<'EOF'`).
* `gh api /repos/…` on Git Bash gets its path rewritten to a Windows path. Omit the leading
  slash: `gh api repos/…`.

---

## 9. One process lesson, because it repeated

The pattern that cost the most time: **an error message named something other than the cause,
and I reasoned from the message instead of probing.**

Concretely — `HasSheafify (J.over x) AddCommGrpCat` "missing" while literally in scope. I
produced four theories and tested each by editing the real file and rebuilding: ~4 iterations,
all wrong. Then I wrote this:

```lean
example {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [hsh : ∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
    (x : C) : HasSheafify (J.over x) AddCommGrpCat.{u} := by infer_instance
```

It succeeded, which killed three theories at once and left unification order as the only
survivor — and that was the answer. The probe took two minutes.

**Write the minimal probe first.** If an error claims something is missing that you can see is
present, the error is about *when* Lean looked, not *what* it found.

---

## 10. Suggested order

1. **#4 / #5** (threefold and fourfold RR). Short, pure Layer A, no plumbing. Good calibration
   for a fresh session and they validate the dimension-general claim.
2. **#11** (§7), in an editor. Small once the goal state is visible.
3. **#6** (Euler pairing) — this is what Bridgeland stability conditions are actually defined
   against, so it is the highest-value Layer A item remaining. Must **not** add fields to
   `NumericalRing`/`NumericalVariety`; extend by a new class or every model breaks.
4. **#21** (toolchain bump and divisor API audit) before any B2 work. Upstream Mathlib gained
   `AlgebraicGeometry/AlgebraicCycle/` and `OrderOfVanishing.lean` after v4.29.0 — build on
   those rather than duplicating them.
5. **B3** is the real gate and everything after it waits. #26 and #27 are the research issues
   that decide the route; do them before writing any cohomology.

## 11. Related repos

Same machine, `Source Code/`:

* `bridgeland-stab-lean` — the consumer. `Stab(D)` group actions, metric, HN polygons. Intended
  to `require` this package, hence the toolchain pin.
* `bstab` — Bridgeland's deformation theorem; separate Lean project.
* `stability-mflds` — Python, exact arithmetic: DLP curve, Bogomolov–Gieseker, Bridgeland walls,
  **K3 Mukai lattice**. Useful as an oracle: `mukai.py` computes the same pairing that
  `Numerical/K3.lean` states, so numeric cross-checks are cheap and worth adding to new models.
