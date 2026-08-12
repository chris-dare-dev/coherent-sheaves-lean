# Fable adversarial review — issue #89 H⁰ exactness bridge

**Verdict: `SHIP WITH FOLLOW-UPS`**

Independent machine review of the pinned local snapshot, performed against the
brief in
[`2026-08-10-issue89-h0-exactness-fable-handoff.md`](2026-08-10-issue89-h0-exactness-fable-handoff.md).
No soundness blocker. Three P2 findings, three P3. All seven public
declarations are axiom-clean and statement-correct.

---

## 0. Scope, and what this review does not establish

This is an **independent machine review**. It does not:

- change `formalization.yaml`'s `human_review: none`;
- establish faithfulness to the pinned paper, or to any source theorem;
- close issue [#89](https://github.com/chris-dare-dev/bridgeland-stab-lean/issues/89);
- constitute the owner-only judgement, which only Chris Dare can perform and record.

Every gate exercised below is machine reproducibility and axiom hygiene, plus
the statement-strength, instance-hygiene, dependency and trust-record analysis
the brief requested. Nothing here converts a construction into a theorem, and
nothing here promotes a `#print axioms` line into a claim about a proposition.

No file in the reviewed snapshot was edited during this review. All Lean probes
were written to a session scratchpad outside the repository.

---

## 1. Snapshot verification

Verified before review, exactly as the brief specifies.

| item | expected | measured | ✓ |
|---|---|---|:-:|
| `HEAD` | `c7ad6ab249eb7f0a1b890a4c9ff5484b4091c7cf` | `c7ad6ab249eb7f0a1b890a4c9ff5484b4091c7cf` | ✓ |
| branch | `agent/issue-89-h0-exactness-current` | `agent/issue-89-h0-exactness-current` | ✓ |
| proof-module SHA-256 | `b001c100192b422114edf1ebd26b91dc3912b13309f243ca19e1e14de236a7f6` | identical | ✓ |
| tracked supporting-diff SHA-256 | `7b9a08a6a9efa6533d9ac284519fc795b376289e22b4c6fb5447f4310c1d60c5` | identical | ✓ |
| Lean | `v4.29.0` | `4.29.0` (emitter `lean_version`) | ✓ |

Working tree state matches the brief: four tracked files modified
(`BridgelandStabLean.lean`, `README.md`, `formalization.yaml`,
`scripts/Audit.lean`), one new proof module, two untracked handoff documents
outside the proof delta and the audit census.

Neither digest moved during the review, so this document describes a fixed
target.

---

## 2. Findings

Six substantive findings. None is a P0 or P1. Ordered by severity, then by
blast radius.

### P2-1 — trust/prose error: the stale claim was corrected at two sites, not three

**Location:** [`BridgelandStabLean/Tilting/HeartTorsionPair.lean:26-30`](../../BridgelandStabLean/Tilting/HeartTorsionPair.lean)

**Classification:** trust/prose error.

**The defect.** The module docstring still asserts:

> "**Mathlib has no `Hⁿ` for a t-structure at the pin** — `TStructure/` carries
> `truncLE`, `truncGE` and the truncation triangle, but no cohomology functor
> into the heart. The anchor has an `H0Functor`, but its *homological* property
> is present only as a list of case-by-case fragments in
> `HeartEquivalence/H0Homological.lean`, **not as an unconditional statement**."

The final clause is **false on this snapshot**.
`HeartStabilityData.H0Functor_isHomological_unconditional` is precisely that
unconditional statement, and it is in the same environment, gated in
`scripts/Audit.lean`, and axiom-clean.

The change corrected this claim family in `formalization.yaml` (§1584 ff.) and
in `scripts/Audit.lean` (§262 ff.). The brief itself scoped the work to *"the
two stale trust statements"*. There are **three** occurrences; the in-tree
module docstring was missed. Measured:

```
grep -rn "case-by-case fragments|never unconditionally" README.md formalization.yaml \
     scripts/*.lean BridgelandStabLean/ CLAUDE.md
→ BridgelandStabLean/Tilting/HeartTorsionPair.lean:30   (sole surviving occurrence)
```

**Downstream affected:** no declaration. Readers of the Tilting lane, and
anyone citing that file as evidence about the anchor's H⁰ API.

**Smallest defensible correction.** Mirror the wording already applied in the
other two places. Two constraints on the fix:

1. The adjacent sentence *"Mathlib has no `Hⁿ` for a t-structure at the pin"*
   is **verified true** and must stay — see §5.4.
2. The Hom-orthogonality rationale must stay intact. The aisle definition
   predates the new theorem and does not depend on it; the correction is that
   the anchor's H⁰ *is now* unconditionally homological, not that the aisles
   should be redefined. The `formalization.yaml` edit already models this
   correctly ("The original aisle construction remains defined by
   HOM-ORTHOGONALITY").

---

### P2-2 — proof-maintenance hazard: the anchor injected-name registry is stale, and its regeneration command cannot see the new names

**Location:** `CLAUDE.md` §1, *"Bumping the anchor pin: check the injected names first"*; all seven declarations in [`BridgelandStabLean/GroupAction/H0ExactnessBridge.lean`](../../BridgelandStabLean/GroupAction/H0ExactnessBridge.lean).

**Classification:** proof-maintenance hazard / trust-record gap.

**The defect.** `CLAUDE.md` maintains a table of dot-notation extensions this
repository declares **on types it does not own**, all anchor types, together
with a regeneration command and the line *"Measured collisions today: **zero**."*
The table covers four owner types and 21 names:

| owner type | injected names |
|---|---|
| `HNFiltration` | 10 |
| `K₀` | 6 |
| `Slicing` | 4 |
| `PostnikovTower` | 1 |

This module is the repository's **first and only** injection into a **fifth**
anchor owner type, `HeartStabilityData`, adding **7** names. All seven live in
`BridgelandStabLean/GroupAction/`, which is exactly the directory the
documented regeneration command scans — but the command's alternation is
hard-coded to the four existing types, so it is structurally blind to them:

```bash
# CLAUDE.md's command, run verbatim on this snapshot
grep -hoE "^(private )?(noncomputable )?(scoped )?(theorem|lemma|def|instance|abbrev) (Slicing|HNFiltration|PostnikovTower|K₀)\.[A-Za-z_'0-9]+" \
  BridgelandStabLean/GroupAction/*.lean | sed -E 's/^.*(theorem|lemma|def|instance|abbrev) //' | sort -u | wc -l
→ 21          # unchanged

# the names it cannot see
grep -rhoE "^(private )?(noncomputable )?(theorem|lemma|def|instance|abbrev) HeartStabilityData\.[A-Za-z_'0-9]+" \
  BridgelandStabLean/ | sed -E 's/^.*(theorem|lemma|def|instance|abbrev) //' | sort -u
→ HeartStabilityData.H0FunctorIsoOriginalHeartCohFunctor
  HeartStabilityData.H0Functor_isHomological_unconditional
  HeartStabilityData.H0primeFunctor_isHomological_unconditional
  HeartStabilityData.heartSourceH0Complex
  HeartStabilityData.heartSourceH0Complex_exact
  HeartStabilityData.heartSourceH0Complex_exact_iff_mono_cokernelDesc
  HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional
```

True count is 28 over five owner types; the checklist reports 21 over four.

**Why the collision risk is concrete, not hypothetical.** The new declarations
land in `CategoryTheory.Triangulated.HeartStabilityData` — the *same namespace*
the anchor uses — and the anchor is **actively developing that exact naming
family** in `HeartEquivalence/H0Homological.lean` and
`HeartEquivalence/EulerLift.lean`:

```
HeartStabilityData.H0Functor_isHomological_of_H0primeFunctor
HeartStabilityData.H0Functor_isHomological_of_eval
HeartStabilityData.H0Functor_isHomological_of_eval_of_heart_case
HeartStabilityData.H0Functor_isHomological_of_eval_of_heartSourceH0primeShortComplex
HeartStabilityData.H0Functor_isHomological_of_heartSourceH0primeShortComplex_f_is_kernel
HeartStabilityData.H0Functor_isHomological_of_heartSourceH0primeShortComplex_distTriang
```

An anchor-pin bump that adds an `..._unconditional` member of this family
produces an ambiguity, which is exactly the failure mode `CLAUDE.md` §1 exists
to anticipate. The failure would be a loud, local build error — but the
checklist meant to anticipate it now cannot.

**Downstream affected:** all seven declarations, on the next anchor-pin bump.

**Smallest defensible correction.** Two edits to `CLAUDE.md` §1:

1. Add a `HeartStabilityData` row listing the seven names.
2. Widen the alternation in the regeneration command to
   `(Slicing|HNFiltration|PostnikovTower|K₀|HeartStabilityData)`, and drop the
   `GroupAction/*.lean` restriction to `BridgelandStabLean/` so a future
   injection from another lane is also caught.

---

### P2-3 — statement strength: the cokernel comparison is provably an isomorphism, not merely monic

**Location:** [`BridgelandStabLean/GroupAction/H0ExactnessBridge.lean:131-139`](../../BridgelandStabLean/GroupAction/H0ExactnessBridge.lean)

**Classification:** statement-strength observation. **Additive, not a defect.**

**The observation.** The final consumer-facing theorem concludes

```text
Mono (coker(A ⟶ H⁰′X₂) ⟶ H⁰′X₃)
```

Using **only** the module's own `H0primeFunctor_isHomological_unconditional`,
the same map is also `Epi`, hence an isomorphism. I proved both against this
exact snapshot; the full probe source is in §7.

```text
Epi   ((h.heartSourceH0Complex A hT).g)                                       -- verified
IsIso (h.heartSourceH0primeShortComplex_cokernelDesc A f g …)                 -- verified
```

**Mechanism.** Rotate the distinguished triangle and apply the same homological
functor. The rotated mapped complex is

```text
H⁰′(X₂) ⟶ H⁰′(X₃) ⟶ H⁰′(A⟦1⟧)
```

and its third object vanishes, because `A` in the heart makes `A⟦1⟧` an
`IsLE (-1)` object, so `τ^{≥0}(A⟦1⟧) = 0`. The vanishing is roughly six lines
from `TStructure.isLE_shift`, `TStructure.isZero_truncGE_obj_of_isLE`, and
`ObjectProperty.FullSubcategory.isZero_of_obj_isZero`. Then
`ShortComplex.Exact.epi_f` gives `Epi (H⁰′g)`; `epi_of_epi` through the anchor's
`heartSourceH0primeShortComplex_cokernelπ_comp_cokernelDesc` transfers it to the
cokernel comparison; `isIso_of_mono_of_epi` closes it against the module's own
`Mono` theorem.

**This contradicts none of the declared non-results.** The first map still need
not be monic, so `ShortExact` for the three-term complex remains unjustified,
and the module docstring's explanation — the incoming `H⁻¹(X₃)` term — is
exactly right. What the probe establishes is narrower and sharper: monicity of
the first map is the **only** missing ingredient, and the *cokernel comparison*
specifically admits a strictly stronger true statement than the one shipped.

**Why it matters.** `coker(A ⟶ H⁰X₂) ≅ H⁰(X₃)` is the shape a mass argument
actually consumes; `Mono` alone forces a downstream author to rebuild the epi
half.

**Downstream affected:**
`mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional`, and any
future consumer of it.

**Smallest defensible correction.** None required — under-claiming is safe, and
the brief neither requested nor authorised the stronger result. If taken, it is
an **eighth** declaration of roughly 30 lines (plus one private vanishing
lemma), and every count in `formalization.yaml`, `scripts/Audit.lean` and the
census would need updating in the same commit.

---

### P3-1 — prose: forward-looking claims stated in the present tense

**Locations:**
[`H0ExactnessBridge.lean:21`](../../BridgelandStabLean/GroupAction/H0ExactnessBridge.lean) — *"the anchor-facing API **used by** the mass-triangle argument"*;
[`README.md:389`](../../README.md) — *"exposes the exact-middle-term and monic-cokernel conclusions **needed by** the mass-triangle argument"*.

**Classification:** trust/prose error (overstatement, non-promotional fix
available).

**The defect.** Nothing on current main consumes the seven declarations except
`scripts/Audit.lean`:

```
grep -rn "H0Functor_isHomological_unconditional|heartSourceH0Complex|…" BridgelandStabLean/ scripts/
→ scripts/Audit.lean:1571-1577 only
```

The sole consumer is stale **open** PR #103, which is not merged and is
explicitly out of scope per the brief. "Used by" asserts a present fact that is
not yet true in the tree; "needed by" asserts a dependency of a proof that does
not exist here — Proposition 8.1 remains `no_claim`, and the semistable
reduction is open.

`CLAUDE.md` §5 warns specifically against describing the mass reduction as
progress on the proposition, and §6 states that every `formalization.yaml`
field is a claim someone may cite. This is adjacent to both.

**Downstream affected:** no declaration. The README and the module docstring
are citable surfaces.

**Smallest defensible correction.** Replace with the intent, not the fact:
"intended for the mass-triangle argument" / "required by the future
mass-triangle rewrite (stale PR #103)".

---

### P3-2 — prose/attribution: `formalization.yaml` credits the construction and the homologicality proof to the bridge module

**Location:** [`formalization.yaml:1585-1588`](../../formalization.yaml)

**Classification:** trust/prose error.

**The defect.** The revised paragraph reads:

> "This project now constructs that functor, proves it homological, and
> transports the result to the anchor's H0Functor **in
> `GroupAction/H0ExactnessBridge.lean`**."

Three verbs, one trailing location. In fact:

| verb | actual location |
|---|---|
| constructs that functor | `BridgelandStabLean/Tilting/HeartCohomology.lean` (`originalHeartCohFunctor`) |
| proves it homological | `BridgelandStabLean/Tilting/HeartCohomologyHomological.lean` (`originalHeartCohFunctor_isHomological`) |
| transports the result | `BridgelandStabLean/GroupAction/H0ExactnessBridge.lean` |

A reader may reasonably attach the file to all three clauses, which would
overstate the 143-line bridge as containing the whole development. The
parallel edit in `scripts/Audit.lean:262` says *"This project now constructs
one and proves it homological"* with no file pinned — that one is accurate as
written.

**Downstream affected:** no declaration. `formalization.yaml` is the citable
trust record.

**Smallest defensible correction.** Split the clause, naming the two Tilting
files for the construction and the proof and the bridge only for the transport.

---

### P3-3 — instance hygiene: three redundant `letI`s

**Locations:**
[`H0ExactnessBridge.lean:106-107`](../../BridgelandStabLean/GroupAction/H0ExactnessBridge.lean) and
[`H0ExactnessBridge.lean:119-120`](../../BridgelandStabLean/GroupAction/H0ExactnessBridge.lean).

**Classification:** API/instance hygiene. Cosmetic.

**The observation.** Both proofs open with

```lean
letI := h.t.hasHeartFullSubcategory
letI : Abelian h.t.heart.FullSubcategory := h.t.heartFullSubcategoryAbelian
```

Neither is needed. The anchor already exports a **global** instance

```lean
noncomputable instance HeartStabilityData.instHeartFullSubcategoryAbelian … :=
  h.t.heartFullSubcategoryAbelian
```
(`BridgelandStability/HeartEquivalence/Basic.lean:270`)

whose body *is* the term the `letI` supplies. `pp.explicit` on the shipped
signature confirms the statements already elaborate against the global
instance — the `letI`s only shadow it inside the proof body, with a
definitionally equal term. I reproved both theorems with every `letI` for
`hasHeartFullSubcategory` and `Abelian` removed; both go through unchanged
(§7, Probe 5).

`h.t.hasHeartFullSubcategory` is Mathlib's `TStructure.Heart` bundle
(`Mathlib/CategoryTheory/Triangulated/TStructure/Heart.lean:69`), also a plain
`def`, also not needed here.

**Assessment.** Harmless, and it is the anchor's own idiom at four sites in
`HeartEquivalence/Basic.lean`. The cost is elaboration time plus a misleading
impression that the module requires non-canonical instances. Shadowing a
canonical instance with a `letI` is the general pattern that can silently
produce statements against a divergent instance — here the two terms are the
same, so nothing is at risk today.

**Smallest defensible correction.** Remove the four `letI` lines, or leave them
and add a one-line note that they restate the global instance. No correctness
impact either way.

---

## 3. Declaration-by-declaration coverage

All seven public declarations live in namespace
`CategoryTheory.Triangulated.HeartStabilityData`. All seven were individually
inspected; none was accepted on the strength of its name, its elaboration, the
handoff summary, or the green gates.

### 3.1 `H0FunctorIsoOriginalHeartCohFunctor` — construction — **sound**

`H0ExactnessBridge.lean:56-59`. Defined as `Iso.refl _`.

Expanding both sides:

```lean
-- anchor: H0Functor is an abbrev for heartCohFunctor 0
HeartStabilityData.heartCohFunctor h n
  = ObjectProperty.lift _ (h.t.truncGELE n n ⋙ shiftFunctor C n) _

-- Tilting lane
originalHeartCohFunctor t n
  = ObjectProperty.lift _ (t.truncGELE n n ⋙ shiftFunctor C n) _
```

The object property (`h.t.heart`) and the functor argument are syntactically
identical; only the heart-membership proofs differ, and those are `Prop`, so
proof irrelevance closes the gap definitionally. `Iso.refl _` is therefore
justified, not a coincidence of unification.

Verified independently of the iso itself, so that `Iso.refl` could not mask a
mismatch:

- `h.H0Functor (C := C) = originalHeartCohFunctor h.t 0 := rfl` ✓
- `(H0FunctorIsoOriginalHeartCohFunctor h).hom = 𝟙 _ := rfl` ✓
- **stronger than requested:** `h.heartCohFunctor n = originalHeartCohFunctor h.t n := rfl`
  holds for *every* `n : ℤ`, so the identity is structural rather than a
  degree-zero accident ✓

Same target subcategory, no transported or merely equivalent t-structure:
`pp.explicit` shows both sides typed at
`@TStructure.heart C … (@HeartStabilityData.t C … h)` — literally the `t` field
of the same `h`.

### 3.2 `heartSourceH0Complex` — construction — **sound**

`H0ExactnessBridge.lean:87-94`. A `noncomputable abbrev` over the anchor's
`heartSourceH0primeShortComplex`, with the zero-composition witness extracted
from distinguishedness.

- **Object and arrow order.** The anchor builds
  `ShortComplex.mk ((H0primeObjIsoOfHeart A).inv ≫ H0primeFunctor.map f) (H0primeFunctor.map g) _`,
  so the complex is `A ⟶ H⁰′(X₂) ⟶ H⁰′(X₃)`. The first object is the heart
  object `A` itself, identified with `H⁰′(A.obj)` by the anchor's canonical
  `H0primeObjIsoOfHeart`. That matches the docstring's `coker(A ⟶ H⁰(X₂))`. ✓
- **Coercion.** `A : h.t.heart.FullSubcategory`; the triangle is built from
  `f : A.obj ⟶ X₂` and `δ : X₃ ⟶ A.obj⟦1⟧`, so `A` is coerced to the ambient
  category exactly once, as `.obj`, in each position. ✓
- **Zero-composition orientation.** `comp_distTriang_mor_zero₁₂ _ hT` on
  `Triangle.mk f g δ` yields `f ≫ g = 0` (mor₁ ≫ mor₂), which is exactly the
  `hfg` the constructor demands. ✓
- **`H0prime` vs `H0`.** A proof-normal-form choice only. The anchor's
  `H0FunctorIsoH0primeFunctor` is a natural isomorphism between the two normal
  forms `τ^{≥0}τ^{≤0}` and `τ^{≤0}τ^{≥0}`; no cohomology object changes. ✓

### 3.3 `H0Functor_isHomological_unconditional` — theorem — **sound**

`H0ExactnessBridge.lean:66-72`.

Mathlib's transport lemma is

```lean
lemma Functor.IsHomological.of_iso {F₁ F₂ : C ⥤ A} [F₁.IsHomological] (e : F₁ ≅ F₂) :
    F₂.IsHomological
```

The instance must sit on the **source**. Here the local instance is placed on
`originalHeartCohFunctor h.t 0`, and `.symm` points
`originalHeartCohFunctor ≅ H0Functor`, so `F₁ = originalHeartCohFunctor`,
`F₂ = H0Functor`. **`.symm` is required and correct.** ✓

"Unconditional" is honest: the printed signature carries no
`[Functor.IsHomological …]` premise and no premise at all beyond the ambient
block. The docstring scopes the word correctly — *"no prior homologicality
instance is an input"* — rather than claiming no categorical hypotheses. ✓

### 3.4 `H0primeFunctor_isHomological_unconditional` — theorem — **sound**

`H0ExactnessBridge.lean:77-83`.

Here the local instance is placed on `h.H0Functor`, and
`H0FunctorIsoH0primeFunctor : H0Functor ≅ H0primeFunctor` is used **un-`symm`'d**,
so `F₁ = H0Functor` (has the instance), `F₂ = H0primeFunctor`. ✓

The asymmetry with 3.3 — one `.symm`, one not — is correct, and is exactly the
place a transport review should look. Cross-checked against the anchor's own
`H0Functor_isHomological_of_H0primeFunctor`, which uses the opposite
orientation for the opposite goal.

### 3.5 `heartSourceH0Complex_exact_iff_mono_cokernelDesc` — theorem — **sound**

`H0ExactnessBridge.lean:98-108`.

Mathlib supplies

```lean
lemma ShortComplex.exact_iff_mono_cokernel_desc [S.HasHomology] [HasCokernel S.f] :
    S.Exact ↔ Mono (cokernel.desc S.f S.g S.zero)
```

and the anchor's `heartSourceH0primeShortComplex_cokernelDesc` is literally
`cokernel.desc S.f S.g S.zero` for the same `S`. Therefore:

- **source** = `cokernel (heartSourceH0Complex …).f` = `coker(A ⟶ H⁰′X₂)` ✓
- **target** = `h.H0prime X₃` ✓
- **map** = the descended second arrow ✓
- **`Mono`, not `Epi`** ✓

No epimorphism or cokernel-isomorphism conclusion is smuggled in by typeclass
inference — I had to prove the epi half by hand (P2-3), which is the strongest
evidence that it is not lurking in the API.

The heart `Abelian` and `HasCokernel` instances used by the **statement** are
the canonical global ones (§5.3); no extra instance binder appears in the
printed signature.

### 3.6 `heartSourceH0Complex_exact` — theorem — **sound**

`H0ExactnessBridge.lean:113-126`.

`Functor.map_distinguished_exact (F := H0primeFunctor) (Triangle.mk f g δ) hT`
gives exactness of the *mapped triangle complex*. The comparison isomorphism
points

```text
heartSourceH0primeShortComplex … ≅ (shortComplexOfDistTriangle …).map H0primeFunctor
```

so `ShortComplex.exact_iff_of_iso e` must be used in the **`.2`** direction to
land on the declared complex. It is. ✓

`ShortComplex.Exact` is exactness at the **middle** object (vanishing of the
homology of the three-term complex), which is the intended conclusion:
exactness at `H⁰(X₂)`. ✓

### 3.7 `mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional` — theorem — **sound**

`H0ExactnessBridge.lean:131-139`.

`.mp` applied to `heartSourceH0Complex_exact` — the **exact → mono** direction,
which is the one required. ✓

Signature confirmed compatible with stale PR #103's actual use (§6.2).

See P2-3: correct, and strictly weaker than what the same machinery yields.

---

## 4. Axiom hygiene

`#print axioms` on all seven, and the emitter's independent scan, agree.

| declaration | axioms |
|---|---|
| `H0FunctorIsoOriginalHeartCohFunctor` | `propext, Classical.choice, Quot.sound` |
| `heartSourceH0Complex` | `propext, Classical.choice, Quot.sound` |
| `H0Functor_isHomological_unconditional` | `propext, Classical.choice, Quot.sound` |
| `H0primeFunctor_isHomological_unconditional` | `propext, Classical.choice, Quot.sound` |
| `heartSourceH0Complex_exact_iff_mono_cokernelDesc` | `propext, Classical.choice, Quot.sound` |
| `heartSourceH0Complex_exact` | `propext, Classical.choice, Quot.sound` |
| `mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional` | `propext, Classical.choice, Quot.sound` |

No `sorryAx` anywhere. The emitter reports **8** constants originating in the
module — the seven public declarations plus one auto-generated
`heartSourceH0Complex._proof_1` — all three-axiom clean.

**Carried forward from the brief, and restated because it matters:** clean
`#print axioms` output on the two **constructions**
(`H0FunctorIsoOriginalHeartCohFunctor`, `heartSourceH0Complex`) says only that
those constructions are axiom-clean. It asserts nothing about any proposition
and does not turn either into a theorem. `scripts/Audit.lean` already carries
this qualification in its header comment.

---

## 5. Explicit answers to the brief's questions

### 5.1 Is `Iso.refl _` mathematically and definitionally justified?

**Yes, and not by proof-irrelevance masking.** See §3.1. The two functors are
the same `ObjectProperty.lift` applied to a syntactically identical functor
argument, differing only in `Prop`-valued membership proofs. I confirmed the
underlying equality directly by `rfl` — independently of the iso — confirmed
`.hom = 𝟙 _`, and confirmed the identity holds at **every** degree `n`, not
only at `0`. Both sides target the heart of the same `h.t`, verified under
`pp.explicit`.

### 5.2 Is homologicality transported with the correct isomorphism orientation?

**Yes, both times, and the two are deliberately different.** Declaration 3.3
requires `.symm` because its available instance sits on
`originalHeartCohFunctor`; declaration 3.4 must **not** have `.symm` because
its instance sits on `H0Functor`, the source of
`H0FunctorIsoH0primeFunctor`. Checked against `Functor.IsHomological.of_iso`'s
signature, in which the instance is on `F₁` and the conclusion is about `F₂`.

### 5.3 Does the module add any global instance or hidden premise?

**No, on both counts, and this was tested rather than read off.**

- **Zero top-level `instance` declarations** in the module. The only `letI`s
  for `IsHomological` are proof-local.
- `#synth Functor.IsHomological (h.H0Functor)` **fails** after importing the
  module. This is the decisive check, because the generic instance in
  `Tilting/HeartCohomologyHomological.lean:875` *is* global, and
  `h.H0Functor` *is* definitionally equal to `originalHeartCohFunctor h.t 0`.
  It does not leak because instance search is up to reducible transparency and
  `heartCohFunctor` is a plain `def`, so the discrimination-tree keys differ.
  No competing instance, no loop.
- Even a hypothetical future diamond would be harmless:
  `Functor.IsHomological` is declared `class … : Prop`, so instances are
  proof-irrelevant.
- **No hidden premise.** Every printed signature carries exactly the ambient
  block `[HasZeroObject] [HasShift C ℤ] [Preadditive] [∀ n, Additive]
  [Pretriangulated] [IsTriangulated]` plus `(h : HeartStabilityData C)` and the
  triangle data. The `Abelian` and `HasCokernel` instances needed by the
  statements resolve from the anchor's global
  `HeartStabilityData.instHeartFullSubcategoryAbelian`, so no extra instance
  binder appears — confirmed under `pp.explicit`.

### 5.4 Is `Exact`, rather than `ShortExact`, the strongest justified statement?

**For the three-term complex, yes.** `ShortExact` is not justified: the first
map need not be monic, and the module docstring's reason — the preceding
`H⁻¹(X₃)` term in the long exact sequence — is correct.

Every `ShortExact` occurrence in the new module, `README.md`,
`formalization.yaml` and `scripts/Audit.lean` prose is a **denial**, never an
asserted result:

| file | line | form |
|---|---|---|
| `H0ExactnessBridge.lean` | 25 | *"This is `ShortComplex.Exact`, not `ShortExact`"* — denial |
| `H0ExactnessBridge.lean` | 112 | *"does not assert `ShortExact`"* — denial |
| `README.md` | 389 | *"is `ShortComplex.Exact`, not `ShortExact`"* — denial |
| `formalization.yaml` | 680 | *"is `ShortComplex.Exact`, not `ShortExact`"* — denial |
| `scripts/Audit.lean` | 1569 | *"`Exact`, not `ShortExact`, is the valid conclusion"* — denial |

The only other `ShortExact` hits in the delta are unrelated
`Tilting.HeartTorsionPair.*OfShortExact` audit gate lines that predate this
change.

**With one nuance, recorded as P2-3.** For the *cokernel comparison*
specifically, `IsIso` is provable from the same machinery and is strictly
stronger than the `Mono` shipped. That does not weaken the answer above — it
sharpens it: monicity of the first map is the only missing ingredient for
`ShortExact`, and the module's denials remain exactly correct.

**Independently verified sub-claim:** *"Mathlib has no `Hⁿ` for a t-structure at
the pin"*. Confirmed. `Mathlib/CategoryTheory/Triangulated/TStructure/`
contains `AbelianSubcategory`, `Basic`, `ETrunc`, `Heart`, `Induced`,
`SpectralObject`, `TruncLEGT`, `TruncLTGE`, and no functor into the heart
(`grep` for `⥤ … heart.FullSubcategory` and for `homology`/`cohomology`
definitions returns nothing).

### 5.5 Does the monic cokernel comparison have the intended source, target, and direction?

**Yes.** Source `cokernel (heartSourceH0Complex …).f = coker(A ⟶ H⁰′X₂)`,
target `h.H0prime X₃`, map the descended second arrow, `iff` used `.mp`
(exact → mono). No epi or iso conclusion enters by inference. See §3.5 and
§3.7.

### 5.6 Are the trust/count records exact and non-promotional?

**Counts: exact.** Every figure in the brief reproduced — see §6.1.

**Non-promotional: with three exceptions**, all recorded above:

- **P2-1** — an uncorrected false claim in a shipped module docstring;
- **P3-1** — present-tense claims of consumption by a consumer that does not
  exist on current main;
- **P3-2** — a misattributed file in `formalization.yaml`.

Nothing else overstates. In particular: no human review is inferred
(`human_review: none` untouched), no paper theorem is declared or promoted, no
mass inequality or global mass API is added, no §14 coverage status changes
(`{mapped: 1, target: 9}` verified unchanged), and no `#print axioms` line is
presented as a claim about a proposition.

The `Audit.lean` header arithmetic also stays internally consistent through the
bump: `1325 − 1128 = 197`, and the "197 are outside this gate" sentence is
correct both before and after because both totals grew by 7.

---

## 6. Verification record

### 6.1 Gates re-run on this snapshot

| command | result |
|---|---|
| `lake build` | **success, 3824 jobs** (matches brief) |
| `lake build BridgelandStabLean.GroupAction.H0ExactnessBridge BridgelandStabLean` | success (olean present; probe imports resolve) |
| `lake exe runLinter BridgelandStabLean` | **"Linting passed for BridgelandStabLean."** |
| `lake env lean scripts/Audit.lean` → `check_audit.py` | **ok: 1128 declarations, all within `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, count matches the 1128 commands in `Audit.lean`** |
| `lake env lean scripts/Census.lean` | see table below |
| `python3 scripts/check_coverage_map.py` | **ok: `registry/coverage-1902.08184v4.json` valid; statuses `{mapped: 1, target: 9}`** |
| `lake build emit` | success, 7619 jobs |
| `lake exe emit --out …` | **2647 constants scanned, 1439 in scope, 0 `sorryAx`**, `lean_version: 4.29.0` |
| `git diff --check` | clean |

A first audit run was **truncated** at 128 KB when it was moved to the
background mid-elaboration. `check_audit.py` caught this correctly and refused
the file ("output is TRUNCATED … do not lower the count"). The gate was re-run
to completion and passed. Worth recording: the checker's truncation guard
works, and a backgrounded audit is not a safe way to run it.

### 6.2 Counts — every claimed figure reproduced

| figure | claimed in brief | measured | ✓ |
|---|---|---|:-:|
| gated declarations | 1128 | 1128 | ✓ |
| of the gated: theorems | 793 | 793 | ✓ |
| of the gated: non-theorems | 335 | 335 (20 structures + 315 other) | ✓ |
| authored declarations (census) | 1325 | 1325 | ✓ |
| private | 111 | 111 (of which 97 theorems) | ✓ |
| structure-field projections | 86 | 86 | ✓ |
| public declarations outside the audit | 0 | 0 | ✓ |
| coverage registry | `{mapped: 1, target: 9}` | `{mapped: 1, target: 9}` | ✓ |
| proof-module size | 143 lines | 143 lines | ✓ |
| public declarations added | 7 (5 theorems, 2 constructions) | 7 (5 theorems, 2 constructions) | ✓ |
| audit delta | 1121 → 1128 | +7 | ✓ |
| census delta | 1318 → 1325 | +7 | ✓ |
| emitter | 2647 scanned, 1439 in scope, 0 `sorryAx` | identical | ✓ |
| modules under `BridgelandStabLean` | — | 67 | — |

The seven `#print axioms` lines added to `scripts/Audit.lean` (§1571-1577)
cover exactly the seven public declarations; none is missing and none is
duplicated.

### 6.3 Dependency and stale-PR reduction

**Imports.** Three, all used:

| import | needed for |
|---|---|
| `BridgelandStabLean.Tilting.HeartCohomologyHomological` | `originalHeartCohFunctor_isHomological` |
| `BridgelandStability.HeartEquivalence.EulerLift` | `heartSourceH0primeShortComplex*` family |
| `Mathlib.CategoryTheory.Abelian.Exact` | abelian-heart context for the cokernel equivalence |

The third is available transitively through the first, so it is redundant in
the strict sense; importing what you use is standard style and this is **not**
recorded as a finding.

**No import cycle.** Nothing under `BridgelandStabLean/Tilting/` imports
`BridgelandStabLean/GroupAction/`. The root import was inserted in
`BridgelandStabLean.lean` between `EffectiveAction` and
`StabilityMassTriangle`.

**Against stale PR #100** (692-line duplicate development, 22 declarations).
Cross-checked directly via `gh pr diff 100` — GitHub **read** access works on
this machine; only the authenticated publishing path is blocked.

Six names are shared, and their signatures are **byte-identical** between PR
#100 and the new module; only the proofs differ:

```
heartSourceH0Complex
heartSourceH0Complex_exact
heartSourceH0Complex_exact_iff_mono_cokernelDesc
H0Functor_isHomological_unconditional
H0primeFunctor_isHomological_unconditional
mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional
```

The new module adds one name PR #100 did not have
(`H0FunctorIsoOriginalHeartCohFunctor`) — the definitional identification that
replaces the duplicate proof.

The 16 dropped names split cleanly into two harmless groups:

1. **Internal machinery** for PR #100's own re-proof of homologicality —
   `H0primeObjIsoTruncGEOfIsLE`, the `toH0primeHom_of_isLE` /
   `fromH0primeHom_of_isLE` family and their naturality lemmas,
   `isIso_H0primeFunctor_map_truncLEι`,
   `mono_H0primeFunctor_map_mor₂_of_obj₁_isGE_one`,
   `H0primeFunctor_map_distinguished_exact_of_*`. Dead once the generic
   theorem is transported instead of re-proved.
2. **Conditional variants** subsumed by the unconditional forms —
   `heartSourceH0Complex_exact_of_isHomological`,
   `heartSourceH0Complex_exact_of_H0Functor_isHomological`,
   `mono_heartSourceH0primeShortComplex_cokernelDesc`,
   `mono_heartSourceH0primeShortComplex_cokernelDesc_of_H0Functor`.

**No still-required consumer theorem was dropped.** Porting the remaining PR
#100 helpers for name parity would be unjustified, and is correctly refused.

**Against stale PR #103.** It references the API exactly once:

```lean
letI : Functor.IsHomological H :=
  hd.H0Functor_isHomological_unconditional (C := C)
```

The new signature satisfies that shape exactly, with no extra premises: `C` is
implicit and determined by `hd : HeartStabilityData C`, so the dot-notation
call elaborates. This review draws **no other conclusion** about PR #103.

### 6.4 Probes written for this review

Seven scratch files, run with `lake env lean` against the built environment.
None was written into the repository.

| probe | question | outcome |
|---|---|---|
| 1 | Is `H0Functor = originalHeartCohFunctor h.t 0` by `rfl`? At every `n`? Is `.hom = 𝟙`? | all three ✓ |
| 2 | Is there a **global** `IsHomological` instance on `h.H0Functor` after import? | **fails to synthesize** — no leak ✓ |
| 3 | `#print axioms` and full signatures for all seven | clean, no hidden premises ✓ |
| 4 | Which `Abelian`/`HasCokernel` instance do the statements use? (`pp.explicit`) | anchor's global `instHeartFullSubcategoryAbelian` ✓ |
| 5 | Are the `letI`s redundant? Reprove both theorems without them | both go through ✓ (→ P3-3) |
| 6 | Is `IsZero (H0prime (A.obj⟦1⟧))` provable? | ✓ in ~6 lines |
| 7 | Are `Epi` of the second map and `IsIso` of the cokernel comparison provable? | **both ✓** (→ P2-3) |

---

## 7. Appendix — the P2-3 strengthening, as verified

Compiles against this snapshot with no `sorry` and no new axiom. Reproduced so
the finding is checkable rather than asserted. **Not applied to the repository.**

```lean
import BridgelandStabLean.GroupAction.H0ExactnessBridge

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated BridgelandStabLean.Tilting

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

private theorem isZero_H0prime_shift_one_of_heart
    (h : HeartStabilityData C) (A : h.t.heart.FullSubcategory) :
    IsZero (h.H0prime (C := C) (A.obj⟦(1 : ℤ)⟧)) := by
  have hA := (h.t.mem_heart_iff A.obj).mp A.property
  letI : h.t.IsLE A.obj 0 := hA.1
  letI : h.t.IsLE (A.obj⟦(1 : ℤ)⟧) (-1) := h.t.isLE_shift A.obj 0 1 (-1) (by lia)
  refine ObjectProperty.FullSubcategory.isZero_of_obj_isZero (C := C) ?_
  change IsZero ((h.t.truncLE 0).obj ((h.t.truncGE 0).obj (A.obj⟦(1 : ℤ)⟧)))
  exact (h.t.truncLE 0).map_isZero
    (h.t.isZero_truncGE_obj_of_isLE (-1) 0 (by lia) (A.obj⟦(1 : ℤ)⟧))

theorem epi_heartSourceH0Complex_g
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    Epi ((h.heartSourceH0Complex (C := C) A hT).g) := by
  letI : Functor.IsHomological (h.H0primeFunctor (C := C)) :=
    h.H0primeFunctor_isHomological_unconditional (C := C)
  have hrot := rot_of_distTriang _ hT
  have hex := Functor.map_distinguished_exact
    (F := h.H0primeFunctor (C := C)) ((Triangle.mk f g δ).rotate) hrot
  have hzero :
      ((shortComplexOfDistTriangle ((Triangle.mk f g δ).rotate) hrot).map
        (h.H0primeFunctor (C := C))).g = 0 :=
    (isZero_H0prime_shift_one_of_heart (C := C) h A).eq_zero_of_tgt _
  exact hex.epi_f hzero

theorem isIso_heartSourceH0primeShortComplex_cokernelDesc
    (h : HeartStabilityData C)
    (A : h.t.heart.FullSubcategory) {X₂ X₃ : C}
    {f : A.obj ⟶ X₂} {g : X₂ ⟶ X₃} {δ : X₃ ⟶ A.obj⟦(1 : ℤ)⟧}
    (hT : Triangle.mk f g δ ∈ distTriang C) :
    IsIso (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
      (comp_distTriang_mor_zero₁₂ _ hT)) := by
  letI : Mono (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
      (comp_distTriang_mor_zero₁₂ _ hT)) :=
    h.mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional (C := C) A hT
  letI : Epi (h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
      (comp_distTriang_mor_zero₁₂ _ hT)) := by
    haveI : Epi (cokernel.π (h.heartSourceH0Complex (C := C) A hT).f ≫
        h.heartSourceH0primeShortComplex_cokernelDesc (C := C) A f g
          (comp_distTriang_mor_zero₁₂ _ hT)) := by
      rw [h.heartSourceH0primeShortComplex_cokernelπ_comp_cokernelDesc (C := C) A f g]
      exact epi_heartSourceH0Complex_g (C := C) h A hT
    exact epi_of_epi (cokernel.π (h.heartSourceH0Complex (C := C) A hT).f) _
  exact isIso_of_mono_of_epi _
```

If taken, this is an eighth public declaration (plus one private lemma), and
`formalization.yaml`, `scripts/Audit.lean` and the census counts must move in
the same commit.

---

## 8. Residual risk that compilation and the emitter cannot detect

Five items. None is a reason to withhold `SHIP WITH FOLLOW-UPS`; all are things
a green build would not surface.

1. **Nothing in CI asserts the no-global-instance property.** If a future edit
   promotes either proof-local `letI` to a top-level `instance`, every gate
   stays green and the anchor's `H0Functor` silently acquires a global
   `IsHomological` instance across the whole downstream environment. The
   `#synth` probe in §6.4 is currently the only check, and it lives outside
   the repository. A guarded `example … := by infer_instance` expected to fail,
   or a note in `scripts/Audit.lean`, would pin it.

2. **`Iso.refl _` is an unpinned definitional coincidence between two
   independently authored `def`s.** It fails loudly on an anchor bump, which is
   the right failure mode, but nothing in the file records *why* it holds
   (identical `ObjectProperty.lift` applications, differing only in `Prop`).
   A future reader may "repair" a break by assembling a component isomorphism
   and thereby lose the definitional identity that makes the transport free.

3. **Namespace collision on the next anchor-pin bump** — P2-2. The build error
   would be loud; the checklist meant to anticipate it is blind.

4. **A downstream author may build machinery that the `IsIso` strengthening
   makes unnecessary** — P2-3. Nothing in the build tells them the epi half is
   six lines away.

5. **Source faithfulness is untouched, and no gate here speaks to it.** The
   audit, the linters, the census, the coverage registry and the emitter are
   all machine-hygiene instruments. `human_review: none` stands. This review is
   a machine review; it does not close issue #89, and it is not the owner-only
   judgement.

---

*Reviewed by Fable. Independent machine review of snapshot
`c7ad6ab249eb7f0a1b890a4c9ff5484b4091c7cf`, 2026-08-10. No repository file was
modified during the review.*
