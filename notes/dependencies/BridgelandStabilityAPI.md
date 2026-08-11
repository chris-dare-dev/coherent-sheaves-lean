# Foundational library API map

Produced by reading the pinned checkout at
`.lake/packages/BridgelandStability/` (commit `9e48f23`) directly. Every
signature below is copied from source, not recalled. Line references are to
that checkout.

Step 3 is "the `G̃L⁺(2, ℝ)` action on stability conditions". This file exists
because that step is the first one that imports the foundational library, and guessing at
its API costs a full rebuild per guess.

---

## 1. The three types

All live in namespace `CategoryTheory.Triangulated`.

### `Slicing C` — `Slicing/Defs.lean:82`

```lean
structure Slicing where
  P : ℝ → ObjectProperty C
  closedUnderIso : ∀ (φ : ℝ), (P φ).IsClosedUnderIsomorphisms
  zero_mem : ∀ (φ : ℝ), (P φ) (0 : C)
  shift_iff : ∀ (φ : ℝ) (X : C), (P φ) X ↔ (P (φ + 1)) (X⟦(1 : ℤ)⟧)
  hom_vanishing : ∀ (φ₁ φ₂ : ℝ) (A B : C),
    φ₂ < φ₁ → (P φ₁) A → (P φ₂) B → ∀ (f : A ⟶ B), f = 0
  hn_exists : ∀ (E : C), Nonempty (HNFiltration C P E)
```

**`Slicing.ext` already exists** (`Slicing/Defs.lean:99`). Do not write another
one. Note its elaborated signature takes `C` **explicitly**:

```lean
Slicing.ext : ∀ (C : Type u_2) [...] {s t : Slicing C}, s.P = t.P → s = t
```

so it is `Slicing.ext C hP`, not `Slicing.ext hP`.

### `PreStabilityCondition.WithClassMap C v` — `StabilityCondition/Defs.lean:60`

```lean
structure WithClassMap (v : K₀ C →+ Λ) where
  slicing : Slicing C
  Z : Λ →+ ℂ
  compat' : ∀ (φ : ℝ) (E : C), slicing.P φ E → ¬IsZero E →
    ∃ (m : ℝ), 0 < m ∧
      Z (v (K₀.of C E)) = ↑m * Complex.exp (↑(Real.pi * φ) * Complex.I)
```

### `StabilityCondition.WithClassMap C v` — `StabilityCondition/Defs.lean:126`

```lean
structure WithClassMap (v : K₀ C →+ Λ)
    extends PreStabilityCondition.WithClassMap C v where
  locallyFinite : slicing.IsLocallyFinite C
```

### Typeclass context to copy verbatim

```lean
variable (C : Type u) [Category.{v} C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]
variable {Λ : Type u'} [AddCommGroup Λ]
```

**Verified against elaborated signatures, not the source `variable` lines** —
the file-level `variable` block is misleading here:

| Type | needs `[IsTriangulated C]`? |
|---|---|
| `Slicing C` | no |
| `HNFiltration` | no |
| `PreStabilityCondition.WithClassMap` | **no** |
| `StabilityCondition.WithClassMap` | **yes** |

`StabilityCondition/Defs.lean` declares `[IsTriangulated C]` at file scope, but
many declarations carry `omit [IsTriangulated C]`, and
`PreStabilityCondition.WithClassMap` is one that does not need it. So 3a and 3b
can be stated without it; only 3c requires it.

---

## 2. The action, and why the conventions line up

For `x = (T, f) : GLTilde` acting on `σ = (P, Z)`:

- **slicing:** `P' φ := P (f⁻¹ φ)`
- **charge:** `Z' := T ∘ Z`

`f⁻¹` (not `f`) is what makes this a *left* action: `f⁻¹ ∘ h⁻¹ = (h ∘ f)⁻¹`,
and `h * f` in `NormalizedShift` is `h` after `f`. Verified by hand; make it a
test.

### Compatibility is consistent — worked through

Assume `P' φ E`, i.e. `P (f⁻¹ φ) E`. Old `compat'` at phase `f⁻¹ φ` gives
`Z (v[E]) = m · exp(iπ f⁻¹φ)` with `m > 0`. Then

```
Z' (v[E]) = T (m · exp(iπ f⁻¹φ)) = m · T(exp(iπ f⁻¹φ))       (ℝ-linearity, m real)
          = m · r · exp(iπ · f(f⁻¹φ))                        (GLTilde compat)
          = (m·r) · exp(iπφ),      m·r > 0                    ✓
```

The middle step is exactly `Compatible`. So step 2 was the right shape.

### Axiom-by-axiom cost for the new slicing

| Axiom | What it needs | Cost |
|---|---|---|
| `closedUnderIso` | reindexing only | free |
| `zero_mem` | reindexing only | free |
| `shift_iff` | `f⁻¹ (φ + 1) = f⁻¹ φ + 1` | **`NormalizedShift.symm_map_add_one`** |
| `hom_vanishing` | `φ₂ < φ₁ → f⁻¹φ₂ < f⁻¹φ₁` | free from `≃o` |
| `hn_exists` | transport `HNFiltration` | small, see below |

**`shift_iff` is why step 1 exists.** `symm_map_add_one` was proved before
there was any consumer for it; this is the consumer. That is the single
load-bearing link between the `+1`-equivariance condition and Bridgeland's
shift axiom.

### Transporting an `HNFiltration` — `Slicing/Defs.lean:66`

```lean
structure HNFiltration (P : ℝ → ObjectProperty C) (E : C)
    extends PostnikovTower C E where
  φ : Fin n → ℝ
  hφ : StrictAnti φ
  semistable : ∀ j, (P (φ j)) (toPostnikovTower.factor j)
```

`PostnikovTower` (`PostnikovTower/Defs.lean:63`) carries **no phase data** —
chain, triangles, base/top isos only. So transport keeps the tower untouched
and replaces `φ` with `f ∘ φ`. `StrictAnti` survives because `f` is strictly
monotone. `semistable` is then definitional: `P' (f (φ j)) = P (f⁻¹ (f (φ j)))
= P (φ j)`.

---

## 3. The impedance mismatch — read this before writing code

**`Z : Λ →+ ℂ` maps into `ℂ`. `GLTilde.mat` acts on `Fin 2 → ℝ`.**

These do not compose. This is the one real architectural finding of the read.

The bridge exists in Mathlib and the coordinate conventions already agree:

- `Complex.basisOneI : Basis (Fin 2) ℝ ℂ` — `LinearAlgebra/Complex/Module.lean:133`
- `Complex.coe_basisOneI_repr (z : ℂ) : ⇑(basisOneI.repr z) = ![z.re, z.im]` — `:145`, and it is `rfl`
- `Complex.exp_mul_I : exp (x * I) = cos x + sin x * I` — `Analysis/Complex/Trigonometric.lean:519`

So coordinate `0` is the real part, coordinate `1` the imaginary part, and

```
basisOneI.repr (Complex.exp (↑(π * φ) * I)) = ![cos (π*φ), sin (π*φ)] = rayVec φ
```

### RESOLVED — this risk is retired

This was the largest identified risk in the step, so it was closed
immediately rather than left as a note.
`BridgelandStabLean/StabilityCondition/Symmetry/GLTilde/ComplexRepresentation.lean` now carries:

- `cplxCoord : ℂ ≃ₗ[ℝ] (Fin 2 → ℝ)` — `Complex.basisOneI.equivFun`
- `cplxCoord_exp : cplxCoord (exp (↑(π * φ) * I)) = rayVec φ` — **proved**
- `compat_exp` — `Compatible` restated on the foundational library's `exp (i π ·)` rays,
  which is the form step 3b consumes

So option **A** below is taken, and option B is not needed.

Two traps found while proving it, both costly to rediscover:

- **Do not use `simp`.** It normalises `↑(π * φ)` into `↑π * ↑φ`, after which
  `Complex.exp_ofReal_mul_I_re` no longer matches. Use `rw` throughout.
- **`Basis.equivFun_apply` does not resolve** from our import set, despite
  existing at `LinearAlgebra/Basis/Defs.lean:245`. It is `rfl`, so go through
  `Complex.basisOneI.repr` with a `show` instead.

`Analysis/Complex/Isometry.lean:149-162` remains the worked template if the
full matrix-↔-`ℂ`-linear-map translation is ever needed, determinants included
(`LinearMap.toMatrix basisOneI basisOneI`, `LinearMap.det_toMatrix`).

### The two options, for the record

- **A — keep matrices, bridge at the boundary.** Taken. Keeps
  `Matrix.GLPos`'s free group structure; `Fin 2 → ℝ` never has to appear
  downstream of `ComplexBridge`.
- **B — refactor `GLTilde` onto `ℂ ≃ₗ[ℝ] ℂ`.** Not needed. It would have
  discarded `Matrix.GLPos` and re-done step 2's closure proofs, and
  "GL⁺(2, ℝ)" is literally matrices in Bridgeland's presentation.

---

## 4. The hard part: local finiteness

`Slicing.IsLocallyFinite` — `IntervalCategory/FiniteLength.lean:268`

```lean
structure Slicing.IsLocallyFinite (s : Slicing C) : Prop where
  intervalFinite : ∃ η : ℝ, ∃ hη : 0 < η, ∃ hη' : η < 1 / 2, ∀ t : ℝ, ...
    ∀ (E : s.IntervalCat C a b), IsStrictArtinianObject E ∧ IsStrictNoetherianObject E
```
with `a := t - η`, `b := t + η`.

**A single uniform `η` is quantified over all `t`.** A general normalized shift
distorts intervals, so `(t-η, t+η)` does not map to a window of any fixed
width.

### Two of the three pieces are now proved

- **Uniform continuity.** `StabilityCondition/Phase/UniformContinuity.lean`:
  `NormalizedShift.uniformContinuous`, and the consumable form
  `NormalizedShift.exists_radius` — for any target width `w` and ceiling `M`
  there is a radius `η < M` such that *every* window `(t-η, t+η)` maps to an
  interval of width `< w`. One `η` for all centres `t`, which is exactly the
  quantifier shape `IsLocallyFinite` demands. Continuity alone is free
  (`OrderIso.continuous`); uniformity comes from `map_add_one` via
  `map_add_int` and a modulus fixed on the compact `[-1, 2]`.
- **Interval reindexing.** `StabilityCondition/Symmetry/GLTilde/Action/Slicing.lean`:
  `relabel_intervalProp` proves
  `(f • s).intervalProp C a b = s.intervalProp C (f⁻¹ a) (f⁻¹ b)` — an
  equality of `ObjectProperty`, not merely an equivalence. The interval
  subcategories match on the nose; there is no structure to transport.

### The third piece — CORRECTION: it was in the foundational library all along

> **This section previously claimed the restriction lemma did not exist in the
> foundational library. That was wrong.** The search behind it covered `IntervalCategory/`
> and `QuasiAbelian/` but not `Deformation/`, where the lemma lives. 3c was
> never blocked. Corrected 2026-08-03; the reasoning below is kept because the
> reduction it describes is still exactly how the proof goes.

The lemma is **`interval_thinFiniteLength_of_inclusion_strict`**
(`Deformation/IntervalSelection.lean:354`), and it is stated for two
*different* slicings — precisely the shape phase relabelling produces:

```lean
theorem interval_thinFiniteLength_of_inclusion_strict
    {s₁ s₂ : Slicing C} {a₁ b₁ a₂ b₂ : ℝ}
    [Fact (a₁ < b₁)] [Fact (b₁ - a₁ ≤ 1)] [Fact (a₂ < b₂)] [Fact (b₂ - a₂ ≤ 1)]
    (h : s₁.intervalProp C a₁ b₁ ≤ s₂.intervalProp C a₂ b₂)
    (hFinite : ∀ Y : s₂.IntervalCat C a₂ b₂,
      IsStrictArtinianObject Y ∧ IsStrictNoetherianObject Y) :
    ∀ X : s₁.IntervalCat C a₁ b₁,
      IsStrictArtinianObject X ∧ IsStrictNoetherianObject X
```

Take the `_strict` variants, not the plain ones: the plain
`interval_strictArtinianObject_of_inclusion` wants `IsArtinianObject` of the
image (DCC on *all* subobjects), which is strictly stronger than what
`IsLocallyFinite` hands you. The whole `_strict` family sits at
`IntervalSelection.lean:206-372`, resting on `intervalInclusion_map_strictMono`
(`:121`), which transports strict monos via the cokernel's distinguished
triangle.

The lesson for future reads: **`Deformation/` is not only deformation theory.**
It carries general interval-category infrastructure that the
`IntervalCategory/` tree does not.

### The reduction (still accurate)

Combining the two above gets you: the objects of
`(f • s).IntervalCat C (t-η') (t+η')` are the objects of
`s.IntervalCat C a' b'` where `a' := f⁻¹(t-η')`, `b' := f⁻¹(t+η')` and
`b' - a' < 2η`. Setting `u := (a'+b')/2` gives `(a', b') ⊆ (u-η, u+η)`.

The hypothesis supplies finite length for `s.IntervalCat C (u-η) (u+η)`. What
is needed is finite length for `s.IntervalCat C a' b'` — a **full subcategory**
of it. So 3c reduces to exactly one missing lemma:

> `IsStrictArtinianObject` / `IsStrictNoetherianObject` restrict along the
> inclusion `s.IntervalCat C a' b' ⥤ s.IntervalCat C a b` for
> `a ≤ a'`, `b' ≤ b`.

`s.intervalProp_mono` turns that containment into the `h` argument above, and
the foundational library's lemma finishes it. `StabilityCondition/Symmetry/GLTilde/Action/Stability.lean`'s
`relabel_isLocallyFinite` is exactly this argument in Lean.

Note `IsLocallyFinite`'s docstring remark that shrinking a witness is
"harmless" — that is backed by the `_strict` family, not merely asserted.

---

## 5. Recommended staging

Do not attempt step 3 as one milestone.

1. ~~**3a — action on `Slicing`.**~~ **Done** (2026-08-03) —
   `StabilityCondition/Symmetry/GLTilde/Action/Slicing.lean`. `MulAction NormalizedShift (Slicing C)`
   with `one_smul` and `mul_smul` proved, and `MulAction GLTilde (Slicing C)`
   through `MulAction.compHom GLTilde.toShiftHom`. The §2 table held exactly:
   only `shift_iff` and `hn_exists` had content.

   One gotcha: inside the `MulAction` instance's own elaboration `•` stays
   opaque, so `relabel_P` cannot match and `simp` reports "no progress". Add
   `show (relabel C … ).P φ = …` before the `simp` in `one_smul`/`mul_smul`.
2. ~~**3b — action on `PreStabilityCondition.WithClassMap`.**~~ **Done**
   (2026-08-03) — `StabilityCondition/Symmetry/GLTilde/Action/PreStability.lean`, with `actC` and
   `actC_exp` added to `ComplexBridge`. `MulAction GLTilde (…WithClassMap C v)`
   with both laws proved. The `compat'` computation went exactly as worked
   through in §2: `m` becomes `m * r`. As predicted, `[IsTriangulated C]` was
   not needed.

   Three gotchas:
   - **`PreStabilityCondition.WithClassMap.ext` is in
     `StabilityCondition/Basic.lean`, not `Defs.lean`.** Import `.Basic`. The
     auto-generated structure `ext` is useless here — it would demand equality
     of the `compat'` proofs.
   - **`smul_smul` will not match `m • r • z` on `ℂ`** — the two scalar
     actions sit on different instance paths. Convert out of `•` with
     `Complex.real_smul`, then `push_cast; ring`.
   - **`simp` will not close `↑c * w = c • w`** — it normalises `•` into `*`,
     which is the direction you already have. Finish with
     `exact Complex.real_smul.symm`.
3. ~~**3c — action on `StabilityCondition.WithClassMap`.**~~ **Done**
   (2026-08-03) — `StabilityCondition/Symmetry/GLTilde/Action/Stability.lean`.
   `MulAction GLTilde (StabilityCondition.WithClassMap C v)`, both laws proved.
   `relabel_isLocallyFinite` closes local finiteness from three ingredients:
   `exists_radius` (uniform continuity), `relabel_intervalProp` (exact
   reindexing), and the foundational library's own
   `interval_thinFiniteLength_of_inclusion_strict`.

   It was briefly recorded here as blocked; see the correction in §4.

**The §8 `G̃L⁺(2, ℝ)` action is complete.** Still absent: the covering-space
identification of `GLTilde` (see `known_divergences` in `formalization.yaml`),
and the `Aut` half — begun, see below.

---

## 7. The `Aut` track

`G̃L⁺(2, ℝ)` moves phases and fixes objects; an autoequivalence does the
opposite. The foundational library has **no functor-transport machinery whatsoever** — only
`HNFiltration.ofIso`, along an isomorphism of the filtered *object*. So this
track is built from scratch.

**Landed** (`StabilityCondition/Symmetry/Autoequivalence/Slicing/Transport.lean`, 2026-08-03):

- `PostnikovTower.mapF` — push a tower through a triangulated functor. Went
  through unchanged on the first attempt: `ComposableArrows C n` is a functor
  category, so the transported chain is literally `chain ⋙ F`, every
  `obj'`/`left`/`right` projection commutes definitionally, and
  `Functor.IsTriangulated.map_distinguished` carries distinguishedness.
- `HNFiltration.mapF` — tower plus untouched phases; only `semistable` argues.
- `Slicing.mapEquiv` — `(Φ • s).P φ X = s.P φ (Φ⁻¹ X)`.

Three API notes that cost build cycles:

- `Functor.IsTriangulated` needs `import Mathlib.CategoryTheory.Triangulated.Functor`
  and `Equivalence.CommShift` needs `Mathlib.CategoryTheory.Shift.Adjunction`.
- `Equivalence.CommShift ℤ` does **not** yield `Φ.functor.CommShift ℤ` by
  instance search. Require the two functor-level instances directly.
- `ObjectProperty.prop_of_iso` takes the property **explicitly**
  (`prop_of_iso _ e h`), and `HNFiltration.ofIso` takes `C` explicitly.

**Packaging: resolved by restriction** (owner decision, 2026-08-03). `C ≌ C` is
associative only up to natural isomorphism, so it has no `Group` instance.
Rather than quotient to isomorphism classes, `StabilityCondition/Symmetry/Autoequivalence/Slicing/Strict.lean`
asks for a group that maps into endofunctors **strictly** — which works because
**functor composition in Lean is strictly associative**, so `C ⥤ C` is an
honest monoid under `⋙`:

```lean
structure StrictAut (G) [Group G] (C) … where
  F : G → (C ⥤ C)
  map_one : F 1 = 𝟭 C
  map_mul : ∀ g h, F (g * h) = F h ⋙ F g      -- ⋙ is diagrammatic order
  additive / commShift / triangulated : ∀ g, …
```

That yields a genuine `MulAction G (Slicing C)`, with
`(g • s).P φ X = s.P φ (g⁻¹ X)` — dual to `relabel`. `StrictAut.equiv` turns
the strict data into an `Equivalence` (unit/counit are `eqToIso`; the coherence
field discharges automatically), so all of `Slicing.mapEquiv` is reused.

**The restriction is real, not cosmetic.** `map_one`/`map_mul` are *equalities
of functors*, so `F g ⋙ F g⁻¹ = 𝟭 C` on the nose: each `F g` is an
**isomorphism of categories**, not merely an equivalence. Serre functors and
spherical twists satisfy that only up to natural isomorphism and are therefore
**out of scope for `StrictAut`**.

### Superseded: the quotient landed too

`StabilityCondition/Symmetry/Autoequivalence/Slicing/Quotient.lean` (2026-08-03) does the general construction, so
`StrictAut` is now the cheap special case rather than the only option.
`AutQuot C` — triangulated auto-equivalences modulo natural isomorphism — is a
genuine `Group` with `MulAction (AutQuot C) (Slicing C)`, and **excludes
nothing**.

The mathematical content is one short lemma, `TriEquiv.act_congr`: if
`Φ⁻¹ ≅ Ψ⁻¹` then `Φ⁻¹ X ≅ Ψ⁻¹ X` for every `X`, so `s.P φ (Φ⁻¹ X)` and
`s.P φ (Ψ⁻¹ X)` are equivalent propositions — because `Slicing.closedUnderIso`
says so — and `propext` upgrades that to *equality*. So the two slicings are
equal on the nose. **`closedUnderIso`, which reads like bookkeeping in the
`Slicing` axioms, is exactly what makes the quotient action well defined.**

The group laws split revealingly: `mul_assoc`, `one_mul`, `mul_one` are all
`Iso.refl`, because functor composition is strictly associative with `𝟭` a
strict unit. Only `inv_mul_cancel` needs a real natural isomorphism
(`unitIso.symm`) — which is precisely the one place strictness fails, and
precisely what quotienting fixes.

The setoid now asks only for `functor ≅ functor`, the standard relation.
`TriEquiv.inverseIsoOfFunctorIso` uses uniqueness of right adjoints to derive
`inverse ≅ inverse` wherever inversion needs it. This removes the earlier
artificially finer two-component relation without changing the action proof.

Also: `AutQuot` is a plain `def`, so `Quotient.mk` alone does not carry enough
type information for `•` to find its instance — use `AutQuot.mk`.

Two implementation notes: the instance `letI`s in `actSlicing` must state each
instance at the `(ρ.equiv g).functor` form (search will not unfold it to
`ρ.F g`), and must be `letI` rather than `haveI` — `Functor.IsTriangulated`
depends on the `CommShift` instance, and an opaque `haveI` breaks the match.

### Scouting the three remaining pieces (2026-08-03)

**1. `K₀` functoriality — DONE, and it was nearly free.**
`StabilityCondition/Symmetry/Autoequivalence/Foundations/GrothendieckGroup.lean`. `K₀.lift` wants an `IsTriangleAdditive` function,
and `X ↦ [F X]` is one whenever `F` is triangulated: `F.map_distinguished`
carries the triangle and `(F.mapTriangle.obj T).obj₁` is *definitionally*
`F.obj T.obj₁`. So the instance is one line and `mapF_id` / `mapF_comp` /
`mapF_congr` are `ext; simp`. `mapF_congr` — naturally isomorphic functors
induce the same map, via `K₀.of_iso` — is the `K₀`-level analogue of
`TriEquiv.act_congr` and is what will make the class-map half descend to
`AutQuot`.

**2. Class-map compatibility — a design choice, not a difficulty.** An
autoequivalence acts on `WithClassMap C v` only paired with `λ : Λ ≃+ Λ`
satisfying `v ∘ K₀.mapF Φ = λ ∘ v`. Forced when `v = id`; extra data otherwise.
Structurally the same move `Compatible` makes for `GLTilde`, and now that
`K₀.mapF` exists there is nothing missing — only the decision about how to
bundle it.

**3. Strict finite length under an equivalence — centrepiece DONE, assembly
remains.** `StabilityCondition/Symmetry/Autoequivalence/Foundations/FiniteLength.lean` (2026-08-03) extracts the
general lemma:

```lean
isStrictArtinian_of_faithful_strict
    (F : A ⥤ D) [F.Full] [F.Faithful]
    (hF   : ∀ f, IsStrictMono f → IsStrictMono (F.map f))
    (harr : ∀ f [Mono f], IsStrictMono f → IsStrictMono (Subobject.mk f).arrow)
    {E} [IsStrictArtinianObject (F.obj E)] : IsStrictArtinianObject E
```

plus the Noetherian twin, for an **arbitrary** functor — the foundational library's own two
interval lemmas are instances. Also landed: `mapEquiv_intervalProp_iff`, which
records that under `Aut` the interval endpoints do **not** move.

The `harr` hypothesis cannot be dropped. It needs strict monos closed under
composition, and strict-mono composition is **not** available in general — the
foundational library proves it only for interval categories
(`Slicing.IntervalCat.comp_strictMono`, `IntervalCategory/FiniteLength.lean:189`).
Callers with an interval target discharge it via
`intervalSubobject_arrow_strictMono_of_strictMono`.

Two API notes: the foundational library's own helpers (`strictSubobjectImageOfFaithful` and
friends, `QuasiAbelian/Basic.lean:638-684`) are `private`, so they had to be
replicated rather than reused; and a theorem whose *statement* does not mention
`hF`/`harr` needs an explicit `include hF harr in`, placed **before** the
docstring.

**ASSEMBLED** (2026-08-04) — `StabilityCondition/Symmetry/Autoequivalence/Stability/Transport.lean`. All three
predicted steps went through as written:

- `autIntervalFunctor` — `Φ⁻¹` restricted, via `ObjectProperty.lift`. Declared
  `abbrev`, not `def`: instance search must see through it to reach the
  underlying lift's `Full`/`Faithful` instances.
- `autFunctor_strictMono` — the cone route, exactly as predicted. `simpa`
  against `Φ.inverse.map_distinguished` closed it first try, with
  `δ := Φ.inverse.map δ ≫ (Φ.inverse.commShiftIso 1).hom.app _`.
- `mapEquiv_isLocallyFinite` — same `η`, no `exists_radius`.
- `actStabAut` — the action itself, with the class-lattice datum.

Two gotchas worth keeping. The foundational library's `exists_distTriang_of_strictShortExact`
and `strictMono_strictEpi_of_distTriang` take the **slicing explicitly**, and
the source-side one wants `s.mapEquiv Φ`, not `s`. And `IsLocallyFinite`'s
statement carries its own `let a := t - η` bindings, so a bare `intro E` after
`intro t` consumes the *let* rather than the object — `show` past them.

The `compat'` obligation costs nothing here: the witness `m` is **unchanged**,
because an autoequivalence moves an object without moving its phase. Contrast
`G̃L⁺(2, ℝ)`, where the matrix rescales the ray and `m` becomes `m * r`.

**Not a `MulAction` — done in `StabilityCondition/Symmetry/Autoequivalence/Stability/ClassMap.lean` (2026-08-04).** The acting
object is a pair `(Φ, lam)`; `AutQuot` groups the `Φ`s alone, which suffices
for slicings but not once a class lattice is in play. `AutPair v` bundles both
and `AutPairQuot v` acts.

This paragraph used to end "and it is packaging, not mathematics". Kept,
because the correction is the useful part — it was wrong on two counts.

1. **A group forces `lam : Λ ≃+ Λ`.** `actStabAut` needs only `Λ →+ Λ`;
   `lam⁻¹` has no source, because `v` is arbitrary. So the group action rests
   on a *strictly stronger* hypothesis and `actStabAut` is not superseded by
   it — a non-invertible compatible datum still acts as a map.
2. **The inverse's `compat` needs an equality, not an isomorphism.**
   `Φ.functor ⋙ Φ.inverse ≅ 𝟭 C` is only a natural isomorphism;
   `K₀.mapF_congr` is what promotes it to an equality of maps on `K₀`, and
   without that the datum cannot cross to `Φ⁻¹`. This is the one step in the
   file that uses `Φ` being an equivalence at all.

Also settled there: `lam` is **not** quotiented, since two `lam`s over one `Φ`
give different `σ.Z ∘ lam` whenever `v` is not surjective.

### Original assessment, for the record

- The foundational library's general transfer lemma
  `isStrictArtinianObject_of_faithful_map_strictMono`
  (`QuasiAbelian/Basic.lean:691`) applies to any full+faithful strict-mono-preserving
  functor — but it wants **ordinary** `IsArtinianObject` of the image, which is
  strictly stronger than what `IsLocallyFinite` supplies. The *strict*-hypothesis
  versions exist only as the interval-specific
  `interval_strictArtinianObject_of_inclusion_strict`
  (`Deformation/IntervalSelection.lean:206`, and the Noetherian twin at `:274`),
  and each **hand-rolls a ~70-line `StrictSubobject` order-embedding** rather
  than calling a general helper. Extracting that argument into a general
  strict-hypothesis lemma is the first sub-part.
- Then: `Φ` induces a full+faithful functor
  `(Φ • s).IntervalCat C a b ⥤ s.IntervalCat C a b` — note the endpoints do
  **not** move, unlike step 3c — and it must be shown to preserve strict monos.
  Since `IsStrict` is defined by the coimage-image comparison, this needs that
  comparison to transfer along an equivalence.

Estimate: ~150+ lines. This is the piece to budget for; the other two are done
or decided.

Done for stability conditions (2026-08-04), all three:

1. `K₀` functoriality — `K₀.mapF` (`StabilityCondition/Symmetry/Autoequivalence/Foundations/GrothendieckGroup.lean`).
2. Class-map compatibility — `actStabAut`'s `lam` + `hlam` arguments.
3. Strict finite length under an equivalence — `mapEquiv_isLocallyFinite`,
   resting on the general `isStrictArtinian_of_faithful_strict`.

Prove the `MulAction` laws (`one_smul`, `mul_smul`) at each stage rather than
at the end — 3a's are cheap and will catch a wrong `f` vs `f⁻¹` convention
immediately, which is the failure mode most likely to survive typechecking.

---

## 8. Joint topology of the symmetry action (2026-08-06)

The fixed-element homeomorphisms in `StabilityCondition/Symmetry/Combined/Topology.lean` and
`StabilityCondition/Symmetry/GLTilde/Action/Continuous.lean` are now strengthened in
`StabilityCondition/Symmetry/GLTilde/Action/JointContinuous.lean`.

The key identity-neighborhood estimates are:

- `GLTilde.eventually_uniform_shift_displacement`: near `1`,
  `|x.shift φ - φ|` is uniformly small for every `φ`. Joint phase
  evaluation is continuous, compactness gives a uniform neighborhood on
  `[0,1]`, and `NormalizedShift.map_add_int` transfers it to all of `ℝ`.
- `GLTilde.continuous_actCCLM`: `x ↦ actCCLM x.mat` is continuous in operator
  norm. Finite-dimensionality reduces this to continuity after evaluation at
  every `z : ℂ`.
- `stabSeminorm_near_identity_le`: the transformed seminorm is bounded by the
  old seminorm times `‖actCCLM x.mat‖`, plus
  `‖actCCLM x.mat - id‖`.
- `exists_identity_basisNhd_control`: those estimates give one source
  `basisNhd` working uniformly for all sufficiently small group elements.

`continuousAt_smul_identity` proves continuity at `(1,σ)`. The factorization
`x • τ = x₀ • ((x₀⁻¹ * x) • τ)` then gives
`ContinuousSMul GLTilde (StabilityCondition.WithClassMap C v)` globally.

For the autoequivalence factor the topology is an explicit design choice:
`AutPairQuot v` is given the discrete topology, the standard topology when it
is used as a symmetry group here. Its action is therefore jointly continuous,
and the commuting product action receives `ContinuousSMul` as well. This does
not assert a moduli topology on autoequivalences or identify `AutPairQuot v`
with an external `Aut(D)`.

---

## 9. Component transport, period equivariance, and the effective quotient (2026-08-06)

The three-milestone chain following the joint action is complete.

1. `StabilityCondition/Symmetry/Combined/Components.lean` defines the induced action on
   `ConnectedComponents X` for any group action with `ContinuousConstSMul`.
   It proves exact transport of connected components, constructs the
   restricted `Homeomorph` between component subtypes, and gives the component
   stabilizer its action on the chosen component.
2. `StabilityCondition/Symmetry/Combined/PeriodMap.lean` defines the additive charge-space
   equivalences. `GLTilde` postcomposes a charge by `actC`; `AutPairQuot v`
   precomposes by its lattice automorphism. The central-charge map is
   equivariant for each factor and their product, and the same square is
   stated for the foundational library's canonical componentwise local-model chart after
   coercion to the ambient charge group. The `GLTilde` operation is only
   asserted additive/real-linear here, not complex-linear.
3. `StabilityCondition/Symmetry/Combined/Effective.lean` bundles the even shift functors as triangulated
   equivalences, proves that `[2]` is trivial on `K₀`, and resolves the action
   convention:

   ```text
   shiftTwoPair.act = deck (-1)
   (deck 1, [2]) acts trivially.
   ```

   `EffectiveCombinedSymmetry v` is the product symmetry group modulo the
   full kernel of its action on stability conditions. The induced action is
   faithful by construction, and the explicit deck/double-shift overlap maps
   to the identity. There is intentionally no theorem that this overlap
   generates the whole kernel; extra category-specific ineffective
   symmetries remain possible.

---

## 10. HN mass, the three-coordinate distance, and full invariance (2026-08-06)

The foundational library supplies `HNFiltration`, intrinsic `phiPlus`/`phiMinus`, and the
phase-only `slicingDist`, but no mass definition and no exposed factorwise
uniqueness theorem for complete HN filtrations. The metric chain begins with a
choice-free envelope rather than choosing a filtration non-functorially.

1. `StabilityCondition/Metric/Mass/Basic.lean`
   - `HNFiltration.mass σ F = ∑ i, ofReal ‖σ.charge (F.factor i)‖`;
   - `stabilityMass σ E = ⨆ F, F.mass σ` over every HN filtration of `E`;
   - positivity on nonzero objects and invariance under object isomorphism;
   - exact backward/forward filtration-mass transport and
     `AutPair.act_stabilityMass`.
2. `StabilityCondition/Metric/Mass/Uniqueness.lean`
   - constructs the head-factor/tail triangle by octahedral induction;
   - uses the half-open t-structure at the common leading phase to identify
     the head and tail objects of two filtrations;
   - proves `HNFiltration.mass_eq_mass`, `stabilityMass_eq_mass`, finiteness,
     the literal real finite-sum formula, and vanishing exactly on zero objects.
3. `StabilityCondition/Metric/Distance/Basic.lean`
   - `logMassDist` agrees with the ordinary absolute log difference on finite
     masses and treats `⊤` as infinitely far from finite values;
   - `stabilityDistTerm` is the maximum of the `φ⁺`, `φ⁻`, and mass
     discrepancies;
   - `massDist_eq_abs_log_ratio` identifies the mass coordinate with the
     paper's literal absolute log-ratio on nonzero objects;
   - `stabilityDist` is the supremum over nonzero objects;
   - reflexivity, symmetry, triangle inequality, and
     `slicingDist_le_stabilityDist` are proved.
4. `StabilityCondition/Metric/Isometry/Full.lean`
   - transports each coordinate through `Φ⁻¹`;
   - proves `AutPair.act_stabilityDist` by the two pointwise supremum bounds;
   - descends to `AutPairQuot_smul_stabilityDist`.
5. `StabilityCondition/Metric/Distance/Separation.lean`
   - extracts equality of intrinsic phases and real masses from distance zero;
   - reconstructs the slicing and every object charge;
   - proves equality of `Z.comp v` without assumptions and literal separation
     when `v` is surjective;
   - specializes to unconditional separation for ordinary stability
     conditions over `K₀ C`.
6. `StabilityCondition/Metric/Distance/Topology.lean`
   - proves strict full-distance control of phases, mass ratios, and the
     central charge, plus the sector estimates needed in the reverse
     comparison;
   - proves that full-distance balls refine Section 6 neighborhoods
     unconditionally;
   - derives the reverse refinement, equality of neighborhood bases, and the
     compatible extended-metric constructors from the single explicit
     proposition `StabilityMassTriangleInequality`;
   - constructs through `PseudoEMetricSpace.ofEDistOfTopology` and proves by
     `rfl` that the inherited topology is the existing Section 6 topology, so
     no topology/typeclass diamond is introduced.
7. `StabilityCondition/Metric/Mass/Subadditivity/Triangle.lean`
   - defines the ordinary observable stability condition with central charge
     `Z.comp v`, making the foundational library's heart stability-function and HN APIs
     available for arbitrary class maps;
   - proves the universal charge lower bound `‖Z(E)‖ ≤ mσ(E)` and charge
     additivity on distinguished triangles, together with mass invariance
     under shifts by `1` and `-1`;
   - proves mass subadditivity for semistable middle objects and for
     same-phase semistable endpoints;
   - transports both cases to short exact sequences in `P((0, 1])`;
   - proves the phase-one boundary-heart inequality, the six-term
     cohomological comparison on `(0, 2]`, the two exact HN cutoffs, and hence
     the arbitrary-phase semistable-left triangle inequality;
   - retains the unrestricted heart short-exact proposition as an explicit
     target for the final global-triangle corollary.
8. `StabilityCondition/Metric/Mass/Subadditivity/HNPolygon.lean`
   - defines the HN polygon as the convex hull of all subobject charges;
   - realizes an abelian HN filtration as its distinguished complex path;
   - proves that successive path edges are the factor charges and that path
     length equals factor mass;
   - proves the endpoint chord bound needed by future refinement/perimeter
     arguments, but not yet HN-boundary extremality.
9. `StabilityCondition/Metric/Mass/Subadditivity/CohomologyExactness.lean`
   - packages the heart-source `H⁰` short complex;
   - identifies exactness with monicity of the canonical map from the
     cokernel of its first arrow;
   - proves the canonical `H⁰'` functor homological from nonpositive
     truncation and transports that structure to `H⁰`;
   - derives the heart-source exactness and monicity unconditionally without
     installing a global instance or assuming an extra input.

Items 8--9 follow the `t = 0` proof architecture of Ikeda,
*Mass growth of objects and categorical entropy*
([arXiv:1612.00995](https://arxiv.org/abs/1612.00995)): Lemma 3.8 is the
boundary-heart polygon step, and the proof of Proposition 3.3 is the subsequent
`H⁰` kernel/image reduction.

The mass bridge, separation clause, analytic topology estimates, and safe
metric-space construction are now closed. The boundary-heart and
semistable-left mass-triangle milestones are also closed, including the
unconditional `H⁰` homological bridge and the exact lower/upper HN cutoffs.
The arbitrary-left reduction is already proved; its one-step application to
the semistable-left theorem remains to expose the unconditional global
triangle proposition. Until that named corollary lands, all topology
comparison results remain explicitly conditional on the global proposition.
The citation to
Proposition 8.1 therefore remains `no_claim`. The Lemma 8.2 citation also
remains `no_claim`
independently, because `AutPairQuot v` is not identified with bare `Aut(D)`.

---

## 6. Open risks

- ~~**Module system.**~~ **RESOLVED.** The foundational library uses Lean's new module
  system (`module`, `public import`, `@[expose] public section`) and this
  repo's files do not. That is fine: a non-`module` file importing
  `BridgelandStability.StabilityCondition.Defs` sees every declaration listed
  above, with full signatures and no errors, and our own declarations coexist
  in the same file. No `module` migration is needed. (Probed
  2026-08-03 once the foundational library oleans existed — the earlier attempt failed only
  because nothing had ever built them.)
- **Build cost.** The foundational library is 74 files / ~35.7k LOC and is **not** covered
  by `lake exe cache get`, which is Mathlib-only. It also is not built by
  `lake build` unless something imports it — as of step 2 nothing did, so the
  first `lake build BridgelandStability` was a cold ~35k-LOC compile. It is
  built now. Avoid touching anything it depends on, and expect the first
  step-3 edit that imports it to be slower than the step-1/2 loop.
- **Universe variables.** The foundational library uses `universe v u u'` with `Λ : Type u'`.
  Our files have not needed explicit universes yet.
- **`autoImplicit false`.** Our `lakefile.toml` sets it (and
  `relaxedAutoImplicit`); the foundational library does not. Copied snippets may need
  explicit binders.
