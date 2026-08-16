# FM lane — adversarial review, round 2

Target: `origin/main` @ `aaa3cfe` (note: origin/main has since advanced to `3848537`;
review pinned at `aaa3cfe` per handoff — post-pin commits out of scope).
Worktree: `/tmp/fm-review` (branch `review/fm-lane`, reset to the pin).

## Baseline reproduced

- `lake build`: pass. `scripts/gates.sh`: **17/17 pass**.
- Both audit scripts clean — no `sorryAx` in StabilityCondition or AlgebraicGeometry closures.
- Spot `#print axioms` on `transformK₀_dual_comp`, `actStab_trans`,
  `pairing_mukaiVector_eq_on_realized_of_categorical`: exactly
  `[propext, Classical.choice, Quot.sound]`.
- Ratchet ceilings unmoved: AlgebraicGeometry 1098, StabilityCondition 383, DGCategory 0
  (`scripts/check_audit_complete.py:70-74`; `audit-complete` gate passes).
- Layering invariant holds: the only `CategoryTheory/` files outside `StabilityCondition/`
  importing `StabilityCondition.*` are the two umbrella files
  (`Triangulated.lean`, `Triangulated/StabilityCondition.lean`). No regression.

## Findings

### P1 — `PostnikovTower.zero_isZero` is a provable field (round-1 defect class 1)

**File:** `DerivedAlgGeo/CategoryTheory/Triangulated/PostnikovTower.lean:47`
**Claimed:** a structure field, i.e. a datum every constructor of a `PostnikovTower` must supply:
`zero_isZero : n = 0 → IsZero E`.
**Delivered / actual status:** it is a theorem of the *other fields*. When `n = 0`,
`chain.left` and `chain.right` are the same object of `ComposableArrows C 0`
(`Fin.last 0 = 0` by `Fin.ext`), so `base_isZero` transports across `top_iso` to give
`IsZero E`. Verified mechanically at the pin — this compiles with no `zero_isZero`:

```lean
example … (chain : ComposableArrows C 0)
    (base_isZero : IsZero chain.left) (top_iso : Nonempty (chain.right ≅ E)) :
    IsZero E := by
  have h0 : chain.right = chain.left := congrArg chain.obj (Fin.ext (by simp))
  exact (h0 ▸ base_isZero).of_iso top_iso.some.symm
```

This is exactly the `s`/`s_spec` pattern round 1 ranked P1: a proof obligation dressed as
supplied data. Every in-repo tower constructor (HN filtrations use this structure across
`Foundation/Slicing`, `Deformation`, `Weak/HarderNarasimhan` — 13 files reference the field)
pays a redundant obligation.
**Smallest change:** delete the field; add
`theorem PostnikovTower.isZero_of_length_zero {E} (P : PostnikovTower C E) (h : P.n = 0) : IsZero E`
proved as above, and drop the corresponding argument at construction sites.

### P2 — the lane's docstrings deny a group action the repository already has

**Files:** `…/Symmetry/Autoequivalence/FourierMukai.lean:46-48` and
`…/Symmetry/Autoequivalence/Stability/Composition.lean:34-37`
**Claimed:** "No orbit, group action, or `MulAction` structure … there is no group here: no
identity law, and **no type of autoequivalences-with-lattice-data to be a group of**" (FourierMukai.lean);
"Turning it into an action needs a group of autoequivalences-with-lattice-data and an identity
law, **neither of which is here**" (Composition.lean).
**Delivered:** `…/Stability/ClassMap.lean` (pre-existing, imported transitively by both files via
`Stability/Transport.lean`, whose own docstring advertises it at line 65) defines precisely that
type and group: `GroupAction.AutPair v` (autoequivalence + `lam : Λ ≃+ Λ` + compat),
`AutPairQuot v : Group`, and
`MulAction (AutPairQuot v) (StabilityCondition.WithClassMap C v)` — identity law
(`act_id`), composition (`act_mul`), descent, the lot. So the answer to the handoff's claim 2
("confirm nothing elsewhere implies a `MulAction` is nearly present") is: **it is not nearly
present, it is present**, for the same transports (`act` is `actStabAut` with the pair bundled).
The lane's statements are true only under the narrowest reading of "here" (= this file), and
false as repo-level statements; a reader (or the next formalize-issue session) would
re-derive ClassMap. There is also literal duplication: `Slicing.mapEquiv_trans`
(Composition.lean:87) is `TriEquiv.act_comp` (Slicing/Quotient.lean:115) unbundled, both
`ext`-on-`rfl`.
**Smallest change:** reword both docstrings to point at ClassMap.lean — e.g. "the bundled
group action exists (`AutPairQuot v`, `Stability/ClassMap.lean`, needing `lam` invertible);
what is *not* here is a group of kernel autoequivalences: `trans` needs supplied
`ConvolutionData`, so kernel-tracked composition does not form a group and this theorem is
only its associativity clause." Optionally note the `mapEquiv_trans` / `act_comp` overlap.

### P2 — `IntegralMukaiData.b_comm` is demanded, never consumed, and half-provable

**File:** `DerivedAlgGeo/AlgebraicGeometry/Numerical/GrothendieckGroup/MukaiVector.lean:113-114`
**Claimed:** the geometric supplier must provide `b_comm : ∀ x y : Λ, b x y = b y x` —
global symmetry of the form on all of `Λ`.
**Delivered:** zero consumers. `b_comm` appears exactly once in the repository (its own
declaration). Every lane result goes through `Mukai.pairing`/`selfPairing`/`IsSpherical`/
`expectedDim`, none of which take symmetry; `Mukai.pairing_comm` takes symmetry as an
explicit *hypothesis* and is used only in `Lattice/Mukai/RankTwo.lean`, never with `D.b`.
Moreover the part of `b_comm` that the rest of the structure can see is already a theorem:
on the image of `c₁`, `b_spec` plus commutativity of `A` and `Int.cast_injective` give
`b (c₁ E) (c₁ F) = b (c₁ F) (c₁ E)`. So the field's *only* content is symmetry **off** the
image — exactly the region the docstring (lines 102-105) insists the structure says nothing
about ("deliberately weaker than a geometric lattice package"). The one global-quantifier
field in the structure contradicts its own minimality story, and inflates the named Layer-B
obligation for no downstream benefit.
**Smallest change:** delete the field (and, if symmetry-on-image is ever wanted, state it as
`theorem b_comm_on_realized` proved from `b_spec`). If the owner wants the field kept for
future `pairing_comm` use, the docstring must say it is currently unused and strictly
stronger than anything the file needs.

### P3 — `section Isometry` label contradicts the file's own central disclaimer

**File:** `…/Numerical/GrothendieckGroup/Realization.lean:165` (`section Isometry` … `end Isometry`:215)
The file's headline discipline — stated three times — is that these results are *not*
isometry statements, and round 1's P1 rename (`…_eq_of_preservesEuler`) enforced it.
The section wrapping exactly those theorems is named `Isometry`. Section names don't
surface in declaration names, so this is cosmetic — but it is the round-1 overclaim
surviving in an internal label. **Smallest change:** rename the section
(e.g. `PairingTransfer`).

### P3 — `Slicing.mapEquiv_trans` defeq dependency carries no pin-fragility note

**File:** `…/Stability/Composition.lean:83-91`
Verified (claim 4): the proof is `ext φ X; rfl` and works because Mathlib defines
`Equivalence.trans` with literal field `inverse := f.inverse ⋙ e.inverse`
(`Mathlib/CategoryTheory/Equivalence.lean:386-388` at the pin), so
`(Φ.trans Ψ).inverse` reduces by projection-of-constructor. The definition is old and
stable, so risk is low, but any Mathlib refactor of `Equivalence.trans` (e.g. via
adjointification) silently breaks this and `KernelAutoequivalence.actStab_trans` behind it.
The repo's own convention elsewhere is to flag such things ("Re-check this if the pin
moves", `Lattice/Mukai/Basic.lean:76`). **Smallest change:** one docstring sentence naming
the defeq being relied on.

### P3 — `K₀.mapF` is now fully subsumed by `K₀.map`, with duplicated API

**Files:** `…/Symmetry/Autoequivalence/Foundations/GrothendieckGroup.lean:53` (mapF, endo-only)
vs `…/Triangulated/GrothendieckGroup/Functorial.lean:38` (map, general — added by this lane).
Both are `K₀.lift C (fun X ↦ K₀.of C (F.obj X))`; the lane itself proves them equal by `rfl`
(`Symmetry/…/FourierMukai.lean:120`). Each has its own `_id`/`_comp`/`_congr`/`_of` quadruple.
Not wrong, but it is the same misfiling/duplication debt #453/#454 were opened for, created
in the opposite direction (generic API landed, specialized twin not retired).
**Smallest change:** file an issue to migrate the stability track from `mapF` to `map` and
delete `mapF`; until then, a docstring cross-reference on `mapF`.

### P3 — the composition theorem collapses kernel-category universes

**File:** `…/Symmetry/Autoequivalence/FourierMukai.lean:268-274`
`FourierMukai/Basic.lean` and `Convolution.lean` are fully universe-polymorphic
(`𝒲ᵢ : Type tᵢ`, independent hom universes). The `Trans` section forces
`𝒲₁ 𝒲₂ 𝒲₃ : Type t` (one object universe) and `Category.{w}` (hom universe equal to `C`'s)
— confirmed in the elaborated signature of `actStab_trans` (`𝒲₁ 𝒲₂ 𝒲₃ : Type u_4`,
all `Category.{u_1}`). Harmless for the geometric target, but a gratuitous restriction the
generic modules were careful to avoid, and a caller with kernels in different universes hits
it. **Smallest change:** give the three `𝒲ᵢ` and their hom universes independent variables.

### P3 — two more generic modules still misfiled under `StabilityCondition/Foundation/`

**Files:** `Foundation/QuasiAbelian.lean` (strict morphisms; imports only Mathlib) and
`Foundation/ExtensionClosure.lean` (extension closure of an `ObjectProperty`; imports only
`PostnikovTower` + Mathlib). Both are generic triangulated/category vocabulary, both already
live in namespace `CategoryTheory.Triangulated` (not `…StabilityCondition`), i.e. the same
profile as `PostnikovTower`/`GrothendieckPresentation`, which #454 moved out. Latent only —
no generic module imports them today, so the layering gate stays green — but the next
generic consumer recreates issue #453. **Smallest change:** file the relocation issue now,
scoped to these two files.

## The handoff's seven claims, verified

1. **`transformK₀_dual_comp` provenance** — CONFIRMED as documented. Proof term is
   `rw [← mapF_eq_transformK₀, ← mapF_inverse_eq_transformK₀]; exact K₀.map_comp_map_eq_id
   A.equiv.functor A.equiv.inverse A.equiv.unitIso.symm`. No `ConvolutionData`, no identity
   kernel anywhere in the term; the mirror `transformK₀_comp_dual` correctly uses `counitIso`.
2. **`actStab_trans` only-associativity claim** — the *mathematical* claim ("no group of
   kernel autoequivalences") holds: `trans` needs supplied `ConvolutionData` per pair, so
   nothing near a group of kernel-tracked objects exists. But the *docstring* claim fails as
   written — see P2 above: `AutPairQuot v` with a full `MulAction` exists in
   `Stability/ClassMap.lean` for the same transports. One caveat worth recording: in
   `actStab_trans`, `D` and `corr₃` enter only through the *packaging* of the composite;
   the equation itself is `actStabAut_trans` and never touches `conv P Q`. The kernel
   computes the composite's class map only via `mapF_eq_transformK₀` instantiated at
   `A₁.trans A₂ corr₃ D` (which needs the corr₃ constituent instances a caller must supply).
   The docstring is honest about this ("the transport does not know it came from a kernel").
3. **`@[reducible] KernelAutoequivalence.trans`** — the stated reason is real:
   `Functor.IsTriangulated` is a class whose type mentions `F.mapTriangle`, which takes
   `[F.CommShift ℤ]`, so a hand-rolled instance is indexed by a different `CommShift` term
   (verified in `Mathlib/CategoryTheory/Triangulated/Functor.lean:183`). No blowup observed:
   the six `Equivalence.trans` instances elaborate with only their needed instance args
   (checked: `transFunctorAdditive` demands exactly `[Φ.functor.Additive] [Ψ.functor.Additive]`),
   and the single in-repo use site compiles in the normal build.
4. **`Slicing.mapEquiv_trans` is `ext` on `rfl`** — confirmed; the defeq it needs is
   Mathlib's literal `inverse := f.inverse ⋙ e.inverse` in `Equivalence.trans`. It IS
   fragile under a Mathlib redefinition and no note says so — P3 above.
5. **`LinearYoneda.lean` framing** — verified sound, one pedantic wording caveat. The real
   argument is right: the `AddCommGrpCat`-valued LES from `preadditiveYoneda` forgets the
   `k`-action, so no functorial `dim_k` count can be extracted, while `ModuleCat k` keeps it.
   Literal nit: "`finrank` is not statable in `AddCommGrpCat`" — `Module.finrank ℤ A` *is*
   statable for any abelian group; what is not statable is `finrank k`. The sentence's own
   continuation ("there is no `k` there") already says the right thing; tighten to
   "`finrank k` is not statable" if touched. The three named Mathlib gaps (`Linear R Cᵒᵖ`,
   `opEquiv_symm_smul`/`opEquiv'_symm_smul`, then the instance) are accurately mirrored in
   `EulerTransfer.lean`'s docstring and #469's framing.
6. **`AlternatingSum.lean` boundary hypotheses** — the ℕ-indexing rationale survives contact
   with a ℤ-indexed LES. A LES supported in `[a,b]`: reindex `Vᵢ := V(a+i)` with zero tails;
   `hzero` holds at the bottom because the preceding group is zero; `hex : ∀ i` holds in the
   tail because kernel and range are both `⊥` in trivial spaces (and at the junction `i = n`
   it is genuine exactness at `V(n+1)`, which a truncation of an exact complex has); `hstop`
   via `diffRank_eq_zero_of_subsingleton`. One reindex, at the boundary, as claimed. The
   `omit [FiniteDimensional]` on `diffRank_eq_zero_of_subsingleton` is correct.
7. **Backsliding grep** — clean. "Hodge" appears only inside explicit disclaimers
   (Realization.lean:75,247) plus one unrelated Hodge-number comment in
   `Examples/Fourfold/CalabiYau.lean`. "Adjunction" appears only in not-adjunction
   statements (EulerTransfer.lean:14-21, Realization.lean:70,157, plus Basic.lean's
   does-not-assume list). No declaration name contains an isometry claim; the only blemish
   is the internal `section Isometry` label (P3 above).

## Trust-boundary sweep — all eleven supplied data

| Declaration | Verdict at the pin |
|---|---|
| `FourierMukai.Correspondence` (Basic.lean:68) | Genuine data — three bare functors, nothing derivable. |
| `FourierMukai.ConvolutionData` (Convolution.lean:76) | Genuine data — the docstring's uniformity argument for why degenerate constructions fail checks out. |
| `K3.IntegralMukaiData` (MukaiVector.lean:106) | `c₁`, `b`, `b_spec` genuine; **`b_comm` unused and image-part provable — P2 above**. |
| `NumericalRealization` (Realization.lean:103) | Genuine data (bare `cl`); nothing at the pin builds `K₀(D^b Coh) → N`. |
| `Descends` (Realization.lean:121) | Genuine hypothesis (Prop). |
| `PreservesEuler` (Realization.lean:160) | Genuine hypothesis; confirmed via `#check` that it does NOT drag in the `NumericalRingWithDual` section instances (`chi₂` needs none, as EulerPairing.lean:67 says). |
| `CategoricalEulerForm` (EulerTransfer.lean:92) | Genuine data until #469's three Mathlib gaps land; both docstrings consistent. |
| `IsRiemannRoch` (EulerTransfer.lean:118) | Genuine hypothesis — bilinear HRR, one-variable version already a Layer-A axiom. |
| `PreservesCategoricalEuler` (EulerTransfer.lean:129) | Genuine hypothesis; full-faithfulness + k-linearity story stated, not smuggled. |
| `KernelAutoequivalence` (Symmetry FM:74) | Genuine — `iso` must be data (it is consumed to *build* `trans.iso` and via `A.iso.app E`); a `Nonempty`/`IsKernelFunctor` weakening would break `trans`. `equiv` not derivable from `corr`+`kernel`. |
| `DualKernel` (Symmetry FM:135) | Genuine — nothing recovers a kernel for the quasi-inverse from `iso`; that is the classical dual-kernel theorem, correctly outside. |

## Not findings (checked and clean)

- Axiom closure, gates, ceilings, layering — all reproduce the handoff baseline exactly.
- `hlam_trans` composite order (`lam₁.comp lam₂`, `lam₂` first) matches
  `(Φ.trans Ψ).inverse = Ψ.inverse ⋙ Φ.inverse` — correct.
- `Slicing.mapEquiv_trans`'s 12 instance arguments are all genuinely required to *state* it
  (`Slicing.mapEquiv` itself demands the full six-instance package per equivalence — checked
  by `#check`); the `Charge` section's `omit`s prune correctly.
- Round-1 fixes present: `mukaiSInt` is a `def` with `mukaiSInt_spec`; spherical-object
  disclaimer includes `Ext¹ = 0` (MukaiVector.lean:48-53, 175-180); k-linearity caveat in
  EulerTransfer's full-faithfulness discussion; `b_spec` image-restriction stated.
- The module docstring line "the action on the central charge is determined by the kernel"
  (Symmetry FM:20-21) is defensible: `K₀(Φ⁻¹)` is the unique two-sided inverse of
  `transformK₀ K`, hence determined (though not computed) by it; the file's own `actStab` /
  `actStabOfDual` docstrings draw the computed-vs-determined line correctly.

---

## Addendum — remediation and one review escape (added with PR #486)

All findings above were remediated in **PR #486** (`fix/fm-review-round2`),
which also carries this record. Per finding: P1 field deleted →
`PostnikovTower.isZero_of_length_zero` (and `HNFiltration.prefix` lost the
`hk₀` argument that existed only to discharge the deleted field — the
unused-arguments linter caught this); P2 `b_comm` deleted →
`b_comm_on_realized`; P2 docstrings now point at `GroupAction.AutPairQuot`;
all five P3 items applied. Follow-ups filed: #487 (`K₀.mapF` retirement),
#488 (`QuasiAbelian`/`ExtensionClosure` relocation). StabilityCondition
ratchet ceiling lowered 383 → 381.

**One escape, found while writing the post-review handoff:**
`Realization.lean`'s module docstring claimed "`D^b(Coh X)` does not exist
here", citing `Families.SchemeDerivedCategory` (all module sheaves). But
`Families/BoundedGeometry.lean` — `SchemeBoundedCoherentDerivedCategory X`
with `Perf(X)` inside it, from #460 — already existed at the review pin
`aaa3cfe`. The bullet was stale at merge time and this review did not catch
it: the claim-7 greps hunted "Hodge" and "adjunction", not existence claims
about other tracks' substrate. Fixed in #486. Lesson for round 3: docstring
claims of the form "X does not exist in this repository" need a grep per
claim, exactly like the backsliding greps.
