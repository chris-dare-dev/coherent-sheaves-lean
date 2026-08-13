/-
Axiom + sorry audit over a HAND-MAINTAINED LIST of this project's declarations.

Run: `lake env lean scripts/BridgelandAudit.lean` (to read the output), or
`lake build BridgelandAudit` (to check it still elaborates).

Part of the library build since 2026-08-04: a `lean_lib` with
`srcDir = "scripts"`. Removed from `defaultTargets` on 2026-08-06 -- this file
does `import BridgelandStabLean`, so it sits downstream of every module and was
making every edit anywhere re-elaborate all 497 records before `lake build`
returned. It is still a `lean_lib` and CI's axiom-gate step still runs it, so
nothing it guarded is lost; you just have to name it. Its output backs the
`fidelity` block of `formalization.yaml`; re-run it before editing that block,
and paste what it actually prints.

Being in the build is not the same as being a gate. `#print axioms` prints
`[sorryAx]` and exits 0, so a sorry-backed declaration builds green here. What
the build catches is this file falling behind the source tree in one direction
only -- see below.

Reading the output: a declaration is clean iff its axiom list is a subset of
[propext, Classical.choice, Quot.sound]. Any other name -- above all
`sorryAx` -- is a failure, not a note.

## What this file covers, and what it does not

CORRECTED 2026-08-06. The first line of this comment used to read "over every
declaration this project introduces". It is not, and cannot be.

RE-MEASURED 2026-08-08 after the #88 HN-polygon port on main at b0b90ed. The
figures below are no longer a source-text estimate and are no longer maintained
by arithmetic. They come from a sweep of the built environment, so they count
what Lean actually has rather than what a regex can find at column 0:

```bash
lake build && lake env lean scripts/Census.lean
```

**REVISED AGAIN 2026-08-07 (later), and the correction is the useful part.**
The revision below reported a real gap of **59**. The true figure was **29**.
The other 30 were compiler-generated names the sweep did not recognise --
`<Struct>.ctorIdx`, `<Struct>.mk.inj`, `<def>.congr_simp`, and `ext'_iff` from
`@[ext] theorem ext'`. Each family was then grepped for in
`BridgelandStabLean/` and occurs there **zero** times, so none is a declaration
anyone wrote or could list. `scripts/Census.lean` now filters all four.

The lesson is not that a number moved. It is that **a filter is itself a claim
about what Lean emits, and it needs the same check as any other claim here.**
The projection bullet below was written immediately after this exact mistake
was caught once. Catching it a second time, in the same file, on generated
names of a different shape, means the check has to be *grep the source for the
family* -- not *remember which families exist*.

Earlier revisions said **497 / 569 / 72 / 42 / 29 / 167** (2026-08-06), then
**670 / 814 / 144 / 44 / 59 / 189** (2026-08-07). PR #97 moved the first two of
those to **677 / 821** and nothing else; PR #104 corrected the theorem figure
to **488**. Both were right against the filter of the day, and both are
superseded here -- the 821 in particular counted the 30 generated names
described above. **Re-run the command; do not adjust the numbers.**

**THE GAP IS NOW ZERO, re-measured after adding the issue #83 abstract
families interfaces on 2026-08-11.** Every
public declaration in this library that is not a structure field projection is
named below. Be precise about what that does and does not mean -- three of the
four qualifications in this comment are unaffected by it:

* it does NOT cover the **114 private** declarations, which remain structurally
  unlistable;
* it does NOT make this file a gate -- `#print axioms` still exits 0 on
  `[sorryAx]`, and nothing here fails on a missing name;
* it does NOT stay true on its own. The next declaration added anywhere lands
  green without an entry here. Zero is a measurement taken at a commit, not a
  property the build maintains.

* It names **1353** declarations. The environment holds **1621** authored
  declarations under `BridgelandStabLean.*`, so **268 are outside this gate**,
  all of them private or projections. ("Authored" excludes constructors,
  recursors, `casesOn`, matchers, equation lemmas, internal names, and the four
  generated families named above -- none of which anybody writes or could
  list.)
* **114 are `private`** -- 100 of them theorems -- and are *structurally*
  unlistable: Lean mangles a private name to `_private.<Module>.<n>.<Name>`,
  which cannot be written as a short name from an importing module. The
  instruction below cannot be followed for them, and no amount of diligence
  changes that.
* **154 are structure field projections** emitted by the `structure` command.
  These are not a coverage gap in any useful sense; listing them would be noise.
  They are called out because a census that does not separate them reports a
  shortfall five times the real one.
* That leaves **0**. The shortfall was closed in two steps on 2026-08-07:
  **20** in `GLTildeSurj.lean` -- the largest single block, quoted in this
  comment since 2026-08-06 without moving -- then the last **10**, spread over
  `AutPairAction.lean` (5), `GLTildeFibre.lean` (3), `PolarDecomposition.lean`
  (1) and `NumericalK.lean` (1).
* **The residue was dominated by one syntactic shape.** Five of the first 20
  and **seven of the last 10** are `@[simp] theorem` on ONE line, which a regex
  anchored on `^theorem` cannot see. That is 12 of the 30, and it is why the
  count is taken from the environment rather than from source text: the names
  hardest to notice by eye were, systematically, the ones left out.
* Nothing detects the shortfall *automatically*. `scripts/check_audit.py` reads
  THIS file, but only to count its `#print axioms` lines against the output's
  record count (its truncation check, added 2026-08-08) -- it never reads the
  source tree, so it cannot see a name that should be listed and is not. This
  file fails to build only when a name it ALREADY lists disappears -- never
  when a name it *should* list appears. `scripts/Census.lean` is the thing that
  reports it, but it is a script you run, not a CI gate; a name added without a
  matching entry here still lands green.
* **410 of the 1353 are not theorems** (40 `structure`, 370 other
  constructions).
  For a `def`, `#print axioms` reports the axiom closure of a CONSTRUCTION and
  asserts nothing about any proposition. In particular
  `CategoryTheory.Triangulated.StabilityMassTriangleInequality` appears below
  formatted identically to the **943** real theorems, but it is a `def ... :
  Prop` -- its clean line means the definition is axiom-clean, NOT that the
  proposition holds.

The environment-wide emitter (`exe/Emit.lean`) sweeps `Environment.constants`
and therefore does see the private and unlisted names. That, not this file, is
the gate that closes the hole.

**On Windows the emitter cannot be linked at all** -- `supportInterpreter`
pushes the PE export table past 65535 symbols, as `exe/Emit.lean` records -- so
on that platform this file is the only axiom check available. That is *not* a
reason to believe the environment is unswept there: `scripts/Census.lean` reads
the same module data through `lake env lean`, which links nothing, and so runs
where the executable cannot. Use it to size the gap; use the emitter, in CI, to
gate it.

Adding a declaration to the library means adding it here. This file is not
derived from the source tree, so it can silently fall behind; `#print axioms`
on a name that no longer exists is a hard error, but a name never added is
invisible.
-/
import BridgelandStabLean

open BridgelandStabLean

/-! ## Cohomology exactness (#146) -/

#print axioms BridgelandStabLean.Tilting.originalHeartCoh_exact_of_distTriang
#print axioms BridgelandStabLean.Tilting.originalHeartCoh_isZero_of_isZero
#print axioms BridgelandStabLean.Tilting.heart_map_originalHeartCoh

/-! ## TStructure — bounded t-structures and t-exact functors (#146) -/

#print axioms BridgelandStabLean.TStructure.IsBounded
#print axioms BridgelandStabLean.TStructure.isBounded_iff
#print axioms BridgelandStabLean.TStructure.exists_isLE
#print axioms BridgelandStabLean.TStructure.exists_isGE
#print axioms BridgelandStabLean.TStructure.IsNondegenerate
#print axioms BridgelandStabLean.TStructure.isNondegenerate_of_isBounded
#print axioms BridgelandStabLean.Functor.IsRightTExact
#print axioms BridgelandStabLean.Functor.IsLeftTExact
#print axioms BridgelandStabLean.Functor.IsTExact
#print axioms BridgelandStabLean.Functor.isLE_map_of_isRightTExact
#print axioms BridgelandStabLean.Functor.isGE_map_of_isLeftTExact
#print axioms BridgelandStabLean.Functor.isTExact_of
#print axioms BridgelandStabLean.Functor.isRightTExact_of_isLE_zero
#print axioms BridgelandStabLean.Functor.isLeftTExact_of_isGE_zero
#print axioms BridgelandStabLean.Functor.isLeftTExact_rightAdjoint
#print axioms BridgelandStabLean.Functor.isRightTExact_leftAdjoint
#print axioms BridgelandStabLean.Functor.heart_map_of_isTExact
#print axioms BridgelandStabLean.Functor.isRightTExact_comp
#print axioms BridgelandStabLean.Functor.isLeftTExact_comp
#print axioms BridgelandStabLean.Functor.isTExact_comp
#print axioms BridgelandStabLean.Functor.isRightTExact_id
#print axioms BridgelandStabLean.Functor.isLeftTExact_id
#print axioms BridgelandStabLean.Functor.isTExact_id

/-! ## Anchor — bridges to the foundational library (#146) -/

#print axioms BridgelandStabLean.Anchor.isBounded_iff_anchor
#print axioms BridgelandStabLean.Anchor.isBounded_of_anchor
#print axioms BridgelandStabLean.Anchor.anchor_isBounded
#print axioms BridgelandStabLean.Anchor.isNondegenerate_of_anchor_isBounded

/-! ## ForMathlib — results Mathlib lacks at the pin -/

#print axioms Matrix.polarFactor

-- Vendored from the anchor so that `Weak/Tilting/Cohomology/{Basic,Homological}.lean`
-- need not import `BridgelandStability`. Deletion conditions are in the file headers.
#print axioms BridgelandStabLean.ForMathlib.CategoryTheory.ObjectProperty.FullSubcategory.isZero_of_obj_isZero
#print axioms BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.heart_hι
#print axioms BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.heart_admissible
#print axioms BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.heartAbelian
#print axioms BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.heart_biprod
#print axioms BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian
#print axioms BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.heartFullSubcategory_shortExact_of_distTriang
#print axioms BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.truncGE_map_comp_descTruncGE
#print axioms BridgelandStabLean.ForMathlib.CategoryTheory.Triangulated.TStructure.exists_truncLT_octahedral_split
#print axioms Matrix.polarFactor_posSemidef
#print axioms Matrix.polarFactor_mul_self
#print axioms Matrix.polarFactor_isHermitian
#print axioms Matrix.det_polarFactor_ne_zero
#print axioms Matrix.isUnit_det_polarFactor
#print axioms Matrix.polarFactor_posDef
#print axioms Matrix.polarUnitary
#print axioms Matrix.polarUnitary_mul_polarFactor
#print axioms Matrix.polarUnitary_mem_unitaryGroup
#print axioms Matrix.exists_polarDecomposition
#print axioms Matrix.eq_polarFactor_of_mul
#print axioms Matrix.eq_polarUnitary_of_mul
#print axioms Matrix.existsUnique_polarDecomposition

/-! ## Lattice lane -/

#print axioms Lattice.NumLattice
#print axioms Lattice.eq_zero_of_zsmul_eq_zero
#print axioms Lattice.eq_zero_of_two_zsmul_eq_zero
#print axioms Lattice.zsmul_injective
#print axioms Lattice.zsmul_left_cancel
#print axioms Lattice.finrank_numLattice
#print axioms Lattice.ne_zero_of_apply_ne_zero
#print axioms Lattice.eq_zero_of_two_zsmul_eq_zero_num

/-! ## Mukai lane — the extension `ℤ ⊕ N ⊕ ℤ` of a symmetric bilinear lattice

Pure lattice arithmetic. Nothing here is a statement about a K3 surface, a
Mukai lattice of a variety, or any geometric object; see the module docstrings
in `BridgelandStabLean/Lattice/Mukai/`. -/

#print axioms Mukai.MukaiLattice
#print axioms Mukai.pairing
#print axioms Mukai.pairing_mk
#print axioms Mukai.pairing_add_left
#print axioms Mukai.pairing_add_right
#print axioms Mukai.pairing_smul_left
#print axioms Mukai.pairing_smul_right
#print axioms Mukai.pairing_neg_left
#print axioms Mukai.pairing_neg_right
#print axioms Mukai.pairing_sub_left
#print axioms Mukai.pairing_sub_right
#print axioms Mukai.pairing_zero_left
#print axioms Mukai.pairing_zero_right
#print axioms Mukai.pairing_comm
#print axioms Mukai.selfPairing
#print axioms Mukai.selfPairing_eq_pairing
#print axioms Mukai.selfPairing_mk
#print axioms Mukai.selfPairing_smul
#print axioms Mukai.selfPairing_zero
#print axioms Mukai.selfPairing_neg
#print axioms Mukai.even_selfPairing
#print axioms Mukai.IsSpherical
#print axioms Mukai.IsIsotropic
#print axioms Mukai.isSpherical_iff
#print axioms Mukai.isIsotropic_iff
#print axioms Mukai.IsSpherical.neg
#print axioms Mukai.IsIsotropic.neg
#print axioms Mukai.not_isSpherical_and_isIsotropic
#print axioms Mukai.expectedDim
#print axioms Mukai.expectedDim_eq_zero_iff
#print axioms Mukai.expectedDim_eq_two_iff
#print axioms Mukai.rankUnit
#print axioms Mukai.corankUnit
#print axioms Mukai.pairing_outer
#print axioms Mukai.isIsotropic_rankUnit
#print axioms Mukai.isIsotropic_corankUnit
#print axioms Mukai.pairing_rankUnit_corankUnit
#print axioms Mukai.pairingBilin
#print axioms Mukai.pairingBilin_apply

/-! ## Mukai lane — rank-two subpairs -/

#print axioms Mukai.gram
#print axioms Mukai.gram_comm
#print axioms Mukai.gram_zero_left
#print axioms Mukai.gram_zero_right
#print axioms Mukai.pairing_lincomb
#print axioms Mukai.selfPairing_lincomb
#print axioms Mukai.gram_lincomb
#print axioms Mukai.IsHyperbolicPair
#print axioms Mukai.isHyperbolicPair_iff
#print axioms Mukai.discr_pos_of_isHyperbolicPair
#print axioms Mukai.gram_ne_zero_of_isHyperbolicPair
#print axioms Mukai.ne_zero_left_of_isHyperbolicPair
#print axioms Mukai.ne_zero_right_of_isHyperbolicPair
#print axioms Mukai.isHyperbolicPair_comm
#print axioms Mukai.isHyperbolicPair_lincomb
#print axioms Mukai.orthWitness
#print axioms Mukai.pairing_orthWitness
#print axioms Mukai.selfPairing_orthWitness
#print axioms Mukai.selfPairing_orthWitness_neg
#print axioms Mukai.orthWitness_ne_zero
#print axioms Mukai.pairSpan
#print axioms Mukai.mem_pairSpan_left
#print axioms Mukai.mem_pairSpan_right
#print axioms Mukai.orthWitness_mem_pairSpan
#print axioms Mukai.HasSphericalClass
#print axioms Mukai.HasIsotropicClass
#print axioms Mukai.exists_neg_selfPairing_of_isHyperbolicPair

/-! ## Tilting lane — torsion pairs in an abelian category

Mathlib has no torsion pair for abelian categories at the pin, so this is built
from scratch. Pure abelian-category theory: no foundational library import, no geometry. The
Happel-Reiten-Smalo tilt itself is NOT here; see the module docstring. -/

#print axioms Tilting.TorsionPair
#print axioms Tilting.TorsionPair.isZero_of_tors_of_free
#print axioms Tilting.TorsionPair.tors_iff
#print axioms Tilting.TorsionPair.free_iff
#print axioms Tilting.TorsionPair.free_of_mono
#print axioms Tilting.TorsionPair.tors_of_epi
#print axioms Tilting.TorsionPair.tors_of_shortExact
#print axioms Tilting.TorsionPair.free_of_shortExact
#print axioms Tilting.TorsionPair.exists_factor_of_tors
#print axioms Tilting.TorsionPair.allTors
#print axioms Tilting.TorsionPair.allFree

/-! ## Tilting lane — torsion pairs on a heart, and the tilted aisles

The aisles are defined by HOM-ORTHOGONALITY, not with a cohomology functor.
Mathlib has no bundled `H^n` functor into the heart at the pin. This project
now constructs one and proves it homological, but that later result does not
change the original aisle definition. `zero'` is proved here;
`exists_triangle_zero_one` is NOT, and is not declared with `sorry`. -/

#print axioms Tilting.HeartTorsionPair
#print axioms Tilting.HeartTorsionPair.tiltLE
#print axioms Tilting.HeartTorsionPair.tiltGE
#print axioms Tilting.HeartTorsionPair.tiltLE_isClosedUnderIsomorphisms
#print axioms Tilting.HeartTorsionPair.tiltGE_isClosedUnderIsomorphisms
#print axioms Tilting.HeartTorsionPair.exists_factor_truncGE
#print axioms Tilting.HeartTorsionPair.factor_truncGE_unique
#print axioms Tilting.HeartTorsionPair.tors_of_orthogonal
#print axioms Tilting.HeartTorsionPair.hom_eq_zero_of_tiltLE_of_tiltGE

/-! ## Tilting lane — the indexed aisle families

The shift and inclusion fields of the tilted t-structure. Note
`tiltAt_zero'` ends in an apostrophe: `scripts/check_audit.py` has a regression
test for exactly that parse hazard. -/

#print axioms Tilting.HeartTorsionPair.torsOrth
#print axioms Tilting.HeartTorsionPair.freeOrth
#print axioms Tilting.HeartTorsionPair.torsOrth_isClosedUnderIsomorphisms
#print axioms Tilting.HeartTorsionPair.freeOrth_isClosedUnderIsomorphisms
#print axioms Tilting.HeartTorsionPair.tiltLEAt
#print axioms Tilting.HeartTorsionPair.tiltGEAt
#print axioms Tilting.HeartTorsionPair.tiltLEAt_zero_iff
#print axioms Tilting.HeartTorsionPair.tiltGEAt_one_iff
#print axioms Tilting.HeartTorsionPair.tiltLEAt_shift
#print axioms Tilting.HeartTorsionPair.tiltGEAt_shift
#print axioms Tilting.HeartTorsionPair.tiltLEAt_zero_le
#print axioms Tilting.HeartTorsionPair.tiltGEAt_one_le
#print axioms Tilting.HeartTorsionPair.tiltAt_zero'

/-! ## Tilting lane — recognising the two aisles from a triangle

The two halves of `exists_triangle_zero_one`. Neither needs a cohomology
functor; the module docstring records why the textbook construction appeared to
and this one does not. -/

#print axioms Tilting.HeartTorsionPair.tiltLE_of_triangle
#print axioms Tilting.HeartTorsionPair.tiltGE_of_triangle
#print axioms Tilting.HeartTorsionPair.tiltLEAt_zero_of_triangle
#print axioms Tilting.HeartTorsionPair.tiltGEAt_one_of_triangle

/-! ## Tilting lane — the Happel-Reiten-Smalo tilt

`tilt` is a genuine Triangulated.TStructure: every field is proved, none is
sorry-backed, and no cohomology functor appears in the construction. Note
`tilt` is a `def`, so its clean axiom line reports the axiom closure of a
CONSTRUCTION -- the theorems it is built from are the six field lemmas above
and below. -/

#print axioms Tilting.HeartTorsionPair.tiltLEAt_isClosedUnderIsomorphisms
#print axioms Tilting.HeartTorsionPair.tiltGEAt_isClosedUnderIsomorphisms
#print axioms Tilting.HeartTorsionPair.exists_tilt_triangle_of_data
#print axioms Tilting.HeartTorsionPair.exists_tilt_triangle
#print axioms Tilting.HeartTorsionPair.tilt
#print axioms Tilting.HeartTorsionPair.tilt_le
#print axioms Tilting.HeartTorsionPair.tilt_ge
#print axioms Tilting.HeartTorsionPair.tilt_le_zero_iff

/-! ## Tilting lane — textbook agreement for the tilted aisles

The dual factorisation pair and `free_of_orthogonal` complete the counit
substitutes on both sides, and the four agreement theorems tie the
Hom-orthogonal aisles to the textbook `H⁰` formulation, with `τ^{≥0}` and
`τ^{≤0}` in the role of `H⁰`. Closes the review finding F1 of #86 (#94). -/

#print axioms Tilting.HeartTorsionPair.exists_factor_truncLE
#print axioms Tilting.HeartTorsionPair.factor_truncLE_unique
#print axioms Tilting.HeartTorsionPair.free_of_orthogonal
#print axioms Tilting.HeartTorsionPair.torsOrth_iff_tors_truncGE
#print axioms Tilting.HeartTorsionPair.freeOrth_iff_free_truncLE
#print axioms Tilting.HeartTorsionPair.tiltLE_iff_tors_truncGE
#print axioms Tilting.HeartTorsionPair.tiltGE_iff_free_truncLE

/-! ## Tilting lane — the tilted heart identified

`tilt_heart_iff` is the textbook `A† = ⟨F⟦1⟧, T⟩` in the single-step form
exact for a torsion pair: membership in the tilted heart is exactly being an
extension of a torsion object by a shifted torsion-free one. Closes #106
under the #81 weak-stability epic; abstract, bound to no source coordinate. -/

#print axioms Tilting.HeartTorsionPair.tilt_heart_of_triangle
#print axioms Tilting.HeartTorsionPair.exists_triangle_of_tilt_heart
#print axioms Tilting.HeartTorsionPair.tilt_heart_iff

/-! ## Tilting lane — original and tilted heart cohomology bridge

The t-structure-only cohomology functor applies to both hearts.  A tilted-heart
object has the canonical torsion-free `H⁻¹` and torsion `H⁰` factors, whose
truncation triangle is a short exact sequence in the tilted heart; its maps
are exposed as a kernel and a cokernel.  The arbitrary-short-exact six-term
cohomology sequence remains deliberately undeclared. -/

#print axioms Tilting.originalHeartCohFunctor
#print axioms Tilting.originalHeartCohFunctor_additive
#print axioms Tilting.originalHeartCoh
#print axioms Tilting.originalHeartCohIsoOfHeart
#print axioms Tilting.HeartTorsionPair.tiltedHeartCohFunctor
#print axioms Tilting.HeartTorsionPair.tors_zero
#print axioms Tilting.HeartTorsionPair.free_zero
#print axioms Tilting.HeartTorsionPair.isLE_zero_of_tilt_heart
#print axioms Tilting.HeartTorsionPair.isGE_neg_one_of_tilt_heart
#print axioms Tilting.HeartTorsionPair.tors_truncGE_zero_of_tilt_heart
#print axioms Tilting.HeartTorsionPair.free_truncLT_zero_shift_of_tilt_heart
#print axioms Tilting.HeartTorsionPair.originalHMinusOne
#print axioms Tilting.HeartTorsionPair.originalHZero
#print axioms Tilting.HeartTorsionPair.originalHMinusOne_free
#print axioms Tilting.HeartTorsionPair.originalHZero_tors
#print axioms Tilting.HeartTorsionPair.originalHeartCohIsoHMinusOne
#print axioms Tilting.HeartTorsionPair.originalHeartCohIsoHZero
#print axioms Tilting.originalCohomologyShiftIso
#print axioms Tilting.originalCohomologyTriangle
#print axioms Tilting.originalCohomologyTriangle_distinguished
#print axioms Tilting.HeartTorsionPair.free_shift_mem_tilt_heart
#print axioms Tilting.HeartTorsionPair.tors_mem_tilt_heart
#print axioms Tilting.HeartTorsionPair.originalHMinusOneShiftInTiltHeart
#print axioms Tilting.HeartTorsionPair.objectInTiltHeart
#print axioms Tilting.HeartTorsionPair.originalHZeroInTiltHeart
#print axioms Tilting.HeartTorsionPair.originalCohomologyShortComplex
#print axioms Tilting.HeartTorsionPair.originalCohomologyShortComplex_shortExact
#print axioms Tilting.HeartTorsionPair.originalCohomologyShortComplex_f_isKernel
#print axioms Tilting.HeartTorsionPair.originalCohomologyShortComplex_g_isCokernel

/-! ## TStructure lane — truncation functors commute with the shift -/

#print axioms BridgelandStabLean.TStructure.shiftedTriangleLTGE
#print axioms BridgelandStabLean.TStructure.shiftedTriangleLTGE_distinguished
#print axioms BridgelandStabLean.TStructure.isLE_shiftedTriangleLTGE_obj₁
#print axioms BridgelandStabLean.TStructure.isGE_shiftedTriangleLTGE_obj₃
#print axioms BridgelandStabLean.TStructure.exists_shiftedTriangleLTGE_iso
#print axioms BridgelandStabLean.TStructure.shiftedTriangleLTGEIso
#print axioms BridgelandStabLean.TStructure.shiftedTriangleLTGEIso_hom₂
#print axioms BridgelandStabLean.TStructure.truncLTShiftIso
#print axioms BridgelandStabLean.TStructure.truncGEShiftIso
#print axioms BridgelandStabLean.TStructure.truncLTShiftIso_hom_comp_truncLTι
#print axioms BridgelandStabLean.TStructure.truncLTShiftIso_hom_comp_truncLTι_assoc
#print axioms BridgelandStabLean.TStructure.truncGEπ_comp_truncGEShiftIso_hom
#print axioms BridgelandStabLean.TStructure.truncGEπ_comp_truncGEShiftIso_hom_assoc
#print axioms BridgelandStabLean.TStructure.truncGEπ_comp_truncGEShiftIso_inv
#print axioms BridgelandStabLean.TStructure.truncGEπ_comp_truncGEShiftIso_inv_assoc
#print axioms BridgelandStabLean.TStructure.truncLTShiftNatIso
#print axioms BridgelandStabLean.TStructure.truncGEShiftNatIso
#print axioms BridgelandStabLean.TStructure.truncLEShiftNatIso
#print axioms BridgelandStabLean.TStructure.truncGELEShiftNatIso
#print axioms Tilting.originalHeartCohUnderlyingShiftNatIso
#print axioms Tilting.originalHeartCohShiftNatIso

/-! ## Tilting lane — six-term original-heart cohomology sequence

Degree-zero cohomology of an arbitrary t-structure is proved homological.
The six-term sequence is then constructed for any triangle and specialized
to a short exact sequence in the tilted heart, with canonical identifications
of all six terms and unconditional exactness plus endpoint mono/epi. -/

#print axioms Tilting.OriginalHeartCohomologyIsHomological
#print axioms Tilting.originalHeartCohFunctor_isHomological
#print axioms Tilting.originalHeartCohFunctor_zero_shiftSequence
#print axioms Tilting.originalHeartCohShiftIso
#print axioms Tilting.originalHeartCoh_isZero_of_isGE
#print axioms Tilting.originalHeartCoh_isZero_of_isLE
#print axioms Tilting.originalHeartCohFunctor_shift_isZero_of_isGE
#print axioms Tilting.originalHeartCohFunctor_shift_isZero_of_isLE
#print axioms Tilting.originalHeartCohomologySixTermSequence
#print axioms Tilting.originalHeartCohomologySixTermSequence_obj₀Iso
#print axioms Tilting.originalHeartCohomologySixTermSequence_obj₁Iso
#print axioms Tilting.originalHeartCohomologySixTermSequence_obj₂Iso
#print axioms Tilting.originalHeartCohomologySixTermSequence_obj₃Iso
#print axioms Tilting.originalHeartCohomologySixTermSequence_obj₄Iso
#print axioms Tilting.originalHeartCohomologySixTermSequence_obj₅Iso
#print axioms Tilting.originalHeartCohomologySixTermSequence_exact
#print axioms Tilting.originalHeartCohomologySixTermSequence_mono_first
#print axioms Tilting.originalHeartCohomologySixTermSequence_epi_last
#print axioms Tilting.HeartTorsionPair.exists_distinguished_triangle_of_shortExact
#print axioms Tilting.HeartTorsionPair.triangleOfShortExact
#print axioms Tilting.HeartTorsionPair.triangleOfShortExact_distinguished
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₀Iso
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₁Iso
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₂Iso
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₃Iso
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₄Iso
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_obj₅Iso
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_exact
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_mono_first
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_epi_last
#print axioms Tilting.HeartTorsionPair.originalCohomologySixTermSequenceOfShortExact_exact_with_endpoints
#print axioms Tilting.HeartTorsionPair.originalHMinusOne_isZero_of_tors
#print axioms Tilting.HeartTorsionPair.originalHZeroIsoOfTors
#print axioms Tilting.HeartTorsionPair.originalHZero_isZero_of_free_shift
#print axioms Tilting.HeartTorsionPair.originalHMinusOneShiftIsoOfHZeroIsZero
#print axioms Tilting.HeartTorsionPair.originalHMinusOneIsoOfFreeShift
#print axioms Tilting.HeartTorsionPair.exists_original_triangle_of_torsion_subobject_free_shift

/-! ## WeakStability lane -- the section-14 definitions

Definitions 14.1-14.3 of 1902.08184v4 on the abstract layer, plus the
ordinary-into-weak embeddings and the closure properties of the zero-charge
subcategory. The three `structure`s and the constructions among these report
axiom closures of DEFINITIONS; the embedding and closure results are the
theorems. Closes #107; no source binding is claimed (see the module
docstring and #111). -/

#print axioms WeakStability.WeakPreStabilityCondition
#print axioms WeakStability.WeakPreStabilityCondition.ofPre
#print axioms WeakStability.WeakPreStabilityCondition.ofPre_slicing
#print axioms WeakStability.WeakPreStabilityCondition.ofPre_Z
#print axioms WeakStability.WeakStabilityFunction
#print axioms WeakStability.StabilityFunction
#print axioms WeakStability.StabilityFunction.toWeak
#print axioms WeakStability.StabilityFunction.toWeak_Z
#print axioms WeakStability.WeakStabilityFunction.charge
#print axioms WeakStability.WeakStabilityFunction.charge_triangle
#print axioms WeakStability.WeakStabilityFunction.charge_triangle'
#print axioms WeakStability.WeakStabilityFunction.charge_isZero
#print axioms WeakStability.WeakStabilityFunction.slope
#print axioms WeakStability.WeakStabilityFunction.slope_of_im_pos
#print axioms WeakStability.WeakStabilityFunction.slope_of_im_nonpos
#print axioms WeakStability.WeakStabilityFunction.IsSemistable
#print axioms WeakStability.WeakStabilityFunction.IsStable
#print axioms WeakStability.WeakStabilityFunction.IsStable.isSemistable
#print axioms WeakStability.WeakStabilityFunction.zeroCharge
#print axioms WeakStability.WeakStabilityFunction.zeroCharge_def
#print axioms WeakStability.WeakStabilityFunction.zeroCharge_isClosedUnderIsomorphisms
#print axioms WeakStability.WeakStabilityFunction.charge_eq_zero_pair
#print axioms WeakStability.WeakStabilityFunction.zeroCharge_left
#print axioms WeakStability.WeakStabilityFunction.zeroCharge_right
#print axioms WeakStability.WeakStabilityFunction.zeroCharge_extension

/-! ## WeakStability lane -- noetherian torsion subcategories

Definition 14.6 in Remark 14.7's chain form (the design decision is in the
module docstring), the free = B-perp identification riding on
free_of_orthogonal, and the zero-subcategory nonvacuity witness. Lemmas
14.8 and 14.11 are deliberately UNDECLARED with their gaps named in the
module -- absent beats sorry-backed. Closes #108. -/

#print axioms WeakStability.IsHeartMono
#print axioms WeakStability.SubobjectChain
#print axioms WeakStability.SubobjectChain.Terminates
#print axioms WeakStability.NoetherianTorsionSubcategory
#print axioms WeakStability.rightOrthogonal
#print axioms WeakStability.free_iff_rightOrthogonal
#print axioms WeakStability.isIso_of_isZero
#print axioms WeakStability.zeroTorsionPair
#print axioms WeakStability.zeroNoetherianTorsion
#print axioms WeakStability.noetherian_mono

/-! ## WeakStability lane -- the torsion pair at a phase cutoff

Display (14.1) in phase language, unconditional on the slicing axioms: the
pair (P((b,1]), P((0,b])) as a HeartTorsionPair on the slicing-induced
t-structure, with the HN cut as decomposition and the slicing's own
hom-vanishing as the orthogonality. slicingTilt_heart_iff composes with
tilt_heart_iff (#106) to identify the tilted heart. The normalized
slope--phase ray identity is formalized later in this lane, but the exact
source-facing cutoff equivalence is not packaged or reviewed; the coverage
map therefore remains `mapped`, not a claim. Closes #109. -/

#print axioms WeakStability.phaseTors
#print axioms WeakStability.phaseFree
#print axioms WeakStability.leProp_of_iso
#print axioms WeakStability.gtProp_of_iso
#print axioms WeakStability.mem_heart_of_bounds
#print axioms WeakStability.slicingTorsionPair
#print axioms WeakStability.slicingTorsionPair_tors
#print axioms WeakStability.slicingTorsionPair_free
#print axioms WeakStability.slicingTilt_heart_iff

/-! ## WeakStability lane -- the tilting property

Definition 14.12 in phase language: A0 is the torsion class of a noetherian
torsion subcategory, and every heart object with phiPlus below the boundary
has a heart-triangle envelope with zero-charge quotient and shifted
Hom-vanishing. The later phase-language Lemma 14.17 infrastructure and
phase-language Proposition 14.16 infrastructure make no coverage promotion:
the map stays `mapped`, and the exact source proposition remains undeclared.
The raw Definition 14.12 envelope is now sufficient for the heart-level
assembly. -/

#print axioms WeakStability.IsNoetherianTorsionSubcategory
#print axioms WeakStability.WeakPreStabilityCondition.zeroCharge
#print axioms WeakStability.WeakPreStabilityCondition.HasFiniteMaxSlope
#print axioms WeakStability.WeakPreStabilityCondition.HasTiltingEnvelope
#print axioms WeakStability.WeakPreStabilityCondition.HasPhaseTiltingEnvelope
#print axioms WeakStability.WeakPreStabilityCondition.HasPhaseTiltingEnvelope.hasTiltingEnvelope
#print axioms WeakStability.WeakPreStabilityCondition.TiltingProperty
#print axioms WeakStability.WeakPreStabilityCondition.TiltingProperty.hasTiltingEnvelope_of_phaseFree

/-! ## WeakStability lane -- heart equivalence and weak HN infrastructure

The two stacked weak-stability milestones following #110: isomorphism
transport for weak stability functions, the slicing-to-heart forward bridge,
and abelian weak Harder--Narasimhan filtrations with existence for the induced
heart function.  These declarations make no new source-coverage claim. -/

#print axioms WeakStability.WeakStabilityFunction.charge_eq_of_iso
#print axioms WeakStability.WeakStabilityFunction.isSemistable_of_iso
#print axioms WeakStability.WeakStabilityFunction.slope_eq_of_iso
#print axioms WeakStability.WeakStabilityFunction.isSemistable_iff_of_iso
#print axioms WeakStability.WeakStabilityFunction.isStable_of_iso
#print axioms WeakStability.WeakStabilityFunction.isStable_iff_of_iso
#print axioms WeakStability.WeakPreStabilityCondition.weakStabilityFunctionOnHeart
#print axioms WeakStability.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_Z
#print axioms WeakStability.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_charge
#print axioms WeakStability.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_zeroCharge_iff
#print axioms WeakStability.WeakPreStabilityCondition.charge_mem_upperHalfPlane_and_arg_le_phiPlus
#print axioms WeakStability.WeakPreStabilityCondition.pi_mul_phiMinus_le_charge_arg_of_im_pos
#print axioms WeakStability.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_isSemistable_of_mem_P_phi
#print axioms WeakStability.WeakPreStabilityCondition.mem_P_phiPlus_of_weakStabilityFunctionOnHeart_isSemistable
#print axioms WeakStability.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_isSemistable_iff
#print axioms WeakStability.SlicingBridge.phiPlus_le_of_heart_subobject
#print axioms WeakStability.WeakStabilityFunction.heartSlope
#print axioms WeakStability.heartSlope_cokernel_ofLE_congr
#print axioms WeakStability.heartSlope_cokernel_mapMono_eq
#print axioms WeakStability.heartSemistable_cokernel_ofLE_congr
#print axioms WeakStability.heartSemistable_cokernel_mapMono_iff
#print axioms WeakStability.WeakAbelianHNFiltration
#print axioms WeakStability.WeakAbelianHNFiltration.factor
#print axioms WeakStability.WeakAbelianHNFiltration.factor_not_isZero
#print axioms WeakStability.WeakAbelianHNFiltration.factor_obj_not_isZero
#print axioms WeakStability.WeakStabilityFunction.HeartSemistable
#print axioms WeakStability.WeakStabilityFunction.HasHNProperty
#print axioms WeakStability.WeakStabilityFunction.append_hn_filtration_of_mono
#print axioms WeakStability.WeakStabilityFunction.exists_hn_with_last_slope_of_semistable
#print axioms WeakStability.WeakStabilityFunction.HNQuotientStep
#print axioms WeakStability.WeakStabilityFunction.HasHNQuotientInduction
#print axioms WeakStability.WeakStabilityFunction.hasHNProperty_of_quotientInduction
#print axioms WeakStability.instAbelianFullSubcategoryHeart_bridgelandStabLean_2
#print axioms WeakStability.WeakPreStabilityCondition.charge_arg_eq_pi_mul_of_mem_P_phi_lt_one
#print axioms WeakStability.WeakPreStabilityCondition.charge_im_pos_of_mem_P_phi_lt_one
#print axioms WeakStability.WeakPreStabilityCondition.slope_lt_of_mem_P_of_phase_lt
#print axioms WeakStability.WeakPreStabilityCondition.slope_eq_top_of_mem_P_one
#print axioms WeakStability.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_hasHN
#print axioms WeakStability.instAbelianFullSubcategoryHeart_bridgelandStabLean
#print axioms WeakStability.instAbelianFullSubcategoryHeart_bridgelandStabLean_1

/-! ## WeakStability lane -- phase-tilt semistable classification

The rotated weak stability function on the HRS tilt, both directions of the
phase-language counterpart of Lemma 14.17, and the positive-imaginary/stable
Hom-vanishing refinement.  These entries make no source-coverage promotion:
the slope--phase reparameterisation remains the mapped boundary. -/

#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltRotation
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltRotation_apply
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltCharge
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltCharge_apply
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltHeart_interval
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltHeart_iff_phaseShiftHeart
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltWeakStabilityFunction
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltWeakStabilityFunction_Z
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltWeakStabilityFunction_charge
#print axioms WeakStability.WeakPreStabilityCondition.zeroCharge_mem_P_one
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltWeakStabilityFunction_zeroCharge_iff
#print axioms WeakStability.WeakPreStabilityCondition.hom_eq_zero_of_zeroCharge_to_phaseTiltSemistable
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_isSemistable_left_of_zeroCharge_right
#print axioms WeakStability.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_isSemistable_of_phaseTors_phaseTiltSemistable
#print axioms WeakStability.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_isSemistable_of_phaseFree_shiftSemistable
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltWeakStabilityFunction_isSemistable_of_ray
#print axioms WeakStability.WeakPreStabilityCondition.IsPhaseTiltTypeOne
#print axioms WeakStability.WeakPreStabilityCondition.IsPhaseTiltTypeTwo
#print axioms WeakStability.WeakPreStabilityCondition.isSemistable_of_isPhaseTiltTypeOne
#print axioms WeakStability.WeakPreStabilityCondition.isSemistable_of_isPhaseTiltTypeTwo
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltClassification_of_isSemistable
#print axioms WeakStability.WeakPreStabilityCondition.isSemistable_of_phaseTiltClassification
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltWeakStabilityFunction_isSemistable_iff_classification

/-! ## WeakStability lane -- Proposition 14.16 heart-level assembly

The maximal-zero-charge-subobject construction, raw-envelope noetherian
assembly, boundary-saturated weak HN assembly over the cohomological `H⁻¹`
and `H⁰` filtrations, and support-property transport. Proposition 14.16
itself remains undeclared, but its heart-level constructive obligations are
assembled directly from Definition 14.12's `TiltingProperty`. -/

#print axioms WeakStability.WeakStabilityFunction.HasZeroChargeDecompositions
#print axioms WeakStability.WeakStabilityFunction.zeroChargeTorsionPair
#print axioms WeakStability.WeakStabilityFunction.zeroChargeTorsionPair_tors
#print axioms WeakStability.WeakStabilityFunction.zeroChargeTorsionPair_free
#print axioms WeakStability.WeakStabilityFunction.heartZeroCharge
#print axioms WeakStability.WeakStabilityFunction.heartZeroCharge_isSerreClass
#print axioms WeakStability.rightOrthogonal_of_iso
#print axioms WeakStability.cokernelCompShortComplex
#print axioms WeakStability.cokernelCompShortComplex_shortExact
#print axioms WeakStability.kernelCokernelCompMiddleShortComplex
#print axioms WeakStability.kernelCokernelCompMiddleShortComplex_shortExact
#print axioms WeakStability.kernelCompShortComplex
#print axioms WeakStability.kernelCompShortComplex_shortExact
#print axioms WeakStability.WeakStabilityFunction.isSemistable_middle_of_zeroCharge_quotient
#print axioms WeakStability.WeakStabilityFunction.isSemistable_quotient_of_zeroCharge_subobject
#print axioms WeakStability.isHeartMono_of_mono
#print axioms WeakStability.mono_of_isHeartMono
#print axioms WeakStability.WeakStabilityFunction.isNoetherianObject_of_zeroCharge
#print axioms WeakStability.WeakStabilityFunction.hasZeroChargeDecomposition_of_chainCondition
#print axioms WeakStability.WeakStabilityFunction.hasZeroChargeDecompositions_of_chainCondition
#print axioms WeakStability.WeakStabilityFunction.hasZeroChargeDecomposition_of_reduction
#print axioms WeakStability.mono_comp_of_zeroCharge_of_rightOrthogonal
#print axioms WeakStability.mono_in_originalHeart_of_mono_in_phaseTilt
#print axioms WeakStability.WeakPreStabilityCondition.zeroCharge_phaseTors
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltingEnvelope_gives_shiftedZeroChargeDecomposition
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltingEnvelope_middle_semistable
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_zeroChargeChain_terminates_of_tiltingEnvelope
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_semistableQuotient_of_saturatedExtension
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_zeroChargeChain_terminates_of_rightOrthogonal
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_hasZeroChargeDecompositions_of_freeShiftDecompositions
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_hasZeroChargeDecompositions_of_phaseEnvelopes
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_hasZeroChargeDecompositions_of_tiltingEnvelopes
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_isNoetherianObject_of_zeroCharge
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltNoetherianTorsionSubcategory
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_hasZeroChargeDecompositions_of_chainCondition
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltNoetherianTorsionSubcategoryOfDecompositions
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltNoetherianTorsionSubcategoryOfTiltingProperty
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltNoetherianTorsionSubcategoryOfPhaseEnvelopes
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltNoetherianTorsionSubcategoryOfTiltingEnvelopes
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltNoetherianTorsionSubcategoryOfChainCondition
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltCharge_im_pos_of_phaseTors
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_slope_lt_of_phase_separated
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_slope_shift_lt_shift_of_phase_separated
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_slope_unshifted_lt_shifted_of_phase_separated
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_semistableQuotient_of_extension
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_hnLastQuotient
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_existsHNWithLastSource_of_freeShift_zeroCharge_extension
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_hasHN_of_freeShift_zeroCharge_extension
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_hZeroLastQuotient
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_hasHNProperty_of_zeroChargeDecompositions
#print axioms WeakStability.WeakStabilityFunction.semistableClasses
#print axioms WeakStability.WeakStabilityFunction.HasSupportProperty
#print axioms WeakStability.WeakStabilityFunction.isSemistable_of_zeroCharge
#print axioms WeakStability.WeakStabilityFunction.class_eq_zero_of_zeroCharge
#print axioms WeakStability.phaseTiltLinearCharge
#print axioms WeakStability.phaseTiltLinearCharge_apply
#print axioms WeakStability.norm_phaseTiltLinearCharge
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_hasSupportProperty
#print axioms WeakStability.WeakStabilityFunction.QuadraticSupportData
#print axioms WeakStability.WeakStabilityFunction.QuadraticSupportData.hasSupportProperty
#print axioms WeakStability.WeakStabilityFunction.QuadraticSupportData.class_eq_zero_of_zeroCharge
#print axioms WeakStability.WeakStabilityFunction.UniformQuadraticSupportData
#print axioms WeakStability.WeakStabilityFunction.UniformQuadraticSupportData.fiber
#print axioms WeakStability.WeakStabilityFunction.UniformQuadraticSupportData.reindex
#print axioms WeakStability.WeakStabilityFunction.QuadraticSupportData.constant
#print axioms WeakStability.WeakStabilityFunction.QuotientUniformQuadraticSupportData
#print axioms WeakStability.WeakStabilityFunction.QuotientUniformQuadraticSupportData.fiber
#print axioms WeakStability.WeakStabilityFunction.QuotientUniformQuadraticSupportData.zero_class_eq_zero
#print axioms WeakStability.WeakPreStabilityCondition.PhaseTiltHeartObligations
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltHeartObligations
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltHeartObligationsOfPhaseEnvelopes
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltHeartObligationsOfTiltingProperty
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_hasHNPropertyOfTiltingProperty

/-! ## WeakStability lane -- reverse heart--slicing foundations

The extended-slope phase normalization, integer-normalized ambient phase
family, analytic charge-ray identity, heart-HN to ambient-Postnikov
conversion, and phase-tilt prestability assembly. These declarations package
no source statement and make no §14 coverage promotion. -/

#print axioms WeakStability.weakPhaseOfSlope
#print axioms WeakStability.weakPhaseOfSlope_top
#print axioms WeakStability.weakPhaseOfSlope_coe
#print axioms WeakStability.weakPhaseOfSlope_coe_mem_Ioo
#print axioms WeakStability.weakPhaseOfSlope_mem_Ioc
#print axioms WeakStability.weakPhaseOfSlope_strictMono
#print axioms WeakStability.weakPhaseOfSlope_lt_iff
#print axioms WeakStability.complex_eq_pos_mul_exp_weakPhaseOfSlope
#print axioms WeakStability.WeakStabilityFunction.charge_ray_of_mem_heart
#print axioms WeakStability.negOnePow_mul_exp_pi_eq_exp_add_int
#print axioms WeakStability.WeakStabilityFunction.ambientPhasePredicate_charge_ray
#print axioms WeakStability.WeakStabilityFunction.phase
#print axioms WeakStability.WeakStabilityFunction.phase_mem_Ioc
#print axioms WeakStability.WeakStabilityFunction.phase_lt_phase_iff
#print axioms WeakStability.WeakStabilityFunction.phase_eq_of_iso
#print axioms WeakStability.WeakStabilityFunction.heartPhasePredicate
#print axioms WeakStability.WeakStabilityFunction.heartPhasePredicate_closedUnderIso
#print axioms WeakStability.WeakStabilityFunction.heartPhasePredicate_instClosedUnderIso
#print axioms WeakStability.WeakStabilityFunction.shiftedHeartPhasePredicate
#print axioms WeakStability.WeakStabilityFunction.ambientPhasePredicate
#print axioms WeakStability.WeakStabilityFunction.shiftedHeartPhasePredicate_zero_iff
#print axioms WeakStability.WeakStabilityFunction.ambientPhasePredicate_iff_of_mem_Ioc
#print axioms WeakStability.WeakStabilityFunction.shiftedHeartPhasePredicate_closedUnderIso
#print axioms WeakStability.WeakStabilityFunction.ambientPhasePredicate_closedUnderIso
#print axioms WeakStability.WeakStabilityFunction.ambientPhasePredicate_instClosedUnderIso
#print axioms WeakStability.WeakStabilityFunction.shiftedHeartPhasePredicate_shift_iff
#print axioms WeakStability.WeakStabilityFunction.ambientPhasePredicate_shift_iff
#print axioms WeakStability.WeakStabilityFunction.ambientPhasePredicate_shift_int
#print axioms WeakStability.WeakAbelianHNFiltration.factorInclusion
#print axioms WeakStability.WeakAbelianHNFiltration.factorInclusion_mono
#print axioms WeakStability.instAbelianFullSubcategoryHeart_bridgelandStabLean_3
#print axioms WeakStability.WeakAbelianHNFiltration.factorTriangle
#print axioms WeakStability.WeakAbelianHNFiltration.factorTriangle_distinguished
#print axioms WeakStability.WeakAbelianHNFiltration.toAmbientHN
#print axioms WeakStability.HNFiltration.relabelPhasePredicate
#print axioms WeakStability.WeakAbelianHNFiltration.toAmbientNormalizedHN
#print axioms WeakStability.WeakStabilityFunction.ambientHNOfHeart
#print axioms WeakStability.WeakStabilityFunction.ambientHN_exists_of_mem_heart
#print axioms WeakStability.HNFiltration.shiftWeakAmbient
#print axioms WeakStability.HNFiltration.shiftWeakAmbient_phase
#print axioms WeakStability.WeakStabilityFunction.ambientHN_exists_of_mem_heart_with_phase_bounds
#print axioms WeakStability.WeakStabilityFunction.ambientHN_exists_of_pure
#print axioms WeakStability.WeakStabilityFunction.ambientHN_exists_of_width
#print axioms WeakStability.WeakStabilityFunction.ambientHN_exists_of_bounded
#print axioms WeakStability.WeakStabilityFunction.ambientHN_of_bounded
#print axioms WeakStability.heartTorsionPair_tilt_isBounded
#print axioms WeakStability.WeakStabilityFunction.ReverseSlicingObligations
#print axioms WeakStability.WeakStabilityFunction.ReverseSlicingObligations.toSlicing
#print axioms WeakStability.WeakStabilityFunction.ReverseSlicingObligations.toSlicing_P
#print axioms WeakStability.WeakStabilityFunction.ReverseSlicingObligations.toWeakPreStabilityCondition
#print axioms WeakStability.WeakStabilityFunction.ReverseSlicingObligations.toWeakPreStabilityCondition_slicing
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltLatticeCharge
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltLatticeCharge_apply
#print axioms WeakStability.WeakPreStabilityCondition.phaseTilt_ambientPhasePredicate_charge_ray
#print axioms WeakStability.WeakPreStabilityCondition.PhaseTiltHeartObligations.ambientHN_exists_of_mem_tiltedHeart
#print axioms WeakStability.WeakPreStabilityCondition.PhaseTiltHeartObligations.ambientHN
#print axioms WeakStability.WeakPreStabilityCondition.PhaseTiltHeartObligations.toWeakPreStabilityCondition
#print axioms WeakStability.WeakPreStabilityCondition.PhaseTiltHeartObligations.toWeakPreStabilityCondition_Z
#print axioms WeakStability.WeakPreStabilityCondition.PhaseTiltHeartObligations.toWeakPreStabilityCondition_P
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltWeakPreStabilityConditionOfTiltingProperty
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltWeakPreStabilityConditionOfTiltingProperty_Z
#print axioms WeakStability.WeakPreStabilityCondition.phaseTiltWeakPreStabilityConditionOfTiltingProperty_P

/-! ## WeakStability lane -- source-normalized §14 tilting -/

#print axioms WeakStability.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_phase_eq_of_mem_P_phi
#print axioms WeakStability.WeakPreStabilityCondition.ExtremalHNData
#print axioms WeakStability.WeakPreStabilityCondition.extremalHNData
#print axioms WeakStability.WeakPreStabilityCondition.muPlus
#print axioms WeakStability.WeakPreStabilityCondition.muMinus
#print axioms WeakStability.WeakPreStabilityCondition.weakPhaseOfSlope_muPlus
#print axioms WeakStability.WeakPreStabilityCondition.weakPhaseOfSlope_muMinus
#print axioms WeakStability.WeakPreStabilityCondition.slopeCutPhase
#print axioms WeakStability.WeakPreStabilityCondition.slopeCutPhase_mem_Ioo
#print axioms WeakStability.WeakPreStabilityCondition.muMinus_gt_iff_phiMinus_gt
#print axioms WeakStability.WeakPreStabilityCondition.muPlus_le_iff_phiPlus_le
#print axioms WeakStability.WeakPreStabilityCondition.slopeTors
#print axioms WeakStability.WeakPreStabilityCondition.slopeFree
#print axioms WeakStability.WeakPreStabilityCondition.slopeTors_iff_phaseTors
#print axioms WeakStability.WeakPreStabilityCondition.slopeFree_iff_phaseFree
#print axioms WeakStability.WeakPreStabilityCondition.slopeTorsionPair
#print axioms WeakStability.WeakPreStabilityCondition.slopeTorsionPair_tors
#print axioms WeakStability.WeakPreStabilityCondition.slopeTorsionPair_free
#print axioms WeakStability.WeakPreStabilityCondition.slopeTilt_heart_iff
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltScale
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltScale_pos
#print axioms WeakStability.WeakPreStabilityCondition.sourceTilt_multiplier
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltRotation
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltRotation_apply
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltRotation_eq_scale_phaseTiltRotation
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltLatticeCharge
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltLatticeCharge_apply
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltLatticeCharge_eq_scale_phaseTiltLatticeCharge
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltCharge
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltCharge_apply
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltCharge_eq_scale_phaseTiltCharge
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_Z
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_charge
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_charge_eq_scale_phaseTilt
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_slope_eq_phaseTilt
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_isSemistable_iff_phaseTilt
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_isStable_iff_phaseTilt
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_zeroCharge_iff
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_ambientPhasePredicate_eq_phaseTilt
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakPreStabilityConditionOfTiltingProperty
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakPreStabilityConditionOfTiltingProperty_Z
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakPreStabilityConditionOfTiltingProperty_P
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakPreStabilityConditionOfTiltingProperty_P_source
#print axioms WeakStability.sourceTiltLinearCharge
#print axioms WeakStability.sourceTiltLinearCharge_apply
#print axioms WeakStability.sourceTiltLinearCharge_eq_scale_phaseTiltLinearCharge
#print axioms WeakStability.norm_sourceTiltLinearCharge
#print axioms WeakStability.WeakPreStabilityCondition.sourceTilt_hasSupportProperty
#print axioms WeakStability.WeakPreStabilityCondition.SourceTiltConclusion
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltConclusion
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltConclusion_condition_Z
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_isSemistable_iff_phaseClassification
#print axioms WeakStability.WeakPreStabilityCondition.sourceTilt_typeOne_im_nonneg
#print axioms WeakStability.WeakPreStabilityCondition.sourceTilt_typeTwo_im_neg
#print axioms WeakStability.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_isSemistable_iff_classification
#print axioms WeakStability.WeakPreStabilityCondition.hom_eq_zero_of_zeroCharge_to_sourceTiltSemistable
#print axioms WeakStability.WeakStabilityFunction.slope_between_of_triangle
#print axioms WeakStability.WeakStabilityFunction.instAbelianFullSubcategoryHeart
#print axioms WeakStability.WeakStabilityFunction.slope_le_of_heart_epi
#print axioms WeakStability.WeakStabilityFunction.heart_subobject_slope_le
#print axioms WeakStability.WeakStabilityFunction.heart_hom_zero_of_semistable_phase_gt
#print axioms WeakStability.WeakStabilityFunction.ambientPhasePredicate_hom_zero
#print axioms WeakStability.WeakStabilityFunction.reverseSlicingObligationsOfHN

/-! ## Support lane — the Kontsevich-Soibelman quadratic-form reformulation

The basic statements are linear algebra plus one compactness argument over a
finite-dimensional real normed space and keep `S` arbitrary. The later
genuine/uniform/quotient declarations add bundled quadratic forms, a saturated
integral quotient, and a weak-stability adapter whose selected loci are actual
nonzero weak-semistable heart classes. The adapter still supplies no geometric
family, HN structure over a curve, boundedness, or moduli theory. -/

#print axioms Support.HasSupportProperty
#print axioms Support.IsHomogTwo
#print axioms Support.IsCompatible
#print axioms Support.slice
#print axioms Support.isCompact_slice
#print axioms Support.norm_inv_smul_mem_slice
#print axioms Support.hasSupportProperty_of_isCompatible
#print axioms Support.exists_isCompatible_of_hasSupportProperty
#print axioms Support.hasSupportProperty_iff
#print axioms Support.HasSupportProperty.mono
#print axioms Support.HasSupportProperty.eq_zero_of_charge_eq_zero
#print axioms Support.hasSupportProperty_of_norm_sub_le
#print axioms Support.HasSupportProperty.exists_tolerance
#print axioms Support.isOpen_hasSupportProperty
#print axioms Support.quadraticForm_isHomogTwo
#print axioms Support.HasQuadraticSupportProperty
#print axioms Support.HasQuadraticSupportProperty.hasSupportProperty
#print axioms Support.HasQuadraticSupportProperty.mono
#print axioms Support.familyLocus
#print axioms Support.HasUniformQuadraticSupportProperty
#print axioms Support.HasUniformQuadraticSupportProperty.fiber
#print axioms Support.hasUniformQuadraticSupportProperty_of_union
#print axioms Support.hasUniformQuadraticSupportProperty_iff_union
#print axioms Support.HasUniformQuadraticSupportProperty.reindex
#print axioms Support.HasQuadraticSupportProperty.constant
#print axioms Support.hasUniformQuadraticSupportProperty_constant_iff
#print axioms Support.transportQuadraticForm
#print axioms Support.transportQuadraticForm_apply
#print axioms Support.isCompatible_transport
#print axioms Support.HasUniformQuadraticSupportProperty.transport
#print axioms Support.hasUniformQuadraticSupportProperty_transport_iff
#print axioms Support.quotientCharge
#print axioms Support.quotientCharge_mkQ
#print axioms Support.quotientFamilyLocus
#print axioms Support.HasUniformQuadraticSupportPropertyModulo
#print axioms Support.hasUniformQuadraticSupportPropertyModulo_iff
#print axioms Support.HasUniformQuadraticSupportPropertyModulo.fiber
#print axioms Support.HasUniformQuadraticSupportPropertyModulo.hasSupportProperty
#print axioms Support.mkQ_eq_zero_of_mem
#print axioms Support.HasQuadraticSupportProperty.constant_modulo
#print axioms Support.ZeroChargeLattice.IsSaturated
#print axioms Support.ZeroChargeLattice.saturatedClosure
#print axioms Support.ZeroChargeLattice.subset_saturatedClosure
#print axioms Support.ZeroChargeLattice.isSaturated_saturatedClosure
#print axioms Support.ZeroChargeLattice.saturatedClosure_le
#print axioms Support.ZeroChargeLattice.neg_mem_saturatedClosure_iff
#print axioms Support.ZeroChargeLattice.Quotient
#print axioms Support.ZeroChargeLattice.quotientClass
#print axioms Support.ZeroChargeLattice.quotientClass_eq_zero_iff
#print axioms Support.ZeroChargeLattice.quotient_isAddTorsionFree
#print axioms Support.ZeroChargeLattice.quotient_moduleFinite
#print axioms Support.ZeroChargeLattice.quotient_moduleFree
#print axioms Support.ZeroChargeLattice.saturatedClosure_le_ker
#print axioms Support.ZeroChargeLattice.quotientCharge
#print axioms Support.ZeroChargeLattice.quotientCharge_quotientClass

/-! ## FiniteLength lane — charges on the free lattice of simples

`Fin n -> Z` is a MODEL of `K_0(A)` for a finite-length abelian category, not
an identification: that is Jordan-Holder, which exists in neither Mathlib nor
the foundational library. Every result is a theorem about `Fin n -> Z`. -/

#print axioms FiniteLength.mem_cone_smul
#print axioms FiniteLength.mem_cone_sum
#print axioms FiniteLength.chargeOf
#print axioms FiniteLength.chargeOf_apply
#print axioms FiniteLength.chargeOf_single
#print axioms FiniteLength.eq_chargeOf
#print axioms FiniteLength.existsUnique_charge
#print axioms FiniteLength.mem_cone_natCombination
#print axioms FiniteLength.chargeOf_mem_cone
#print axioms FiniteLength.chargeOf_ne_zero

/-! ## Wall lane — numerical walls in the (s, t) half plane

Arithmetic on triples of reals. There is NO surface: no coherent sheaf, no
Chern character, no polarisation, and no Bogomolov-Gieseker inequality -- and
none is axiomatised, because the wall equation is an identity and needs none. -/

#print axioms Wall.NumClass
#print axioms Wall.NumClass.rk
#print axioms Wall.NumClass.deg
#print axioms Wall.NumClass.ch2
#print axioms Wall.reZ
#print axioms Wall.imZ
#print axioms Wall.minA
#print axioms Wall.minB
#print axioms Wall.minC
#print axioms Wall.wallExpr
#print axioms Wall.wallExpr_eq
#print axioms Wall.wall_iff_circle
#print axioms Wall.wall_circle_eq
#print axioms Wall.wall_line_eq
#print axioms Wall.shift
#print axioms Wall.minA_shift
#print axioms Wall.minB_shift
#print axioms Wall.minC_shift
#print axioms Wall.wallExpr_shift
#print axioms Wall.charge_eq_zero_iff
#print axioms Wall.eq_of_two_walls

/-! ### Wall lane — the nested wall theorem

Still the same arithmetic: `wall_eq_of_meet` is a statement about triples of
reals and says nothing about sheaves. In particular it is NOT the geometric
nested-wall theorem, which additionally asserts that the walls it orders are
walls of actual stability, and that is not expressible at the pin.

`wall_eq_of_meet_needs_charge` is a counterexample, not a theorem about walls:
it exhibits two genuinely different walls meeting at the one point where `v`'s
charge degenerates, which is what makes the charge hypothesis load-bearing
rather than decorative. -/

#print axioms Wall.minor_orth
#print axioms Wall.crossAB
#print axioms Wall.crossAC
#print axioms Wall.crossBC
#print axioms Wall.crossAB_swap
#print axioms Wall.crossAC_swap
#print axioms Wall.crossBC_swap
#print axioms Wall.minorCross_eq_zero_of_two_walls
#print axioms Wall.wall_subset_of_crossZero
#print axioms Wall.wall_eq_of_meet
#print axioms Wall.degV
#print axioms Wall.degV_charge_eq_zero
#print axioms Wall.wall_eq_of_meet_needs_charge

/-! ## GroupAction lane — NormalizedShift (step 1) -/

#print axioms GroupAction.NormalizedShift
#print axioms GroupAction.NormalizedShift.toOrderIso_injective
#print axioms GroupAction.NormalizedShift.ext'
#print axioms GroupAction.NormalizedShift.symm_map_add_one
#print axioms GroupAction.NormalizedShift.group
#print axioms GroupAction.NormalizedShift.mul_apply
#print axioms GroupAction.NormalizedShift.one_apply
#print axioms GroupAction.NormalizedShift.inv_apply

/-! ## GroupAction lane — ShiftAnalysis (step 3c groundwork) -/

#print axioms GroupAction.NormalizedShift.map_add_nat
#print axioms GroupAction.NormalizedShift.map_sub_nat
#print axioms GroupAction.NormalizedShift.map_add_int
#print axioms GroupAction.NormalizedShift.uniformContinuous
#print axioms GroupAction.NormalizedShift.exists_radius

/-! ## GroupAction lane — GLTilde (step 2) -/

#print axioms GroupAction.rayVec
#print axioms GroupAction.rayVec_add_one
#print axioms GroupAction.rayVec_ne_zero
#print axioms GroupAction.OnRay
#print axioms GroupAction.OnRay.refl
#print axioms GroupAction.OnRay.trans
#print axioms GroupAction.toMat
#print axioms GroupAction.toMat_mul
#print axioms GroupAction.toMat_one
#print axioms GroupAction.Compatible
#print axioms GroupAction.compat_one
#print axioms GroupAction.compat_mul
#print axioms GroupAction.compat_inv
#print axioms GroupAction.GLTilde
#print axioms GroupAction.GLTilde.ext'
#print axioms GroupAction.GLTilde.group
#print axioms GroupAction.GLTilde.mul_mat
#print axioms GroupAction.GLTilde.mul_shift
#print axioms GroupAction.GLTilde.one_mat
#print axioms GroupAction.GLTilde.one_shift
#print axioms GroupAction.GLTilde.inv_mat
#print axioms GroupAction.GLTilde.inv_shift
#print axioms GroupAction.GLTilde.toMatHom
#print axioms GroupAction.GLTilde.toShiftHom

/-! ## GroupAction lane — ComplexBridge (step 3 groundwork) -/

#print axioms GroupAction.cplxCoord
#print axioms GroupAction.cplxCoord_exp
#print axioms GroupAction.compat_exp
#print axioms GroupAction.actC
#print axioms GroupAction.actC_apply
#print axioms GroupAction.actC_one
#print axioms GroupAction.actC_mul
#print axioms GroupAction.actC_exp

/-! ## GroupAction lane — SlicingAction (step 3a) -/

#print axioms GroupAction.relabel
#print axioms GroupAction.relabel_P
#print axioms GroupAction.slicingMulAction
#print axioms GroupAction.smul_slicing_P
#print axioms GroupAction.gltildeSlicingMulAction
#print axioms GroupAction.gltilde_smul_slicing_P
#print axioms GroupAction.relabel_intervalProp_iff
#print axioms GroupAction.relabel_intervalProp

/-! ## GroupAction lane — PreStabilityAction (step 3b) -/

#print axioms GroupAction.actPre
#print axioms GroupAction.actPre_slicing
#print axioms GroupAction.actPre_Z
#print axioms GroupAction.preMulAction
#print axioms GroupAction.smul_pre_slicing
#print axioms GroupAction.smul_pre_Z

/-! ## GroupAction lane — StabilityAction (step 3c) -/

#print axioms GroupAction.relabel_isLocallyFinite
#print axioms GroupAction.actStab
#print axioms GroupAction.actStab_slicing
#print axioms GroupAction.actStab_Z
#print axioms GroupAction.stabMulAction
#print axioms GroupAction.smul_stab_slicing
#print axioms GroupAction.smul_stab_Z

/-! ## AutAction — transport along a triangulated auto-equivalence

These extend the foundational library's own namespace, since they are API for its types. -/

#print axioms CategoryTheory.Triangulated.PostnikovTower.mapF
#print axioms CategoryTheory.Triangulated.HNFiltration.mapF
#print axioms CategoryTheory.Triangulated.Slicing.mapEquiv
#print axioms CategoryTheory.Triangulated.Slicing.mapEquiv_P

/-! ## StrictAutAction — a strict subgroup of autoequivalences -/

#print axioms GroupAction.StrictAut
#print axioms GroupAction.StrictAut.comp_inv
#print axioms GroupAction.StrictAut.inv_comp
#print axioms GroupAction.StrictAut.obj_inv
#print axioms GroupAction.StrictAut.obj_self
#print axioms GroupAction.StrictAut.F_inv_one
#print axioms GroupAction.StrictAut.F_inv_mul
#print axioms GroupAction.StrictAut.equiv
#print axioms GroupAction.StrictAut.equiv_functor
#print axioms GroupAction.StrictAut.equiv_inverse
#print axioms GroupAction.StrictAut.actSlicing
#print axioms GroupAction.StrictAut.actSlicing_P
#print axioms GroupAction.StrictAut.mulActionSlicing

/-! ## QuotAutAction — Aut(D) as an honest group, by quotienting -/

#print axioms GroupAction.TriEquiv
#print axioms GroupAction.TriEquiv.id
#print axioms GroupAction.TriEquiv.comp
#print axioms GroupAction.TriEquiv.symm
#print axioms GroupAction.TriEquiv.act
#print axioms GroupAction.TriEquiv.act_P
#print axioms GroupAction.TriEquiv.act_id
#print axioms GroupAction.TriEquiv.act_comp
#print axioms GroupAction.TriEquiv.act_congr
#print axioms GroupAction.TriEquiv.setoid
#print axioms GroupAction.AutQuot
#print axioms GroupAction.AutQuot.group
#print axioms GroupAction.AutQuot.mulActionSlicing
#print axioms GroupAction.AutQuot.mk
#print axioms GroupAction.AutQuot.mk_smul_P

/-! ## K0Functor — K₀ is functorial in triangulated functors -/

#print axioms CategoryTheory.Triangulated.isTriangleAdditive_of_isTriangulated
#print axioms CategoryTheory.Triangulated.K₀.mapF
#print axioms CategoryTheory.Triangulated.K₀.mapF_of
#print axioms CategoryTheory.Triangulated.K₀.mapF_id
#print axioms CategoryTheory.Triangulated.K₀.mapF_comp
#print axioms CategoryTheory.Triangulated.K₀.mapF_congr

/-! ## StrictFiniteLength — general strict-hypothesis transfer -/

#print axioms CategoryTheory.Triangulated.strictImage
#print axioms CategoryTheory.Triangulated.strictImage_monotone
#print axioms CategoryTheory.Triangulated.strictImage_injective
#print axioms CategoryTheory.Triangulated.strictImage_strictMono
#print axioms CategoryTheory.Triangulated.isStrictArtinian_of_faithful_strict
#print axioms CategoryTheory.Triangulated.isStrictNoetherian_of_faithful_strict
#print axioms CategoryTheory.Triangulated.mapEquiv_intervalProp_iff

/-! ## AutStabilityAction — the Aut action on stability conditions -/

#print axioms CategoryTheory.Triangulated.autIntervalFunctor
#print axioms CategoryTheory.Triangulated.autFunctor_strictMono
#print axioms CategoryTheory.Triangulated.mapEquiv_isLocallyFinite
#print axioms CategoryTheory.Triangulated.actStabAut
#print axioms CategoryTheory.Triangulated.actStabAut_slicing
#print axioms CategoryTheory.Triangulated.actStabAut_Z

/-! ## GLTildeFibre — the fibre of the projection is Z -/

#print axioms BridgelandStabLean.GroupAction.rayVec_eq_iff
#print axioms BridgelandStabLean.GroupAction.rayVec_eq_of_onRay
#print axioms BridgelandStabLean.GroupAction.deckShift
#print axioms BridgelandStabLean.GroupAction.deckShift_apply
#print axioms BridgelandStabLean.GroupAction.compat_one_deckShift
#print axioms BridgelandStabLean.GroupAction.deck
#print axioms BridgelandStabLean.GroupAction.deck_mat
#print axioms BridgelandStabLean.GroupAction.deck_shift
#print axioms BridgelandStabLean.GroupAction.exists_deckShift_of_mat_eq_one
#print axioms BridgelandStabLean.GroupAction.deckHom
#print axioms BridgelandStabLean.GroupAction.deckHom_injective
#print axioms BridgelandStabLean.GroupAction.range_deckHom_eq_ker
#print axioms BridgelandStabLean.GroupAction.kerEquiv

/-! ## GLTildeSurj — the projection is surjective

COVERAGE COMPLETE as of 2026-08-07. This section was the single largest gap in
the file: `scripts/Census.lean` reported **20** ungated public declarations
here, more than in any other module and more than a third of the whole
shortfall, and the figure had been quoted in this file's docstring since
2026-08-06 without moving.

The 20 added are, in source order: `cexpI_re`, `cexpI_im`, `cexpI_add`,
`norm_cexpI`, `cexpI_ne_zero`, `cplxCoord_cexpI`, `det_toMat_pos`,
`normSq_cB_lt_normSq_cA`, `cA_ne_zero`, `ratio`, `norm_ratio_lt_one`,
`Wmap_ne_zero`, `cexpI_neg_two_pi`, `pi_mul_lift`, `lift_scale_pos`,
`cross_smul`, `abs_arg_Wmap_lt`, `lift_add_nat`, `liftShift_apply`, `sect_mat`.

Five of them were missed by every earlier source-text pass because they are
`@[simp] theorem` on ONE line -- a regex anchored on `^theorem` never sees
them. That is the same class of miss the docstring's projection paragraph
records, and it is why the count is now taken from the environment.

The list below is in SOURCE ORDER and is complete: 49 public declarations, plus
`sin_pos_unique` and `lift_lt_of_sub_lt_nat` which are `private` and therefore
structurally unlistable here. Keep the order when adding, so a reader can diff
this against the file by eye. -/

#print axioms BridgelandStabLean.GroupAction.cexpI
#print axioms BridgelandStabLean.GroupAction.cexpI_re
#print axioms BridgelandStabLean.GroupAction.cexpI_im
#print axioms BridgelandStabLean.GroupAction.cexpI_add
#print axioms BridgelandStabLean.GroupAction.norm_cexpI
#print axioms BridgelandStabLean.GroupAction.cexpI_ne_zero
#print axioms BridgelandStabLean.GroupAction.cplxCoord_apply
#print axioms BridgelandStabLean.GroupAction.cplxCoord_cexpI
#print axioms BridgelandStabLean.GroupAction.cA
#print axioms BridgelandStabLean.GroupAction.cB
#print axioms BridgelandStabLean.GroupAction.mulVec_rayVec_eq
#print axioms BridgelandStabLean.GroupAction.normSq_cA_sub_normSq_cB
#print axioms BridgelandStabLean.GroupAction.det_toMat_pos
#print axioms BridgelandStabLean.GroupAction.normSq_cB_lt_normSq_cA
#print axioms BridgelandStabLean.GroupAction.cA_ne_zero
#print axioms BridgelandStabLean.GroupAction.norm_cB_lt_norm_cA
#print axioms BridgelandStabLean.GroupAction.ratio
#print axioms BridgelandStabLean.GroupAction.norm_ratio_lt_one
#print axioms BridgelandStabLean.GroupAction.Wmap
#print axioms BridgelandStabLean.GroupAction.Wmap_re_pos
#print axioms BridgelandStabLean.GroupAction.Wmap_ne_zero
#print axioms BridgelandStabLean.GroupAction.cexpI_neg_two_pi
#print axioms BridgelandStabLean.GroupAction.Wmap_add_one
#print axioms BridgelandStabLean.GroupAction.lift
#print axioms BridgelandStabLean.GroupAction.pi_mul_lift
#print axioms BridgelandStabLean.GroupAction.mulVec_rayVec_lift
#print axioms BridgelandStabLean.GroupAction.lift_scale_pos
#print axioms BridgelandStabLean.GroupAction.compatible_lift
#print axioms BridgelandStabLean.GroupAction.lift_add_one
#print axioms BridgelandStabLean.GroupAction.cross
#print axioms BridgelandStabLean.GroupAction.cross_rayVec
#print axioms BridgelandStabLean.GroupAction.cross_mulVec
#print axioms BridgelandStabLean.GroupAction.cross_smul
#print axioms BridgelandStabLean.GroupAction.abs_arg_Wmap_lt
#print axioms BridgelandStabLean.GroupAction.lift_lt_lift_of_lt_of_sub_lt_one
#print axioms BridgelandStabLean.GroupAction.lift_add_nat
#print axioms BridgelandStabLean.GroupAction.lift_strictMono
#print axioms BridgelandStabLean.GroupAction.lift_continuous
#print axioms BridgelandStabLean.GroupAction.lift_surjective
#print axioms BridgelandStabLean.GroupAction.liftShift
#print axioms BridgelandStabLean.GroupAction.liftShift_apply
#print axioms BridgelandStabLean.GroupAction.compatible_liftShift
#print axioms BridgelandStabLean.GroupAction.toMatHom_surjective
#print axioms BridgelandStabLean.GroupAction.sect
#print axioms BridgelandStabLean.GroupAction.sect_mat
#print axioms BridgelandStabLean.GroupAction.toMatHom_comp_sect
#print axioms BridgelandStabLean.GroupAction.deck_injective
#print axioms BridgelandStabLean.GroupAction.existsUnique_deck_mul_sect
#print axioms BridgelandStabLean.GroupAction.exact_deckHom_toMatHom

/-! ## GLTildeTopology — topology and simple connectedness -/

#print axioms BridgelandStabLean.GroupAction.rotationMatrix
#print axioms BridgelandStabLean.GroupAction.rotationMatrix_det
#print axioms BridgelandStabLean.GroupAction.rotationMatrix_mulVec_rayVec
#print axioms BridgelandStabLean.GroupAction.rotationMatrix_neg_mul
#print axioms BridgelandStabLean.GroupAction.rotationMatrix_mul_neg
#print axioms BridgelandStabLean.GroupAction.rotationGLPos
#print axioms BridgelandStabLean.GroupAction.rotationGLPos_mat
#print axioms BridgelandStabLean.GroupAction.phaseTranslation
#print axioms BridgelandStabLean.GroupAction.phaseTranslation_apply
#print axioms BridgelandStabLean.GroupAction.compatible_rotation
#print axioms BridgelandStabLean.GroupAction.liftedRotation
#print axioms BridgelandStabLean.GroupAction.liftedRotation_mat
#print axioms BridgelandStabLean.GroupAction.liftedRotation_shift_zero
#print axioms BridgelandStabLean.GroupAction.GLTilde.ext_mat_shift_zero
#print axioms BridgelandStabLean.GroupAction.PositiveReal
#print axioms BridgelandStabLean.GroupAction.GLTildeCoordinates
#print axioms BridgelandStabLean.GroupAction.upperMatrix
#print axioms BridgelandStabLean.GroupAction.upperMatrix_det
#print axioms BridgelandStabLean.GroupAction.upperMatrixInv
#print axioms BridgelandStabLean.GroupAction.upperMatrix_mul_inv
#print axioms BridgelandStabLean.GroupAction.upperMatrix_inv_mul
#print axioms BridgelandStabLean.GroupAction.upperGLPos
#print axioms BridgelandStabLean.GroupAction.upperGLPos_mat
#print axioms BridgelandStabLean.GroupAction.alignedMatrix
#print axioms BridgelandStabLean.GroupAction.alignedMatrix_zero_zero_pos
#print axioms BridgelandStabLean.GroupAction.alignedMatrix_one_zero
#print axioms BridgelandStabLean.GroupAction.alignedMatrix_one_one_pos
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinates
#print axioms BridgelandStabLean.GroupAction.matrixOfCoordinates
#print axioms BridgelandStabLean.GroupAction.matrixOfCoordinates_apply
#print axioms BridgelandStabLean.GroupAction.upperDeckIndex
#print axioms BridgelandStabLean.GroupAction.upperDeckIndex_spec
#print axioms BridgelandStabLean.GroupAction.upperSectionZero
#print axioms BridgelandStabLean.GroupAction.upperSectionZero_mat
#print axioms BridgelandStabLean.GroupAction.upperSectionZero_shift_zero
#print axioms BridgelandStabLean.GroupAction.glTildeOfCoordinates
#print axioms BridgelandStabLean.GroupAction.glTildeOfCoordinates_shift_zero
#print axioms BridgelandStabLean.GroupAction.glTildeOfCoordinates_mat
#print axioms BridgelandStabLean.GroupAction.alignedMatrix_glTildeOfCoordinates
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinates_ofCoordinates
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinates_injective
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinates_surjective
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinateEquiv
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinateEquiv_apply
#print axioms BridgelandStabLean.GroupAction.GLTilde.topologicalSpace
#print axioms BridgelandStabLean.GroupAction.glTildeCoordinateHomeomorph
#print axioms BridgelandStabLean.GroupAction.continuous_rotationMatrix
#print axioms BridgelandStabLean.GroupAction.glTildeOfCoordinates_coordinates
#print axioms BridgelandStabLean.GroupAction.GLTilde.continuous_toMat
#print axioms BridgelandStabLean.GroupAction.GLTilde.contractibleSpace
#print axioms BridgelandStabLean.GroupAction.GLTilde.simplyConnectedSpace

/-! ## GLTildeCover — base coordinates and the universal covering map -/

#print axioms BridgelandStabLean.GroupAction.circleMatrix
#print axioms BridgelandStabLean.GroupAction.circleMatrixInv
#print axioms BridgelandStabLean.GroupAction.circleMatrix_det
#print axioms BridgelandStabLean.GroupAction.circleMatrix_mul_inv
#print axioms BridgelandStabLean.GroupAction.circleMatrix_inv_mul
#print axioms BridgelandStabLean.GroupAction.circleGLPos
#print axioms BridgelandStabLean.GroupAction.circleGLPos_mat
#print axioms BridgelandStabLean.GroupAction.GLPosCoordinates
#print axioms BridgelandStabLean.GroupAction.firstColumnComplex
#print axioms BridgelandStabLean.GroupAction.firstColumnComplex_ne_zero
#print axioms BridgelandStabLean.GroupAction.firstColumnRadius
#print axioms BridgelandStabLean.GroupAction.firstColumnDirection
#print axioms BridgelandStabLean.GroupAction.firstColumnDirection_re
#print axioms BridgelandStabLean.GroupAction.firstColumnDirection_im
#print axioms BridgelandStabLean.GroupAction.secondColumnAlong
#print axioms BridgelandStabLean.GroupAction.secondColumnPerp
#print axioms BridgelandStabLean.GroupAction.secondColumnPerp_pos
#print axioms BridgelandStabLean.GroupAction.glPosCoordinates
#print axioms BridgelandStabLean.GroupAction.glPosOfCoordinates
#print axioms BridgelandStabLean.GroupAction.glPosOfCoordinates_mat
#print axioms BridgelandStabLean.GroupAction.firstColumnDirection_glPosOfCoordinates
#print axioms BridgelandStabLean.GroupAction.secondColumnAlong_glPosOfCoordinates
#print axioms BridgelandStabLean.GroupAction.secondColumnPerp_glPosOfCoordinates
#print axioms BridgelandStabLean.GroupAction.glPosCoordinates_ofCoordinates
#print axioms BridgelandStabLean.GroupAction.glPosOfCoordinates_coordinates
#print axioms BridgelandStabLean.GroupAction.continuous_toMatGLPos
#print axioms BridgelandStabLean.GroupAction.glPosCoordinateHomeomorph
#print axioms BridgelandStabLean.GroupAction.isCoveringMap_prodMap_id
#print axioms BridgelandStabLean.GroupAction.phaseCircle
#print axioms BridgelandStabLean.GroupAction.phaseCircle_isCoveringMap
#print axioms BridgelandStabLean.GroupAction.coordinateProjection
#print axioms BridgelandStabLean.GroupAction.coordinateProjection_isCoveringMap
#print axioms BridgelandStabLean.GroupAction.phaseCircle_coe
#print axioms BridgelandStabLean.GroupAction.circleMatrix_phaseCircle
#print axioms BridgelandStabLean.GroupAction.glPosOfCoordinates_coordinateProjection
#print axioms BridgelandStabLean.GroupAction.coordinateProjection_apply_glTildeCoordinates
#print axioms BridgelandStabLean.GroupAction.GLTilde.isCoveringMap_toMat
#print axioms BridgelandStabLean.GroupAction.GLTilde.universalCoverData

/-! ## GLTildeTopologicalGroup — compatibility of topology and group operations -/

#print axioms BridgelandStabLean.GroupAction.upperSectionZero_shift_apply
#print axioms BridgelandStabLean.GroupAction.coordinateShift
#print axioms BridgelandStabLean.GroupAction.glTildeOfCoordinates_shift_apply
#print axioms BridgelandStabLean.GroupAction.GLTilde.continuous_shift_apply
#print axioms BridgelandStabLean.GroupAction.GLTilde.isTopologicalGroup

/-! ## AutPairAction — the same action, as a genuine `MulAction` -/

#print axioms BridgelandStabLean.GroupAction.AutPair
#print axioms BridgelandStabLean.GroupAction.AutPair.id
#print axioms BridgelandStabLean.GroupAction.AutPair.mul
#print axioms BridgelandStabLean.GroupAction.AutPair.inv
#print axioms BridgelandStabLean.GroupAction.AutPair.setoid
#print axioms BridgelandStabLean.GroupAction.AutPair.act
#print axioms BridgelandStabLean.GroupAction.AutPair.act_slicing
#print axioms BridgelandStabLean.GroupAction.AutPair.act_Z
#print axioms BridgelandStabLean.GroupAction.AutPair.act_id
#print axioms BridgelandStabLean.GroupAction.AutPair.act_mul
#print axioms BridgelandStabLean.GroupAction.AutPair.act_congr
#print axioms BridgelandStabLean.GroupAction.AutPairQuot
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.mk
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.group
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.mulAction
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.mk_smul_slicing
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.mk_smul_Z
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.toAutQuot

/-! ## Normalized quotient, combined action, and topological action layer -/

#print axioms BridgelandStabLean.GroupAction.TriEquiv.inverseIsoOfFunctorIso

#print axioms BridgelandStabLean.GroupAction.relabel_mapEquiv
#print axioms BridgelandStabLean.GroupAction.gltilde_autPair_smul_comm
#print axioms BridgelandStabLean.GroupAction.smulCommClassGLTildeAutPairQuot
#print axioms BridgelandStabLean.GroupAction.combinedMulAction
#print axioms BridgelandStabLean.GroupAction.prod_mk_smul_slicing
#print axioms BridgelandStabLean.GroupAction.prod_mk_smul_Z

#print axioms BridgelandStabLean.GroupAction.Slicing.mapEquiv_phiPlus
#print axioms BridgelandStabLean.GroupAction.Slicing.mapEquiv_phiMinus
#print axioms BridgelandStabLean.GroupAction.slicingDist_mapEquiv_le
#print axioms BridgelandStabLean.GroupAction.stabSeminorm_aut_le
#print axioms BridgelandStabLean.GroupAction.AutPair.mapsTo_basisNhd
#print axioms BridgelandStabLean.GroupAction.AutPair.continuous_act
#print axioms BridgelandStabLean.GroupAction.autPairQuotContinuousConstSMul
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.homeomorph

#print axioms BridgelandStabLean.GroupAction.Slicing.relabel_phiPlus
#print axioms BridgelandStabLean.GroupAction.Slicing.relabel_phiMinus
#print axioms BridgelandStabLean.GroupAction.exists_slicingDist_relabel_control
#print axioms BridgelandStabLean.GroupAction.actCCLM
#print axioms BridgelandStabLean.GroupAction.actCCLM_apply
#print axioms BridgelandStabLean.GroupAction.actC_inv_apply
#print axioms BridgelandStabLean.GroupAction.actCCondition
#print axioms BridgelandStabLean.GroupAction.actCCondition_pos
#print axioms BridgelandStabLean.GroupAction.norm_actC_div_norm_actC_le
#print axioms BridgelandStabLean.GroupAction.stabSeminorm_gltilde_le
#print axioms BridgelandStabLean.GroupAction.exists_gltilde_basisNhd_control
#print axioms BridgelandStabLean.GroupAction.GLTilde.continuous_const_smul_stability
#print axioms BridgelandStabLean.GroupAction.gltildeContinuousConstSMulStability
#print axioms BridgelandStabLean.GroupAction.combinedContinuousConstSMulStability
#print axioms BridgelandStabLean.GroupAction.GLTilde.stabilityHomeomorph
#print axioms BridgelandStabLean.GroupAction.combinedStabilityHomeomorph

/-! ## Jointly continuous symmetry actions -/

#print axioms BridgelandStabLean.GroupAction.GLTilde.continuous_shift_displacement
#print axioms BridgelandStabLean.GroupAction.GLTilde.eventually_uniform_shift_displacement
#print axioms BridgelandStabLean.GroupAction.slicingDist_smul_le_of_displacement
#print axioms BridgelandStabLean.GroupAction.actCCLM_one
#print axioms BridgelandStabLean.GroupAction.GLTilde.continuous_actCCLM
#print axioms BridgelandStabLean.GroupAction.norm_actC_sub_div_le
#print axioms BridgelandStabLean.GroupAction.stabSeminorm_near_identity_le
#print axioms BridgelandStabLean.GroupAction.exists_identity_basisNhd_control
#print axioms BridgelandStabLean.GroupAction.continuousAt_smul_identity
#print axioms BridgelandStabLean.GroupAction.GLTilde.continuousAt_smul_stability
#print axioms BridgelandStabLean.GroupAction.GLTilde.continuous_smul_stability
#print axioms BridgelandStabLean.GroupAction.gltildeContinuousSMulStability
#print axioms BridgelandStabLean.GroupAction.autPairQuotTopologicalSpace
#print axioms BridgelandStabLean.GroupAction.autPairQuotDiscreteTopology
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.continuous_smul_stability
#print axioms BridgelandStabLean.GroupAction.autPairQuotContinuousSMulStability
#print axioms BridgelandStabLean.GroupAction.continuous_combined_smul_stability
#print axioms BridgelandStabLean.GroupAction.combinedContinuousSMulStability

/-! ## Components, equivariant periods, and the effective symmetry quotient -/

#print axioms BridgelandStabLean.GroupAction.componentSmul
#print axioms BridgelandStabLean.GroupAction.componentSmul_mk
#print axioms BridgelandStabLean.GroupAction.componentMulAction
#print axioms BridgelandStabLean.GroupAction.image_connectedComponent_smul
#print axioms BridgelandStabLean.GroupAction.componentHomeomorph
#print axioms BridgelandStabLean.GroupAction.componentHomeomorph_apply_coe
#print axioms BridgelandStabLean.GroupAction.componentStabilizer
#print axioms BridgelandStabLean.GroupAction.mem_componentStabilizer_iff
#print axioms BridgelandStabLean.GroupAction.componentStabilizerMulAction

#print axioms BridgelandStabLean.GroupAction.GLTilde.chargeAddEquiv
#print axioms BridgelandStabLean.GroupAction.GLTilde.chargeAddEquiv_apply
#print axioms BridgelandStabLean.GroupAction.AutPair.chargeAddEquiv
#print axioms BridgelandStabLean.GroupAction.AutPair.chargeAddEquiv_apply
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.chargeAddEquiv
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.chargeAddEquiv_mk
#print axioms BridgelandStabLean.GroupAction.combinedChargeAddEquiv
#print axioms BridgelandStabLean.GroupAction.combinedChargeAddEquiv_mk_apply
#print axioms BridgelandStabLean.GroupAction.GLTilde.centralCharge_equivariant
#print axioms BridgelandStabLean.GroupAction.AutPairQuot.centralCharge_equivariant
#print axioms BridgelandStabLean.GroupAction.combinedCentralCharge_equivariant
#print axioms BridgelandStabLean.GroupAction.combinedCentralCharge_equivariant_apply
#print axioms BridgelandStabLean.GroupAction.componentCentralCharge_equivariant
#print axioms BridgelandStabLean.GroupAction.componentLocalModel_chargeMap_equivariant

#print axioms BridgelandStabLean.GroupAction.shiftFunctorCommShift
#print axioms BridgelandStabLean.GroupAction.shiftTwoMapTriangleIso
#print axioms BridgelandStabLean.GroupAction.shiftTwoIsTriangulated
#print axioms BridgelandStabLean.GroupAction.shiftNegTwoMapTriangleIso
#print axioms BridgelandStabLean.GroupAction.shiftNegTwoIsTriangulated
#print axioms BridgelandStabLean.GroupAction.shiftTwoTriEquiv
#print axioms BridgelandStabLean.GroupAction.K₀.mapF_shift_neg_two
#print axioms BridgelandStabLean.GroupAction.shiftTwoPair
#print axioms BridgelandStabLean.GroupAction.deckShift_neg_one_inv_apply
#print axioms BridgelandStabLean.GroupAction.shiftTwoPair_act_eq_deck_neg_one
#print axioms BridgelandStabLean.GroupAction.deck_mul_deck
#print axioms BridgelandStabLean.GroupAction.deck_zero
#print axioms BridgelandStabLean.GroupAction.deck_one_shiftTwo_combined_smul
#print axioms BridgelandStabLean.GroupAction.combinedActionHom
#print axioms BridgelandStabLean.GroupAction.combinedActionKernel
#print axioms BridgelandStabLean.GroupAction.EffectiveCombinedSymmetry
#print axioms BridgelandStabLean.GroupAction.effectiveCombinedPermHom
#print axioms BridgelandStabLean.GroupAction.effectiveCombinedMulAction
#print axioms BridgelandStabLean.GroupAction.effectiveCombinedFaithfulSMul
#print axioms BridgelandStabLean.GroupAction.deck_one_shiftTwo_mem_combinedActionKernel
#print axioms BridgelandStabLean.GroupAction.deck_one_shiftTwo_eq_one_in_effective

/-! ## AutIsometry — the action preserves the foundational library's phase distance -/

#print axioms CategoryTheory.Triangulated.Slicing.phiPlus_congr
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_congr
#print axioms CategoryTheory.Triangulated.isZero_inverse_iff
#print axioms CategoryTheory.Triangulated.isZero_functor_iff
#print axioms CategoryTheory.Triangulated.mapEquiv_phiPlus
#print axioms CategoryTheory.Triangulated.mapEquiv_phiMinus
#print axioms CategoryTheory.Triangulated.mapEquiv_slicingDist
#print axioms CategoryTheory.Triangulated.actStabAut_slicingDist
#print axioms CategoryTheory.Triangulated.AutPairQuot_smul_slicingDist

/-! ## StabilityMass — choice-free HN mass envelope -/

#print axioms CategoryTheory.Triangulated.HNFiltration.mass
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.charge_ne_zero_of_semistable
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_pos
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_ofIso
#print axioms CategoryTheory.Triangulated.stabilityMass
#print axioms CategoryTheory.Triangulated.stabilityMass_pos
#print axioms CategoryTheory.Triangulated.stabilityMass_congr
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_eq_zero_of_isZero
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_eq_mass
#print axioms CategoryTheory.Triangulated.stabilityMass_eq_mass
#print axioms CategoryTheory.Triangulated.stabilityMass_ne_top
#print axioms CategoryTheory.Triangulated.stabilityMass_lt_top
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_sum
#print axioms CategoryTheory.Triangulated.stabilityMass_eq_zero_iff
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_pos
#print axioms BridgelandStabLean.GroupAction.AutPair.act_charge
#print axioms BridgelandStabLean.GroupAction.AutPair.mass_map_inverse
#print axioms BridgelandStabLean.GroupAction.AutPair.mass_map_functor
#print axioms BridgelandStabLean.GroupAction.AutPair.act_stabilityMass
#print axioms BridgelandStabLean.GroupAction.AutPair.act_stabilityMass_functor_obj

/-! ## HNPolygon — abelian HN paths and positive-angle support -/

#print axioms CategoryTheory.AbelianHNFiltration.factorObj
#print axioms CategoryTheory.AbelianHNFiltration.hnPolygon_le_of_polygonVertex_isMax
#print axioms CategoryTheory.AbelianHNFiltration.last_le_phase
#print axioms CategoryTheory.AbelianHNFiltration.last_prefix_le_quotient_phase
#print axioms CategoryTheory.AbelianHNFiltration.mass
#print axioms CategoryTheory.AbelianHNFiltration.norm_charge_le_mass
#print axioms CategoryTheory.AbelianHNFiltration.norm_charge_le_polygonLength
#print axioms CategoryTheory.AbelianHNFiltration.phase_last_prefix_le_of_ne_zero_to_semistable
#print axioms CategoryTheory.AbelianHNFiltration.phase_le_first
#print axioms CategoryTheory.AbelianHNFiltration.polygonEdge
#print axioms CategoryTheory.AbelianHNFiltration.polygonEdge_arg
#print axioms CategoryTheory.AbelianHNFiltration.polygonEdge_arg_strictAnti
#print axioms CategoryTheory.AbelianHNFiltration.polygonEdge_mem_upperHalfPlaneUnion
#print axioms CategoryTheory.AbelianHNFiltration.polygonLength
#print axioms CategoryTheory.AbelianHNFiltration.polygonLength_eq_mass
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex_exists_strict_support
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex_exists_strict_support_hnPolygon
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex_last
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex_mem_hnPolygon
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex_succ_sub
#print axioms CategoryTheory.AbelianHNFiltration.polygonVertex_zero
#print axioms CategoryTheory.AbelianHNFiltration.quotientHNFiltration
#print axioms CategoryTheory.AbelianHNFiltration.quotientInfToCokernel
#print axioms CategoryTheory.AbelianHNFiltration.quotientInfToCokernel_mono
#print axioms CategoryTheory.AbelianHNFiltration.quotient_inf_phase_le
#print axioms CategoryTheory.AbelianHNFiltration.semistable_le_chain_of_phase_gt
#print axioms CategoryTheory.AbelianHNFiltration.semistable_phase_le_first
#print axioms CategoryTheory.AbelianHNFiltration.subobjectCharge_exists_strict_support
#print axioms CategoryTheory.AbelianHNFiltration.subobjectCharge_le_of_polygonVertex_isMax
#print axioms CategoryTheory.AbelianHNFiltration.subobject_phase_le_first
#print axioms CategoryTheory.ComplexPolygonalPath.arg_last_edge_le_arg_last_sub_zero
#print axioms CategoryTheory.ComplexPolygonalPath.arg_last_sub_zero_le_arg_first
#print axioms CategoryTheory.ComplexPolygonalPath.arg_unitRay
#print axioms CategoryTheory.ComplexPolygonalPath.crossFunctional
#print axioms CategoryTheory.ComplexPolygonalPath.crossFunctional_apply
#print axioms CategoryTheory.ComplexPolygonalPath.crossFunctional_neg_of_arg_lt
#print axioms CategoryTheory.ComplexPolygonalPath.crossFunctional_pos_of_arg_lt
#print axioms CategoryTheory.ComplexPolygonalPath.exists_strict_support_at_interior
#print axioms CategoryTheory.ComplexPolygonalPath.length
#print axioms CategoryTheory.ComplexPolygonalPath.norm_last_sub_zero_le_length
#print axioms CategoryTheory.ComplexPolygonalPath.sum_edges_eq_last_sub_zero
#print axioms CategoryTheory.ComplexPolygonalPath.unitRay
#print axioms CategoryTheory.ComplexPolygonalPath.unitRay_im
#print axioms CategoryTheory.ComplexPolygonalPath.unitRay_mem_upperHalfPlaneUnion
#print axioms CategoryTheory.ComplexPolygonalPath.unitRay_re
#print axioms CategoryTheory.StabilityFunction.hnPolygon
#print axioms CategoryTheory.StabilityFunction.hnPolygon_mono
#print axioms CategoryTheory.StabilityFunction.subobjectCharge_mem_hnPolygon

/-! ## ConvexPolygonPerimeter — finite perimeter and short-exact mass bounds -/

#print axioms CategoryTheory.AbelianHNFiltration.mass_eq_mass
#print axioms CategoryTheory.AbelianHNFiltration.mass_le_add_norm_cokernel_of_mono
#print axioms CategoryTheory.AbelianHNFiltration.mass_le_add_norm_of_shortExact
#print axioms CategoryTheory.AbelianHNFiltration.polygonLength_le_add_norm_charge_sub_of_mono
#print axioms CategoryTheory.AbelianHNFiltration.polygonLength_le_of_vertexHull_subset
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength_comp_monotone_le
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength_cons_cons
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength_mono_sublist
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength_nil
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength_ofFn_eq_length
#print axioms CategoryTheory.ComplexPolygonalPath.chainLength_singleton
#print axioms CategoryTheory.ComplexPolygonalPath.closedEdge
#print axioms CategoryTheory.ComplexPolygonalPath.closedLength
#print axioms CategoryTheory.ComplexPolygonalPath.closedLength_comp_monotone_le
#print axioms CategoryTheory.ComplexPolygonalPath.closedLength_eq_length_add_chord
#print axioms CategoryTheory.ComplexPolygonalPath.closedLength_eq_sum_turning
#print axioms CategoryTheory.ComplexPolygonalPath.closedLength_le_of_monotone_support
#print axioms CategoryTheory.ComplexPolygonalPath.closedTangent
#print axioms CategoryTheory.ComplexPolygonalPath.crossMaxIndex
#print axioms CategoryTheory.ComplexPolygonalPath.crossMaxIndex_max
#print axioms CategoryTheory.ComplexPolygonalPath.crossMaxIndex_mono_of_angle_gt
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional_apply
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional_le_norm_mul
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional_sub_left
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional_sub_right
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional_unitDirection_self
#print axioms CategoryTheory.ComplexPolygonalPath.dotFunctional_unitRay_sub
#print axioms CategoryTheory.ComplexPolygonalPath.interiorBisector
#print axioms CategoryTheory.ComplexPolygonalPath.interiorBisector_mem_Ioo
#print axioms CategoryTheory.ComplexPolygonalPath.interiorBisector_strictAnti
#print axioms CategoryTheory.ComplexPolygonalPath.interiorNextEdge
#print axioms CategoryTheory.ComplexPolygonalPath.interiorPrevEdge
#print axioms CategoryTheory.ComplexPolygonalPath.interiorTurnScale
#print axioms CategoryTheory.ComplexPolygonalPath.interiorTurnScale_pos
#print axioms CategoryTheory.ComplexPolygonalPath.last_sub_zero_mem_upperHalfPlaneUnion
#print axioms CategoryTheory.ComplexPolygonalPath.length_le_of_convexHull_subset
#print axioms CategoryTheory.ComplexPolygonalPath.length_snoc
#print axioms CategoryTheory.ComplexPolygonalPath.norm_unitDirection_le_one
#print axioms CategoryTheory.ComplexPolygonalPath.sub_mem_upperHalfPlaneUnion_of_lt
#print axioms CategoryTheory.ComplexPolygonalPath.turningFunctional
#print axioms CategoryTheory.ComplexPolygonalPath.turningFunctional_interior_eq_cross
#print axioms CategoryTheory.ComplexPolygonalPath.unitDirection
#print axioms CategoryTheory.ComplexPolygonalPath.unitDirection_eq_unitRay_arg

/-! ## StabilityDistance — the three-coordinate extended pseudodistance -/

#print axioms CategoryTheory.Triangulated.logMassDist
#print axioms CategoryTheory.Triangulated.logMassDist_self
#print axioms CategoryTheory.Triangulated.logMassDist_comm
#print axioms CategoryTheory.Triangulated.logMassDist_triangle
#print axioms CategoryTheory.Triangulated.logMassDist_eq_of_ne_top
#print axioms CategoryTheory.Triangulated.phiPlusDist
#print axioms CategoryTheory.Triangulated.phiMinusDist
#print axioms CategoryTheory.Triangulated.massDist
#print axioms CategoryTheory.Triangulated.stabilityDistTerm
#print axioms CategoryTheory.Triangulated.stabilityDist
#print axioms CategoryTheory.Triangulated.phiPlusDist_self
#print axioms CategoryTheory.Triangulated.phiMinusDist_self
#print axioms CategoryTheory.Triangulated.massDist_self
#print axioms CategoryTheory.Triangulated.phiPlusDist_comm
#print axioms CategoryTheory.Triangulated.phiMinusDist_comm
#print axioms CategoryTheory.Triangulated.massDist_comm
#print axioms CategoryTheory.Triangulated.phiPlusDist_triangle
#print axioms CategoryTheory.Triangulated.phiMinusDist_triangle
#print axioms CategoryTheory.Triangulated.massDist_triangle
#print axioms CategoryTheory.Triangulated.massDist_eq_abs_log
#print axioms CategoryTheory.Triangulated.massDist_eq_abs_log_ratio
#print axioms CategoryTheory.Triangulated.stabilityDist_self
#print axioms CategoryTheory.Triangulated.stabilityDist_comm
#print axioms CategoryTheory.Triangulated.stabilityDist_triangle
#print axioms CategoryTheory.Triangulated.slicingDist_le_stabilityDist
#print axioms CategoryTheory.Triangulated.stabilityDistTerm_le_stabilityDist
#print axioms CategoryTheory.Triangulated.phiPlusDist_le_stabilityDist
#print axioms CategoryTheory.Triangulated.phiMinusDist_le_stabilityDist
#print axioms CategoryTheory.Triangulated.massDist_le_stabilityDist

/-! ## StabilityDistanceSeparation — identity of indiscernibles -/

#print axioms CategoryTheory.Triangulated.stabilityDistTerm_eq_zero_of_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_norm_charge
#print axioms CategoryTheory.Triangulated.phiPlus_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.phiMinus_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.slicing_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.charge_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.charge_comp_eq_of_stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityDist_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityDist_eq_zero_iff
#print axioms CategoryTheory.Triangulated.stabilityConditionDist_eq_zero
#print axioms CategoryTheory.Triangulated.stabilityConditionDist_eq_zero_iff

/-! ## StabilityDistanceTopology — Proposition 8.1 topology comparison -/

#print axioms CategoryTheory.Triangulated.abs_phiPlus_sub_lt_of_stabilityDist
#print axioms CategoryTheory.Triangulated.abs_phiMinus_sub_lt_of_stabilityDist
#print axioms CategoryTheory.Triangulated.abs_log_mass_ratio_lt_of_stabilityDist
#print axioms CategoryTheory.Triangulated.exp_neg_lt_mass_ratio_and_lt_exp_of_stabilityDist
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_lt_exp_mul_of_stabilityDist
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_lt_exp_mul_of_stabilityDist'
#print axioms CategoryTheory.Triangulated.norm_phaseExp_sub_phaseExp_le
#print axioms CategoryTheory.Triangulated.norm_sum_phaseExp_sub_centralRay_le
#print axioms CategoryTheory.Triangulated.charge_eq_stabilityMass_mul_phaseExp
#print axioms CategoryTheory.Triangulated.norm_charge_sub_mass_phaseExp_le_of_stabilityDist
#print axioms CategoryTheory.Triangulated.cos_mul_stabilityMass_le_norm_charge_of_width
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_le_of_mem_basisNhd_of_semistable
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_le_of_mem_basisNhd_of_semistable'
#print axioms CategoryTheory.Triangulated.StabilityMassTriangleInequality
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_congr
#print axioms CategoryTheory.Triangulated.stabilityMass_chain_le_partial_sum
#print axioms CategoryTheory.Triangulated.stabilityMass_le_sum_postnikov_factors
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_le_of_mem_basisNhd
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_le_of_mem_basisNhd'
#print axioms CategoryTheory.Triangulated.basisForwardMassFactor
#print axioms CategoryTheory.Triangulated.basisReverseMassFactor
#print axioms CategoryTheory.Triangulated.basisMassControl
#print axioms CategoryTheory.Triangulated.basisForwardMassFactor_zero
#print axioms CategoryTheory.Triangulated.basisReverseMassFactor_zero
#print axioms CategoryTheory.Triangulated.basisMassControl_zero
#print axioms CategoryTheory.Triangulated.abs_log_mass_ratio_le_of_mem_basisNhd
#print axioms CategoryTheory.Triangulated.exists_basisMassControl_lt
#print axioms CategoryTheory.Triangulated.exists_basisNhd_subset_stabilityDist_ball
#print axioms CategoryTheory.Triangulated.stabilityChargeControl
#print axioms CategoryTheory.Triangulated.stabilityChargeControl_zero
#print axioms CategoryTheory.Triangulated.norm_charge_sub_charge_lt_of_stabilityDist
#print axioms CategoryTheory.Triangulated.stabSeminorm_le_of_stabilityDist_lt
#print axioms CategoryTheory.Triangulated.exists_stabilityChargeControl_lt
#print axioms CategoryTheory.Triangulated.exists_stabilityDist_ball_subset_basisNhd
#print axioms CategoryTheory.Triangulated.nhds_hasBasis_basisNhd
#print axioms CategoryTheory.Triangulated.StabilityDistanceTopologyCompatible
#print axioms CategoryTheory.Triangulated.stabilityDistanceTopologyCompatible_of_mass_triangle
#print axioms CategoryTheory.Triangulated.stabilityPseudoEMetricSpace
#print axioms CategoryTheory.Triangulated.stabilityPseudoEMetricSpace_toTopologicalSpace
#print axioms CategoryTheory.Triangulated.stabilityPseudoEMetricSpace_edist
#print axioms CategoryTheory.Triangulated.stabilityEMetricSpace
#print axioms CategoryTheory.Triangulated.stabilityEMetricSpace_toTopologicalSpace
#print axioms CategoryTheory.Triangulated.stabilityPseudoEMetricSpaceOfMassTriangle
#print axioms CategoryTheory.Triangulated.stabilityEMetricSpaceOfMassTriangle

/-! ## H⁰ exactness bridge — current-main adapter for issue #89

The generic Tilting cohomology functor is homological. This narrow adapter
records its definitional identification with the anchor's
`HeartStabilityData.H0Functor`, transports homologicality without adding a new
global instance, and discharges exactness plus the monic cokernel comparison
for heart-source triangles. `Exact`, not `ShortExact`, is the valid conclusion.
No mass theorem or source-faithfulness claim is made here. -/

#print axioms CategoryTheory.Triangulated.HeartStabilityData.H0FunctorIsoOriginalHeartCohFunctor
#print axioms CategoryTheory.Triangulated.HeartStabilityData.H0Functor_isHomological_unconditional
#print axioms CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_isHomological_unconditional
#print axioms CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0Complex
#print axioms CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0Complex_exact_iff_mono_cokernelDesc
#print axioms CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0Complex_exact
#print axioms CategoryTheory.Triangulated.HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc_unconditional
#print axioms CategoryTheory.Triangulated.HeartStabilityData.isIso_heartSourceH0primeShortComplex_cokernelDesc_unconditional
#print axioms CategoryTheory.Triangulated.HeartStabilityData.mono_H0primeFunctor_map_mor₂_of_obj₁_isGE_one
#print axioms CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0Complex_exact_of_H0Functor_isHomological
#print axioms CategoryTheory.Triangulated.HeartStabilityData.isIso_H0primeFunctor_map_truncLEι
#print axioms CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_of_isLE_comp
#print axioms CategoryTheory.Triangulated.HeartStabilityData.H0primeObjIsoTruncGEOfIsLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isLE_zero
#print axioms CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_map_distinguished_exact_of_isLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_of_isLE_comp_assoc
#print axioms CategoryTheory.Triangulated.HeartStabilityData.heartSourceH0Complex_exact_of_isHomological
#print axioms CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isLE_naturality_assoc
#print axioms CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_of_isLE_fromH0primeHom_of_isLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc
#print axioms CategoryTheory.Triangulated.HeartStabilityData.mono_heartSourceH0primeShortComplex_cokernelDesc_of_H0Functor
#print axioms CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.H0primeFunctor_map_distinguished_exact_of_obj₁_isLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.toH0primeHom_of_isLE
#print axioms CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isLE_naturality
#print axioms CategoryTheory.Triangulated.HeartStabilityData.fromH0primeHom_of_isLE_toH0primeHom_of_isLE

/-! ## The octahedral reduction of the mass triangle inequality -/

#print axioms CategoryTheory.Triangulated.stabilityMass_eq_ofReal_norm_charge
#print axioms CategoryTheory.Triangulated.exists_headTail_stabilityMass
#print axioms CategoryTheory.Triangulated.HNFiltration.exists_headTail_mass
#print axioms CategoryTheory.Triangulated.StabilityMassSemistableLeftTriangleInequality
#print axioms CategoryTheory.Triangulated.stabilityMassTriangleInequality_of_semistable_obj₁
#print axioms CategoryTheory.Triangulated.stabilityMassSemistableLeftTriangleInequality
#print axioms CategoryTheory.Triangulated.stabilityMassTriangleInequality
#print axioms CategoryTheory.Triangulated.stabilityDistanceTopologyCompatible
#print axioms CategoryTheory.Triangulated.stabilityMassBoundaryHeartInequality
#print axioms CategoryTheory.Triangulated.stabilityMass_H0FunctorShift_negOne_zero_triangle_le_of_obj₁_phase_one
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_shift_one
#print axioms CategoryTheory.Triangulated.HNFiltration.unrotateStability
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_appendFactor
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_triangle_eq_add_of_same_phase
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.charge_triangle
#print axioms CategoryTheory.Triangulated.StabilityMassBoundaryHeartInequality
#print axioms CategoryTheory.Triangulated.stabilityMass_liftedRotation
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observable_charge
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart
#print axioms CategoryTheory.Triangulated.phaseOne_endpoints_of_heart_shortExact
#print axioms CategoryTheory.Triangulated.stabilityMass_shift_neg_one
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_rotateStability
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_unrotateStability
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observable
#print axioms CategoryTheory.Triangulated.StabilityMassHeartShortExactInequality
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.mem_slicing_of_heart_isSemistable
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_obj₁_phase_one_of_amplitude
#print axioms CategoryTheory.Triangulated.HNFiltration.rotateStability
#print axioms CategoryTheory.Triangulated.stabilityMass_heart_shortExact_le_of_obj₂_semistable
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_Zobj
#print axioms CategoryTheory.Triangulated.heartShortExact_exists_distinguished_triangle
#print axioms CategoryTheory.Triangulated.norm_charge_le_stabilityMass_toReal
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_shift_neg_one
#print axioms CategoryTheory.Triangulated.norm_actC_rotationGLPos
#print axioms CategoryTheory.Triangulated.HNFiltration.mass_appendFactor
#print axioms CategoryTheory.Triangulated.actC_rotationGLPos
#print axioms CategoryTheory.Triangulated.stabilityMassHeartShortExactInequality_of_triangle
#print axioms CategoryTheory.Triangulated.stabilityMass_heartCoh_negOne_zero_triangle_le_of_obj₁_phase_one
#print axioms CategoryTheory.Triangulated.stabilityMass_shift_one
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_obj₂_semistable
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_triangle_eq_add_of_gtProp_leProp
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_heartCoh_negOne_add_zero
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_obj₁_phase_one
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_triangle_eq_add_of_hn_separated
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_hasHN
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.mass_eq_stabilityMass_toReal
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_obj₁_phase_one_of_obj₃_le_one
#print axioms CategoryTheory.Triangulated.stabilityMass_triangle_le_of_same_phase
#print axioms CategoryTheory.Triangulated.stabilityMass_heart_shortExact_le_of_same_phase
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observable_slicing

/-! ## AutFullIsometry — invariance of all three coordinates -/

#print axioms BridgelandStabLean.GroupAction.AutPair.act_phiPlusDist
#print axioms BridgelandStabLean.GroupAction.AutPair.act_phiMinusDist
#print axioms BridgelandStabLean.GroupAction.AutPair.act_massDist
#print axioms BridgelandStabLean.GroupAction.AutPair.act_stabilityDistTerm
#print axioms BridgelandStabLean.GroupAction.AutPair.act_stabilityDistTerm_functor_obj
#print axioms BridgelandStabLean.GroupAction.AutPair.act_stabilityDist
#print axioms CategoryTheory.Triangulated.AutPairQuot_smul_stabilityDist

/-! ## Group-law spot checks

`#print axioms` audits the proof term; these check the instance actually
computes the intended composition rather than some other group structure that
happens to typecheck. Both are `rfl`, so a wrong `mul` would fail here.
-/

section SpotChecks

open GroupAction

example (f g : NormalizedShift) (φ : ℝ) :
    (f * g).toOrderIso φ = f.toOrderIso (g.toOrderIso φ) := rfl

example (φ : ℝ) : (1 : NormalizedShift).toOrderIso φ = φ := rfl

example (f : NormalizedShift) (φ : ℝ) :
    (f⁻¹ * f).toOrderIso φ = φ := by simp

/-- `GLTilde` multiplication must compose the shift factors in the SAME order
as `NormalizedShift` does. An order flip here would typecheck and be wrong. -/
example (x y : GLTilde) (φ : ℝ) :
    (x * y).shift.toOrderIso φ = x.shift.toOrderIso (y.shift.toOrderIso φ) :=
  rfl

/-- The projections agree with the field accessors. -/
example (x : GLTilde) : GLTilde.toMatHom x = x.mat := rfl
example (x : GLTilde) : GLTilde.toShiftHom x = x.shift := rfl

/-- The identity really is a compatible pair, so `GLTilde` is inhabited and
the group is not vacuous. -/
example : (1 : GLTilde).mat = 1 ∧ (1 : GLTilde).shift = 1 := ⟨rfl, rfl⟩

/-- Phase `+1` is the antipodal ray — the shift functor `[1]`. -/
example (φ : ℝ) : rayVec (φ + 1) = -rayVec φ := rayVec_add_one φ

end SpotChecks

/-! ## Step-3a convention checks

The slicing action relabels by `f⁻¹`, not `f`. With `f` the definition still
typechecks and `mul_smul` fails, so the `MulAction` laws below are the real
guard; these `example`s pin the surface convention that goes with them.
-/

section SlicingChecks

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated GroupAction

-- Declared explicitly. `lake env lean` does not apply the package's
-- `[leanOptions]`, so under a bare `lean` invocation `u` and `v` were
-- auto-bound and this section elaborated by accident. Under the repo's actual
-- settings (`autoImplicit = false`) it did not compile at all -- which is
-- exactly the rot that covering this file with a `lean_lib` is meant to catch.
universe u v

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

example (f : NormalizedShift) (s : Slicing C) (φ : ℝ) :
    (f • s).P φ = s.P (f⁻¹.toOrderIso φ) := rfl

/-- `GLTilde` acts through its shift factor only — the matrix factor is not
consulted. -/
example (x : GLTilde) (s : Slicing C) (φ : ℝ) :
    (x • s).P φ = (x.shift • s).P φ := rfl

/-! Step 3b: both factors act, each on its own component. -/

variable {Λ : Type*} [AddCommGroup Λ] (v : K₀ C →+ Λ)

example (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) :
    (x • σ).slicing = x • σ.slicing := rfl

example (x : GLTilde) (σ : PreStabilityCondition.WithClassMap C v) (a : Λ) :
    (x • σ).Z a = actC x.mat (σ.Z a) := rfl

/-! Step 3c: the action reaches full stability conditions. -/

section StabChecks

variable [IsTriangulated C]

example (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) :
    (x • σ).slicing = x • σ.slicing := rfl

example (x : GLTilde) (σ : StabilityCondition.WithClassMap C v) (a : Λ) :
    (x • σ).Z a = actC x.mat (σ.Z a) := rfl

end StabChecks

/-! The `Aut` half, now a `MulAction`.

Both components reverse under `*`, and they reverse in *opposite* syntactic
directions — the auto-equivalences compose contravariantly, the lattice maps
covariantly. Getting one of the two backwards typechecks and is wrong, so both
are pinned by `rfl` here. -/

section AutPairChecks

variable [IsTriangulated C]

/-- `a * b` applies `b`'s lattice automorphism FIRST. -/
example (a b : AutPair v) (σ : StabilityCondition.WithClassMap C v) (x : Λ) :
    ((AutPairQuot.mk a * AutPairQuot.mk b) • σ).Z x = σ.Z (b.lam (a.lam x)) := rfl

/-- ...and correspondingly applies `a`'s inverse equivalence first on objects. -/
example (a b : AutPair v) (σ : StabilityCondition.WithClassMap C v) (φ : ℝ) (X : C) :
    ((AutPairQuot.mk a * AutPairQuot.mk b) • σ).slicing.P φ X
      = σ.slicing.P φ (b.Φ.e.inverse.obj (a.Φ.e.inverse.obj X)) := rfl

/-- The identity acts as the identity, definitionally on both components. -/
example (σ : StabilityCondition.WithClassMap C v) (x : Λ) :
    ((1 : AutPairQuot v) • σ).Z x = σ.Z x := rfl

/-- The forgetful map really does forget only the lattice datum. -/
example (a : AutPair v) : AutPairQuot.toAutQuot (AutPairQuot.mk a) = AutQuot.mk a.Φ := rfl

/-- The quotient relation is normalized: only the forward functor is part of
the relation; inverse isomorphisms are derived from adjoint uniqueness. -/
example (a b : AutPair v) :
    a ≈ b ↔ (Nonempty (a.Φ.e.functor ≅ b.Φ.e.functor) ∧ a.lam = b.lam) := Iff.rfl

/-- The two §8 factors commute on stability conditions. -/
example (x : GLTilde) (a : AutPair v) (σ : StabilityCondition.WithClassMap C v) :
    x • (AutPairQuot.mk a • σ) = AutPairQuot.mk a • (x • σ) :=
  gltilde_autPair_smul_comm x a σ

/-- All three fixed-element continuity instances are found by typeclass search. -/
example (x : GLTilde) :
    Continuous fun σ : StabilityCondition.WithClassMap C v ↦ x • σ :=
  continuous_const_smul x

example (q : AutPairQuot v) :
    Continuous fun σ : StabilityCondition.WithClassMap C v ↦ q • σ :=
  continuous_const_smul q

example (p : GLTilde × AutPairQuot v) :
    Continuous fun σ : StabilityCondition.WithClassMap C v ↦ p • σ :=
  continuous_const_smul p

/-- The corresponding joint-continuity instances are also available. -/
example : Continuous fun p : GLTilde × StabilityCondition.WithClassMap C v ↦
    p.1 • p.2 :=
  continuous_smul

example : Continuous fun p : AutPairQuot v × StabilityCondition.WithClassMap C v ↦
    p.1 • p.2 :=
  continuous_smul

example : Continuous fun p : (GLTilde × AutPairQuot v) ×
    StabilityCondition.WithClassMap C v ↦ p.1 • p.2 :=
  continuous_smul

end AutPairChecks

end SlicingChecks

/-! ## Families lane -- abstract Definition 20.5/21.15 interfaces -/

#print axioms StabilityFamilies.ChargeProbe
#print axioms StabilityFamilies.ChargeProbe.IsLocallyConstant
#print axioms StabilityFamilies.UniversallyLocallyConstantCharge
#print axioms StabilityFamilies.ChargeProbe.constant
#print axioms StabilityFamilies.ChargeProbe.constant_isLocallyConstant
#print axioms StabilityFamilies.universallyLocallyConstantCharge_constant
#print axioms StabilityFamilies.OpenLocusProbe
#print axioms StabilityFamilies.OpenLocusProbe.IsOpen
#print axioms StabilityFamilies.UniversalOpenness
#print axioms StabilityFamilies.OpenLocusProbe.full
#print axioms StabilityFamilies.OpenLocusProbe.full_isOpen
#print axioms StabilityFamilies.universalOpenness_full
#print axioms StabilityFamilies.GenericSemistabilityProbe
#print axioms StabilityFamilies.GenericSemistabilityProbe.IsGenericallyOpen
#print axioms StabilityFamilies.UniversalGenericOpenness
#print axioms StabilityFamilies.GenericSemistabilityProbe.full
#print axioms StabilityFamilies.GenericSemistabilityProbe.full_isGenericallyOpen
#print axioms StabilityFamilies.universalGenericOpenness_full
#print axioms StabilityFamilies.DedekindHNProblem
#print axioms StabilityFamilies.IntegratesAfterDedekindBaseChange
#print axioms StabilityFamilies.DedekindHNProblem.constant
#print axioms StabilityFamilies.integratesAfterDedekindBaseChange_constant
#print axioms StabilityFamilies.WeakDedekindHNProblem
#print axioms StabilityFamilies.WeakIntegratesAfterDedekindBaseChange
#print axioms StabilityFamilies.WeakDedekindHNProblem.constant
#print axioms StabilityFamilies.weakIntegratesAfterDedekindBaseChange_constant
#print axioms StabilityFamilies.BoundednessProblem
#print axioms StabilityFamilies.UniversalBoundedness
#print axioms StabilityFamilies.BoundednessProblem.trivial
#print axioms StabilityFamilies.universalBoundedness_trivial
#print axioms StabilityFamilies.OrdinaryDefinition20_5Conditions
#print axioms StabilityFamilies.WeakDefinition20_5Conditions
#print axioms StabilityFamilies.OrdinaryStabilityInFamiliesData
#print axioms StabilityFamilies.OrdinaryStabilityInFamiliesData.punit
#print axioms StabilityFamilies.ordinary_punit_locallyConstantCharge
#print axioms StabilityFamilies.HasGaussianRationalValues
#print axioms StabilityFamilies.hasGaussianRationalValues_zero
#print axioms StabilityFamilies.WeakChargeProbe
#print axioms StabilityFamilies.WeakChargeProbe.toChargeProbe
#print axioms StabilityFamilies.WeakChargeProbe.constant
#print axioms StabilityFamilies.WeakChargeProbe.constant_isLocallyConstant
#print axioms StabilityFamilies.WeakSemistabilityProbe
#print axioms StabilityFamilies.WeakSemistabilityProbe.toGenericProbe
#print axioms StabilityFamilies.WeakSemistabilityProbe.constant
#print axioms StabilityFamilies.WeakSemistabilityProbe.constant_isGenericallyOpen
#print axioms StabilityFamilies.WeakDefinition20_5ClauseZero
#print axioms StabilityFamilies.WeakDefinition20_5ClauseZero.reindex
#print axioms StabilityFamilies.weakDefinition20_5ClauseZero_constant
#print axioms StabilityFamilies.WeakQuotientQuadraticSupportData
#print axioms StabilityFamilies.WeakQuotientQuadraticSupportData.constant
#print axioms StabilityFamilies.quotientUniformQuadraticSupportData_reindex
#print axioms StabilityFamilies.WeakStabilityInFamiliesData
#print axioms StabilityFamilies.WeakStabilityInFamiliesData.constant
#print axioms StabilityFamilies.WeakStabilityInFamiliesData.punit
#print axioms StabilityFamilies.Theorem22_2SourceClauses
#print axioms StabilityFamilies.Theorem22_2DependencyContract
#print axioms StabilityFamilies.Theorem22_2DependencyContract.hasSourceClauses
