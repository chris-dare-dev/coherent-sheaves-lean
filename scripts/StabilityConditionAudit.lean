/-
Axiom + sorry audit over a HAND-MAINTAINED LIST of this project's declarations.

Run: `lake env lean scripts/StabilityConditionAudit.lean` (to read the output), or
`lake build StabilityConditionAudit` (to check it still elaborates).

Part of the library build since 2026-08-04: a `lean_lib` with
`srcDir = "scripts"`. Removed from `defaultTargets` on 2026-08-06 -- this file
does `import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition`, so it sits downstream of every module and was
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
lake build && lake env lean scripts/StabilityConditionCensus.lean
```

**REVISED AGAIN 2026-08-07 (later), and the correction is the useful part.**
The revision below reported a real gap of **59**. The true figure was **29**.
The other 30 were compiler-generated names the sweep did not recognise --
`<Struct>.ctorIdx`, `<Struct>.mk.inj`, `<def>.congr_simp`, and generated
`ext_iff`/`ext'_iff` companions of `@[ext]` theorems. Each family was then grepped for in
`DerivedAlgGeo/CategoryTheory/Triangulated/StabilityCondition/` and occurs there **zero** times, so none is a declaration
anyone wrote or could list. A later census correction added the likewise
source-absent `hcongr_*` family; `scripts/StabilityConditionCensus.lean` now filters all six.

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

**THE GAP IS NOW ZERO, re-measured after the literal source-independence
cutover on 2026-08-14.** Every
public declaration in this library that is not a structure field projection is
named below. Be precise about what that does and does not mean -- three of the
four qualifications in this comment are unaffected by it:

* it does NOT cover the **132 private** declarations, which remain structurally
  unlistable;
* it does NOT make this file a gate by itself -- `#print axioms` still exits 0
  on `[sorryAx]`; CI's output checker and environment emitter supply the gate;
* it does NOT make the zero figure self-explanatory. The broader completeness
  ratchet now rejects an unlisted public declaration, but zero in the narrower
  authored/non-projection census is still a measurement that must be rerun.

* It issues **2347** audit commands. The environment holds **2718** authored
  declarations under the stability-condition modules under `DerivedAlgGeo`; the declarations outside the
  substantive hand audit are precisely the private declarations and structure
  projections. Seven projections are additionally listed because the newer
  repository-wide completeness ratchet deliberately uses a broader census.
  ("Authored" excludes constructors,
  recursors, `casesOn`, matchers, equation lemmas, internal names, and the six
  generated families named above -- none of which anybody writes or could
  list.)
* **132 are `private`** -- 115 of them theorems -- and are *structurally*
  unlistable: Lean mangles a private name to `_private.<Module>.<n>.<Name>`,
  which cannot be written as a short name from an importing module. The
  instruction below cannot be followed for them, and no amount of diligence
  changes that.
* **251 are structure field projections** emitted by the `structure` command.
  These are not a coverage gap in any useful sense; listing them would be noise.
  Seven are nevertheless named below to keep the broader CI completeness
  ratchet from worsening. They are called out because a census that does not
  separate them reports a shortfall five times the real one.
* That leaves **0**. The literal-independence audit found 194 public names that
  had accumulated outside this list; all 194 were added on 2026-08-14.
* **The residue was dominated by one syntactic shape.** Five of the first 20
  and **seven of the last 10** are `@[simp] theorem` on ONE line, which a regex
  anchored on `^theorem` cannot see. That is 12 of the 30, and it is why the
  count is taken from the environment rather than from source text: the names
  hardest to notice by eye were, systematically, the ones left out.
* `scripts/check_audit.py` still checks only that this file's commanded output
  is complete and untruncated. The complementary CI gate
  `scripts/check_audit_complete.py` now enumerates public declarations and
  rejects growth beyond its recorded legacy ceiling. It is a ratchet rather
  than a zero-gap assertion because its intentionally broader census includes
  generated projections; `scripts/StabilityConditionCensus.lean` remains the precise measurement
  for the authored, non-projection claim above.
* **612 of the distinct gated declarations are not theorems** (68 `structure`, 544 other
  constructions).
  For a `def`, `#print axioms` reports the axiom closure of a CONSTRUCTION and
  asserts nothing about any proposition. In particular
  `CategoryTheory.Triangulated.StabilityMassTriangleInequality` appears below
formatted identically to the **1723** real theorems, but it is a `def ... :
  Prop` -- its clean line means the definition is axiom-clean, NOT that the
  proposition holds.

The environment-wide emitter (`exe/Emit.lean`) sweeps `Environment.constants`
and therefore does see the private and unlisted names. That, not this file, is
the gate that closes the hole.

**On Windows the emitter cannot be linked at all** -- `supportInterpreter`
pushes the PE export table past 65535 symbols, as `exe/Emit.lean` records -- so
on that platform this file is the only axiom check available. That is *not* a
reason to believe the environment is unswept there: `scripts/StabilityConditionCensus.lean` reads
the same module data through `lake env lean`, which links nothing, and so runs
where the executable cannot. Use it to size the gap; use the emitter, in CI, to
gate it.

Adding a declaration to the library means adding it here. This file is not
derived from the source tree, so it can silently fall behind; `#print axioms`
on a name that no longer exists is a hard error, but a name never added is
invisible.
-/
import DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition
import DerivedAlgGeo.LinearAlgebra

open CategoryTheory.Triangulated

/-! ## Owner-controlled Bridgeland foundation (#226) -/

#print axioms CategoryTheory.Triangulated.PostnikovTower
#print axioms CategoryTheory.Triangulated.PostnikovTower.length
#print axioms CategoryTheory.Triangulated.PostnikovTower.factor
#print axioms CategoryTheory.Triangulated.PostnikovTower.factors
#print axioms CategoryTheory.Triangulated.ExtensionClosure
#print axioms CategoryTheory.Triangulated.ExtensionClosure.mono
#print axioms CategoryTheory.Triangulated.ExtensionClosure.hom_eq_zero
#print axioms CategoryTheory.Triangulated.ExtensionClosure.ofIso
#print axioms CategoryTheory.Triangulated.ExtensionClosure.ofPostnikovTower
#print axioms CategoryTheory.Triangulated.ExtensionClosure.instIsClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.ExtensionClosure.le_of_closed
#print axioms CategoryTheory.Triangulated.HNFiltration
#print axioms CategoryTheory.Triangulated.Slicing
#print axioms CategoryTheory.Triangulated.Slicing.ext
#print axioms CategoryTheory.Triangulated.Slicing.ext_iff
#print axioms CategoryTheory.Triangulated.Slicing.zero_mem_of_isZero
#print axioms CategoryTheory.Triangulated.Slicing.shift
#print axioms CategoryTheory.Triangulated.Slicing.unshift

/-! ## Owner-controlled Grothendieck and pre-stability foundation (#228) -/

#print axioms CategoryTheory.Triangulated.GrothendieckPresentation
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.relationSubgroup
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.Group
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.instAddCommGroupGroup
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.of
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.of_relation
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.IsAdditive
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.lift
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.lift_of
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.hom_ext
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.hom_ext_iff
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.induction_on
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.isAdditive_of
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.map
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.map_of
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.IsAdditive.of_relationMap
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.map_id
#print axioms CategoryTheory.Triangulated.GrothendieckPresentation.map_comp
#print axioms CategoryTheory.Triangulated.triangulatedPresentation
#print axioms CategoryTheory.Triangulated.K₀
#print axioms CategoryTheory.Triangulated.K₀.of
#print axioms CategoryTheory.Triangulated.K₀.of_triangle
#print axioms CategoryTheory.Triangulated.K₀.of_zero
#print axioms CategoryTheory.Triangulated.K₀.of_iso
#print axioms CategoryTheory.Triangulated.K₀.of_isZero
#print axioms CategoryTheory.Triangulated.K₀.of_shift_one
#print axioms CategoryTheory.Triangulated.K₀.of_shift_neg_one
#print axioms CategoryTheory.Triangulated.IsTriangleAdditive
#print axioms CategoryTheory.Triangulated.instIsAdditiveSubtypeTriangleMemSetDistinguishedTrianglesTriangulatedPresentationOfIsTriangleAdditive
#print axioms CategoryTheory.Triangulated.K₀.lift
#print axioms CategoryTheory.Triangulated.K₀.lift_of
#print axioms CategoryTheory.Triangulated.K₀.hom_ext
#print axioms CategoryTheory.Triangulated.K₀.hom_ext_iff
#print axioms CategoryTheory.Triangulated.K₀.of_postnikovTower_eq_sum
#print axioms CategoryTheory.Triangulated.classOf
#print axioms CategoryTheory.Triangulated.classOf_id
#print axioms CategoryTheory.Triangulated.classOf_isZero
#print axioms CategoryTheory.Triangulated.classOf_triangle
#print axioms CategoryTheory.Triangulated.classOf_iso
#print axioms CategoryTheory.Triangulated.classOf_shift_one
#print axioms CategoryTheory.Triangulated.classOf_shift_neg_one
#print axioms CategoryTheory.Triangulated.classOf_postnikovTower_eq_sum
#print axioms CategoryTheory.Triangulated.K₀.isTriangleAdditive_map
#print axioms CategoryTheory.Triangulated.K₀.map
#print axioms CategoryTheory.Triangulated.K₀.map_of
#print axioms CategoryTheory.Triangulated.K₀.map_id
#print axioms CategoryTheory.Triangulated.K₀.map_comp
#print axioms CategoryTheory.Triangulated.K₀.map_congr
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge_def
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.compat
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge_isZero
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge_congr
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.charge_postnikovTower_eq_sum
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.ext
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.ext_iff
#print axioms CategoryTheory.Triangulated.PreStabilityCondition
#print axioms CategoryTheory.Triangulated.preStabilityCondition_compat_apply

/-! ## Owner-controlled local finiteness and stability conditions (#229) -/

#print axioms CategoryTheory.Triangulated.Slicing.intervalProp
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.ι
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_of_isZero
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_containsZero
#print axioms CategoryTheory.Triangulated.Slicing.IsAdmissibleSubobject
#print axioms CategoryTheory.Triangulated.Slicing.AdmissibleSubobject
#print axioms CategoryTheory.Triangulated.Slicing.IsAdmissiblyArtinian
#print axioms CategoryTheory.Triangulated.Slicing.IsAdmissiblyNoetherian
#print axioms CategoryTheory.Triangulated.Slicing.IsFiniteLength
#print axioms CategoryTheory.Triangulated.admissibleSubobjectOrderIso
#print axioms CategoryTheory.Triangulated.admissibleSubobjectOrderIso_wellFoundedLT_iff
#print axioms CategoryTheory.Triangulated.admissibleSubobjectOrderIso_wellFoundedGT_iff
#print axioms CategoryTheory.Triangulated.Slicing.IsLocallyFinite
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ext
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.ext_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition
#print axioms CategoryTheory.Triangulated.stabilityCondition_compat_apply

/-! ## Owner slicing phase bounds and filtration operations (#231) -/

#print axioms CategoryTheory.Triangulated.Slicing.shift_nat
#print axioms CategoryTheory.Triangulated.Slicing.unshift_nat
#print axioms CategoryTheory.Triangulated.Slicing.shift_int
#print axioms CategoryTheory.Triangulated.HNFiltration.phiPlus
#print axioms CategoryTheory.Triangulated.HNFiltration.phiMinus
#print axioms CategoryTheory.Triangulated.HNFiltration.phase_mem_range
#print axioms CategoryTheory.Triangulated.HNFiltration.phiMinus_le_phiPlus
#print axioms CategoryTheory.Triangulated.HNFiltration.ofIso
#print axioms CategoryTheory.Triangulated.Slicing.leProp
#print axioms CategoryTheory.Triangulated.Slicing.gtProp
#print axioms CategoryTheory.Triangulated.Slicing.ltProp
#print axioms CategoryTheory.Triangulated.Slicing.geProp
#print axioms CategoryTheory.Triangulated.Slicing.leProp_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.Slicing.gtProp_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.Slicing.ltProp_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.Slicing.geProp_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.Slicing.leProp_of_isZero
#print axioms CategoryTheory.Triangulated.Slicing.gtProp_of_isZero
#print axioms CategoryTheory.Triangulated.Slicing.ltProp_of_isZero
#print axioms CategoryTheory.Triangulated.Slicing.geProp_of_isZero
#print axioms CategoryTheory.Triangulated.Slicing.leProp_mono
#print axioms CategoryTheory.Triangulated.Slicing.gtProp_anti
#print axioms CategoryTheory.Triangulated.Slicing.ltProp_mono
#print axioms CategoryTheory.Triangulated.Slicing.geProp_anti
#print axioms CategoryTheory.Triangulated.Slicing.leProp_of_ltProp
#print axioms CategoryTheory.Triangulated.Slicing.geProp_of_gtProp
#print axioms CategoryTheory.Triangulated.Slicing.ltProp_of_intervalProp
#print axioms CategoryTheory.Triangulated.Slicing.gtProp_of_intervalProp
#print axioms CategoryTheory.Triangulated.Slicing.hom_eq_zero_of_phase_gap
#print axioms CategoryTheory.Triangulated.Slicing.intervalHom_eq_zero
#print axioms CategoryTheory.Triangulated.Slicing.leProp_of_triangle
#print axioms CategoryTheory.Triangulated.Slicing.ltProp_of_triangle
#print axioms CategoryTheory.Triangulated.Slicing.gtProp_of_triangle
#print axioms CategoryTheory.Triangulated.Slicing.geProp_of_triangle
#print axioms CategoryTheory.Triangulated.Slicing.exists_cutoff_truncation
#print axioms CategoryTheory.Triangulated.Slicing.exists_cutoff_truncation_in_interval
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_gtProp
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_ge_of_geProp
#print axioms CategoryTheory.Triangulated.Slicing.phiPlus_le_of_leProp
#print axioms CategoryTheory.Triangulated.Slicing.phiPlus_lt_of_ltProp
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_of_gtProp_ltProp
#print axioms CategoryTheory.Triangulated.Slicing.zero_of_gtProp_leProp
#print axioms CategoryTheory.Triangulated.Slicing.zero_of_geProp_ltProp
#print axioms CategoryTheory.Triangulated.HNFiltration.zero
#print axioms CategoryTheory.Triangulated.HNFiltration.single
#print axioms CategoryTheory.Triangulated.HNFiltration.semistable_of_length_one
#print axioms CategoryTheory.Triangulated.HNFiltration.prefix
#print axioms CategoryTheory.Triangulated.HNFiltration.prefix_φ
#print axioms CategoryTheory.Triangulated.HNFiltration.appendFactor
#print axioms CategoryTheory.Triangulated.HNFiltration.appendLengthOne
#print axioms CategoryTheory.Triangulated.HNFiltration.appendLengthOne_phase_bounds
#print axioms CategoryTheory.Triangulated.HNFiltration.ofTriangleThirdZero
#print axioms CategoryTheory.Triangulated.HNFiltration.exists_of_distinguished_triangle
#print axioms CategoryTheory.Triangulated.HNFiltration.exists_of_distinguished_triangle_phase_bounds
#print axioms CategoryTheory.Triangulated.HNFiltration.exists_split_at_cutoff
#print axioms CategoryTheory.Triangulated.Deformation.ThinStrictFiniteLength
#print axioms CategoryTheory.Triangulated.Deformation.ThinStrictFiniteLength.of_finiteLength
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.exists_semistable_strictQuotient_le_phase
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.id_of_semistable
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.epi
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.strict
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.phase_le
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.factor_of_phase_eq
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.precomposeIso
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.of_strictEpi_factor
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.phase_le_of_strictQuotient
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.isSemistable_of_strictQuotient_phase_eq
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.factor_of_strictQuotient_phase_eq
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.comp_of_destabilizing_semistable_subobject
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.exists_strictMDQ
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.kernelSubobject_ne_bot_of_not_semistable
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.kernelSubobject_isLimitKernelFork
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.strictShortExact_kernelSubobject
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.kernelSubobject_ne_top_of_strictEpi_nonzero
#print axioms CategoryTheory.Triangulated.Deformation.Subobject.map_eq_mk_comp
#print axioms CategoryTheory.Triangulated.Deformation.Subobject.mapUnderlyingIso
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.phase_cokernel_kernelSubobject
#print axioms CategoryTheory.Triangulated.Deformation.IsStrictMDQ.phase_lt_of_strictQuotient_of_kernel
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.hn_exists_of_quotientLowerBound
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.hn_exists
#print axioms CategoryTheory.Triangulated.HNFiltration.shift
#print axioms CategoryTheory.Triangulated.HNFiltration.shift_phiPlus
#print axioms CategoryTheory.Triangulated.HNFiltration.shift_phiMinus
#print axioms CategoryTheory.Triangulated.HNFiltration.n_pos
#print axioms CategoryTheory.Triangulated.HNFiltration.exists_nonzero_factor
#print axioms CategoryTheory.Triangulated.HNFiltration.dropFirst
#print axioms CategoryTheory.Triangulated.Slicing.exists_hn_nonzero_first
#print axioms CategoryTheory.Triangulated.HNFiltration.dropLast
#print axioms CategoryTheory.Triangulated.Slicing.exists_hn_nonzero_last
#print axioms CategoryTheory.Triangulated.Slicing.exists_hn_nonzero_boundaries
#print axioms CategoryTheory.Triangulated.HNFiltration.firstFactor_hom_chain_eq_zero
#print axioms CategoryTheory.Triangulated.HNFiltration.firstFactor_isZero_of_hom_eq_zero
#print axioms CategoryTheory.Triangulated.HNFiltration.phiPlus_le_of_firstFactor_nonzero
#print axioms CategoryTheory.Triangulated.HNFiltration.phiPlus_eq_of_firstFactors_nonzero
#print axioms CategoryTheory.Triangulated.HNFiltration.lastFactor_isZero_of_hom_eq_zero
#print axioms CategoryTheory.Triangulated.HNFiltration.phiMinus_le_of_lastFactor_nonzero
#print axioms CategoryTheory.Triangulated.HNFiltration.phiMinus_eq_of_lastFactors_nonzero
#print axioms CategoryTheory.Triangulated.Slicing.phiPlus
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus
#print axioms CategoryTheory.Triangulated.Slicing.phiPlus_eq
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_eq
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_le_phiPlus
#print axioms CategoryTheory.Triangulated.Slicing.phiPlus_eq_of_semistable
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_eq_of_semistable
#print axioms CategoryTheory.Triangulated.Slicing.exists_hn_intrinsic_width
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_mono
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_intersection
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_widen
#print axioms CategoryTheory.Triangulated.Slicing.phiPlus_lt_of_intervalProp
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_intervalProp
#print axioms CategoryTheory.Triangulated.Slicing.phiPlus_gt_of_intervalProp
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_lt_of_intervalProp
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_of_intrinsic_phases
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_iff_intrinsic_phases
#print axioms CategoryTheory.Triangulated.Slicing.intrinsic_phases_mem_interval
#print axioms CategoryTheory.Triangulated.Slicing.gtProp_of_phiMinus_gt
#print axioms CategoryTheory.Triangulated.Slicing.geProp_of_phiMinus_ge
#print axioms CategoryTheory.Triangulated.Slicing.leProp_of_phiPlus_le
#print axioms CategoryTheory.Triangulated.Slicing.ltProp_of_phiPlus_lt
#print axioms CategoryTheory.Triangulated.Slicing.ltProp_of_leProp_of_lt
#print axioms CategoryTheory.Triangulated.Slicing.phiPlus_lt_of_triangle_with_leProp
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_triangle_with_gtProp
#print axioms CategoryTheory.Triangulated.Slicing.first_intervalProp_of_triangle
#print axioms CategoryTheory.Triangulated.HNFiltration.phaseShift
#print axioms CategoryTheory.Triangulated.Slicing.phaseShift
#print axioms CategoryTheory.Triangulated.Slicing.phaseShift_gtProp_zero
#print axioms CategoryTheory.Triangulated.Slicing.phaseShift_gtProp
#print axioms CategoryTheory.Triangulated.Slicing.phaseShift_leProp_zero
#print axioms CategoryTheory.Triangulated.Slicing.phaseShift_leProp
#print axioms CategoryTheory.Triangulated.Slicing.phaseShift_ltProp_zero
#print axioms CategoryTheory.Triangulated.Slicing.phaseShift_ltProp
#print axioms CategoryTheory.Triangulated.Slicing.phaseShift_geProp_zero
#print axioms CategoryTheory.Triangulated.Slicing.phaseShift_geProp
#print axioms CategoryTheory.Triangulated.Slicing.leProp_shift
#print axioms CategoryTheory.Triangulated.Slicing.gtProp_shift
#print axioms CategoryTheory.Triangulated.Slicing.ltProp_shift
#print axioms CategoryTheory.Triangulated.Slicing.geProp_shift
#print axioms CategoryTheory.Triangulated.Slicing.leProp_of_hn
#print axioms CategoryTheory.Triangulated.Slicing.gtProp_of_hn
#print axioms CategoryTheory.Triangulated.Slicing.ltProp_of_hn
#print axioms CategoryTheory.Triangulated.Slicing.geProp_of_hn
#print axioms CategoryTheory.Triangulated.Slicing.leProp_of_semistable
#print axioms CategoryTheory.Triangulated.Slicing.gtProp_of_semistable
#print axioms CategoryTheory.Triangulated.Slicing.HasPhaseTruncations
#print axioms CategoryTheory.Triangulated.Slicing.exists_phase_truncation
#print axioms CategoryTheory.Triangulated.Slicing.hasPhaseTruncations
#print axioms CategoryTheory.Triangulated.Slicing.exists_dual_phase_truncation
#print axioms CategoryTheory.Triangulated.Slicing.exists_upper_boundary_triangle
#print axioms CategoryTheory.Triangulated.Slicing.exists_lower_boundary_triangle
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_of_upper_boundary_triangle
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_of_lower_boundary_triangle
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_of_triangle
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_implies_leftHeart
#print axioms CategoryTheory.Triangulated.Slicing.toDualTStructure
#print axioms CategoryTheory.Triangulated.Slicing.toDualTStructure_heart_iff
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_implies_rightHeart
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_gt_of_triangle_with_geProp
#print axioms CategoryTheory.Triangulated.Slicing.third_intervalProp_of_triangle
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_of_mono_leftHeart
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_of_epi_rightHeart
#print axioms CategoryTheory.Triangulated.Slicing.intervalCat_hasKernel
#print axioms CategoryTheory.Triangulated.Slicing.intervalCat_hasKernels
#print axioms CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernel
#print axioms CategoryTheory.Triangulated.Slicing.intervalCat_hasCokernels
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeartKernelIso
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeartCokernelIso
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeartKernelIso_hom_comp_ι
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeartCokernelIso_π_comp_hom
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.strictMono_of_mono_toRightHeart
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.strictEpi_of_epi_toLeftHeart
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.mono_toRightHeart_of_strictMono
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.epi_toLeftHeart_of_strictEpi
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.comp_strictMono
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.comp_strictEpi
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.strictEpi_of_comp_strictEpi
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_preservesKernel
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_preservesCokernel
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_isClosedUnderBinaryProducts
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_isClosedUnderFiniteProducts
#print axioms CategoryTheory.Triangulated.Slicing.intervalCat_hasFiniteProducts
#print axioms CategoryTheory.Triangulated.Slicing.intervalCat_hasBinaryBiproducts
#print axioms CategoryTheory.Triangulated.Slicing.intervalCat_hasFiniteBiproducts
#print axioms CategoryTheory.Triangulated.Slicing.intervalCat_hasEqualizers
#print axioms CategoryTheory.Triangulated.Slicing.intervalCat_hasCoequalizers
#print axioms CategoryTheory.Triangulated.Slicing.intervalCat_hasPullbacks
#print axioms CategoryTheory.Triangulated.Slicing.intervalCat_hasPushouts
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_preservesFiniteLimits
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_preservesFiniteColimits
#print axioms CategoryTheory.Triangulated.Slicing.intervalCat_quasiAbelian
#print axioms CategoryTheory.Triangulated.IsStrict
#print axioms CategoryTheory.Triangulated.IsStrictMono
#print axioms CategoryTheory.Triangulated.IsStrictEpi
#print axioms CategoryTheory.Triangulated.isStrictEpi_of_isColimitCokernelCofork
#print axioms CategoryTheory.Triangulated.isStrictMono_of_isLimitKernelFork
#print axioms CategoryTheory.Triangulated.IsStrictEpi.isColimitCokernelCofork
#print axioms CategoryTheory.Triangulated.IsStrictMono.isLimitKernelFork
#print axioms CategoryTheory.Triangulated.IsStrictEpi.normalEpi
#print axioms CategoryTheory.Triangulated.IsStrictMono.normalMono
#print axioms CategoryTheory.Triangulated.isStrictMono_of_isIso
#print axioms CategoryTheory.Triangulated.isStrictEpi_of_isIso
#print axioms CategoryTheory.Triangulated.IsStrictEpi.isIso
#print axioms CategoryTheory.Triangulated.IsStrictMono.isIso
#print axioms CategoryTheory.Triangulated.isStrictEpi_of_normalEpi
#print axioms CategoryTheory.Triangulated.isStrictMono_of_normalMono
#print axioms CategoryTheory.Triangulated.IsStrictEpi.regularEpi
#print axioms CategoryTheory.Triangulated.IsStrictEpi.strongEpi
#print axioms CategoryTheory.Triangulated.IsStrictMono.regularMono
#print axioms CategoryTheory.Triangulated.IsStrictMono.strongMono
#print axioms CategoryTheory.Triangulated.isStrictMono_kernel
#print axioms CategoryTheory.Triangulated.isStrictEpi_cokernel
#print axioms CategoryTheory.Triangulated.StrictShortExact
#print axioms CategoryTheory.Triangulated.IsStrictEpi.strictShortExact_kernel
#print axioms CategoryTheory.Triangulated.QuasiAbelian
#print axioms CategoryTheory.Triangulated.isStrict_of_abelian
#print axioms CategoryTheory.Triangulated.isStrictMono_of_mono
#print axioms CategoryTheory.Triangulated.isStrictEpi_of_epi
#print axioms CategoryTheory.Triangulated.strictShortExact_of_shortExact
#print axioms CategoryTheory.Triangulated.IsStrictSubobject
#print axioms CategoryTheory.Triangulated.isStrictSubobject_iff
#print axioms CategoryTheory.Triangulated.StrictSubobject
#print axioms CategoryTheory.Triangulated.isStrictArtinianObject
#print axioms CategoryTheory.Triangulated.IsStrictArtinianObject
#print axioms CategoryTheory.Triangulated.isStrictNoetherianObject
#print axioms CategoryTheory.Triangulated.IsStrictNoetherianObject
#print axioms CategoryTheory.Triangulated.isStrictArtinianObject_of_isArtinianObject
#print axioms CategoryTheory.Triangulated.isStrictNoetherianObject_of_isNoetherianObject
#print axioms CategoryTheory.Triangulated.isArtinianObject_of_isStrictArtinianObject
#print axioms CategoryTheory.Triangulated.isNoetherianObject_of_isStrictNoetherianObject
#print axioms CategoryTheory.Triangulated.subobjectImageOfFullFaithful
#print axioms CategoryTheory.Triangulated.subobjectImageOfFullFaithful_injective
#print axioms CategoryTheory.Triangulated.subobjectImageOfFullFaithful_monotone
#print axioms CategoryTheory.Triangulated.Finite.subobject_of_fullFaithful_preservesMono
#print axioms CategoryTheory.Triangulated.isArtinianObject_of_fullFaithful_preservesMono
#print axioms CategoryTheory.Triangulated.isNoetherianObject_of_fullFaithful_preservesMono
#print axioms CategoryTheory.Triangulated.strictSubobjectImageOfFullFaithful
#print axioms CategoryTheory.Triangulated.strictSubobjectImageOfFullFaithful_monotone
#print axioms CategoryTheory.Triangulated.strictSubobjectImageOfFullFaithful_injective
#print axioms CategoryTheory.Triangulated.isStrictArtinianObject_of_fullFaithful_map_strictMono
#print axioms CategoryTheory.Triangulated.isStrictNoetherianObject_of_fullFaithful_map_strictMono
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.finite_subobject_of_leftHeart
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.isArtinianObject_of_leftHeart
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.isNoetherianObject_of_leftHeart
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.isStrictArtinianObject_of_rightHeart
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.isStrictNoetherianObject_of_rightHeart
#print axioms CategoryTheory.Triangulated.IsStrictFiniteLengthObject
#print axioms CategoryTheory.Triangulated.IsFiniteLengthObject
#print axioms CategoryTheory.Triangulated.isStrictFiniteLengthObject_iff
#print axioms CategoryTheory.Triangulated.IsStrictFiniteLengthObject.isStrictArtinianObject
#print axioms CategoryTheory.Triangulated.IsStrictFiniteLengthObject.isStrictNoetherianObject
#print axioms CategoryTheory.Triangulated.IsStrictFiniteLengthObject.mk'
#print axioms CategoryTheory.Triangulated.IsFiniteLengthObject.isArtinianObject
#print axioms CategoryTheory.Triangulated.IsFiniteLengthObject.isNoetherianObject
#print axioms CategoryTheory.Triangulated.IsFiniteLengthObject.mk'
#print axioms CategoryTheory.Triangulated.isStrictFiniteLengthObject_of_finite_subobjects
#print axioms CategoryTheory.Triangulated.isStrictFiniteLengthObject_of_isFiniteLengthObject
#print axioms CategoryTheory.Triangulated.isStrictFiniteLengthObject_iff_isFiniteLengthObject
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.isStrictSubobject_of_isAdmissible
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.admissibleToStrictSubobject
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.isAdmissiblyArtinian_of_isStrictArtinian
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.isAdmissiblyNoetherian_of_isStrictNoetherian
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.isFiniteLength_of_isStrictFiniteLength
#print axioms CategoryTheory.Triangulated.Slicing.IsLocallyFinite.of_strictFiniteLength
#print axioms CategoryTheory.Triangulated.Slicing.IsLocallyFinite.of_finiteSubobjects
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.strictShortExact_of_distinguished
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.exists_distinguished_of_shortExact_toLeftHeart
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.exists_distinguished_of_strictShortExact
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.strictShortExact_iff_exists_distinguished
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.K₀_of_strictShortExact
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.strictShortExact_inclusion
#print axioms CategoryTheory.Triangulated.HNFiltration.appendStrictFactor
#print axioms CategoryTheory.Triangulated.TStructure.exists_distinguished_triangle_of_heart_epi
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_mem_enveloped_branch
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_gt_of_geProp
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_lt_of_leProp
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.intervalProp_of_skewedSemistable_upper_target
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.intervalProp_of_skewedSemistable_lower_target
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.hom_eq_zero_of_deformedPred_of_target_transport
#print axioms CategoryTheory.Triangulated.Slicing.toTStructure
#print axioms CategoryTheory.Triangulated.Slicing.toTStructure_heart_iff
#print axioms CategoryTheory.Triangulated.Slicing.toTStructure_bounded

/-! ## Owner relative phase geometry (#236) -/

#print axioms CategoryTheory.Triangulated.Deformation.relativePhase
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_mem_Ioc
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_polar
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_of_ray
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_zero
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_neg
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_add_two
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_eq_of_mem
#print axioms CategoryTheory.Triangulated.Deformation.im_sq_le_norm_sub_one_sq_mul
#print axioms CategoryTheory.Triangulated.Deformation.abs_sin_arg_le_norm_sub_one
#print axioms CategoryTheory.Triangulated.Deformation.sin_abs_eq_abs_sin
#print axioms CategoryTheory.Triangulated.Deformation.abs_arg_one_add_lt
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_perturbation
#print axioms CategoryTheory.Triangulated.Deformation.SectorFiniteLength
#print axioms CategoryTheory.Triangulated.Deformation.WideSectorFiniteLength
#print axioms CategoryTheory.Triangulated.Deformation.exists_wideSectorRadius
#print axioms CategoryTheory.Triangulated.Deformation.exists_sectorRadius
#print axioms CategoryTheory.Triangulated.Deformation.rotatedIm
#print axioms CategoryTheory.Triangulated.Deformation.rotatedIm_polar
#print axioms CategoryTheory.Triangulated.Deformation.rotatedIm_eq_norm_mul_sin
#print axioms CategoryTheory.Triangulated.Deformation.rotatedIm_eq_zero_of_relativePhase_eq
#print axioms CategoryTheory.Triangulated.Deformation.rotatedIm_neg_of_relativePhase_lt
#print axioms CategoryTheory.Triangulated.Deformation.rotatedIm_pos_of_relativePhase_gt
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_gt_of_rotatedIm_pos
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_lt_of_rotatedIm_neg
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_seesaw
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_seesaw_strict
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_seesaw_dual
#print axioms CategoryTheory.Triangulated.rotatedIm_charge_eq_sum
#print axioms CategoryTheory.Triangulated.rotatedIm_charge_neg_of_hn
#print axioms CategoryTheory.Triangulated.rotatedIm_charge_pos_of_hn
#print axioms CategoryTheory.Triangulated.Slicing.rotatedIm_charge_neg_of_interval
#print axioms CategoryTheory.Triangulated.Slicing.rotatedIm_charge_pos_of_interval
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.charge
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.phase
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.ChargeNe
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.phase_congr
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.phase_iso
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.charge_triangle
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.phase_seesaw
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.phase_seesaw_strict
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.IsSemistable
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.IsSemistable.phase_le_of_quotient_triangle
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.IsSemistable.phase_mem_Ioc
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.IsSemistable.charge_polar
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.IsSemistable.ofIso
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.IsSemistable.ofCompatibleInterval
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.subobject_isZero_iff_eq_bot
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.subobject_not_isZero_of_ne_bot
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.subobject_arrow_strictMono
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.strictShortExact_cokernel
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.liftSub
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.liftSub_le
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.liftSub_ne_bot
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.liftSub_lt
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.liftSub_arrow_strictMono
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.phase_liftSub
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.exists_phase_gt_strictSubobject_of_not_semistable
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.exists_first_strictShortExact_of_not_semistable
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.pullbackProjection_strictEpi
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.bot_arrow_strictMono
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.pullbackArrow_strictMono
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.le_pullbackCokernel
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.ofLE_pullbackProjection_eq_zero
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.lt_pullbackCokernel_of_ne_bot
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.pullbackCokernel_ne_top
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.cokernel_not_isZero_of_ne_top
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.cokernelPullbackIso
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.charge_cokernelPullback
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.phase_cokernelPullback
#print axioms CategoryTheory.Triangulated.Deformation.SkewedStabilityFunction.phase_cokernel_lt_of_phase_gt_strictSubobject
#print axioms CategoryTheory.Triangulated.Deformation.SemistableChargeBound
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_charge_eq
#print axioms CategoryTheory.Triangulated.Deformation.perturbedCharge_ne_zero
#print axioms CategoryTheory.Triangulated.Deformation.skewedStabilityFunctionOfBound
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_perturbation_of_charge
#print axioms CategoryTheory.Triangulated.Deformation.stabilitySeminorm
#print axioms CategoryTheory.Triangulated.Deformation.charge_norm_pos
#print axioms CategoryTheory.Triangulated.Deformation.ratio_le_stabilitySeminorm
#print axioms CategoryTheory.Triangulated.Deformation.stabilitySeminorm_nonneg
#print axioms CategoryTheory.Triangulated.Deformation.stabilitySeminorm_zero
#print axioms CategoryTheory.Triangulated.Deformation.stabilitySeminorm_neg
#print axioms CategoryTheory.Triangulated.Deformation.stabilitySeminorm_add_le
#print axioms CategoryTheory.Triangulated.Deformation.semistableChargeBound_of_stabilitySeminorm_le
#print axioms CategoryTheory.Triangulated.Deformation.semistableChargeBound_toReal
#print axioms CategoryTheory.Triangulated.Deformation.skewedStabilityFunctionOfSeminormLtOne
#print axioms CategoryTheory.Triangulated.Deformation.relativePhase_perturbation_of_stabilitySeminorm
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_of_isZero
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_deformedPred_witness
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_charge_ne
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_charge_polar
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_intrinsic_phase_window
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedGtGen
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLeGen
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLtGen
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedGtPred
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLePred
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLtPred
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLePred_mono
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLtPred_mono
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLePred_of_deformedLtPred
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedGtPred_anti
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_shift_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_of_shift_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_shift_neg_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedGtPred_shift_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedGtPred_shift_neg_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLePred_shift_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLePred_shift_neg_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLtPred_shift_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLtPred_shift_neg_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedGtPred_shift_one_same
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLePred_shift_neg_one_same
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLtPred_shift_neg_one_same
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedGtPred_of_triangle_obj₃
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLePred_of_triangle_obj₁
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLtPred_of_triangle_obj₁
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.hom_eq_zero_of_intrinsic_deformed_gap
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.hom_eq_zero_of_deformedPred_large_gap
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.hom_eq_zero_of_deformedPred_gap
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.hom_eq_zero_of_deformedCuts_gap
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.hom_eq_zero_of_skewed_small_gap
#print axioms CategoryTheory.Triangulated.midpoint_branch_contains
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_sub_lt_of_stabilitySeminorm
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_mem_interval_of_stabilitySeminorm
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_mem_lower_branch
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_mem_upper_branch
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_mem_expanded_interval
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_eq_of_mem_branch
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.charge_ne_of_interval
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_eq_of_common_interval
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedSemistable_of_subinterval
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_eq_of_target_envelope
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_rewitness_subinterval
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedSemistable_of_nested_interval
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedSemistable_of_controlled_subinterval
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedSemistable_on_witness_intersection
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedSemistable_common_refinement
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_rewitness_nested_interval
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewed_phiPlus_le
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewed_phiMinus_ge
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_intrinsic_bounds
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_geProp
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_leProp
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedPred_intervalProp
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.intervalProp_of_deformed_hn
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedGtPred_gtProp
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLePred_leProp
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedLtPred_ltProp
#print axioms CategoryTheory.Triangulated.Slicing.mem_phaseShiftHeart_of_intrinsic_bounds
#print axioms CategoryTheory.Triangulated.Slicing.mem_phaseShiftHeart_of_intervalProp
#print axioms CategoryTheory.Triangulated.Slicing.gtProp_leProp_of_phaseShiftHeart
#print axioms CategoryTheory.Triangulated.Slicing.geProp_leProp_of_phaseShiftHeart
#print axioms CategoryTheory.Triangulated.Slicing.gtProp_leProp_of_intrinsic_bounds
#print axioms CategoryTheory.Triangulated.midpoint_left_target_thin
#print axioms CategoryTheory.Triangulated.midpoint_right_target_thin
#print axioms CategoryTheory.Triangulated.midpoint_image_window_thin
#print axioms CategoryTheory.Triangulated.Slicing.mem_phaseShiftHeart_of_midpoint_left
#print axioms CategoryTheory.Triangulated.Slicing.mem_phaseShiftHeart_of_midpoint_right
#print axioms CategoryTheory.Triangulated.Slicing.exists_heart_image_factorisation_windows
#print axioms CategoryTheory.Triangulated.slicingDist
#print axioms CategoryTheory.Triangulated.slicingDistTerm_le
#print axioms CategoryTheory.Triangulated.phiPlusDist_le
#print axioms CategoryTheory.Triangulated.phiMinusDist_le
#print axioms CategoryTheory.Triangulated.slicingDist_self
#print axioms CategoryTheory.Triangulated.slicingDist_symm
#print axioms CategoryTheory.Triangulated.slicingDist_triangle
#print axioms CategoryTheory.Triangulated.instPseudoEMetricSpaceSlicing
#print axioms CategoryTheory.Triangulated.abs_phiPlus_sub_lt_of_slicingDist
#print axioms CategoryTheory.Triangulated.abs_phiMinus_sub_lt_of_slicingDist
#print axioms CategoryTheory.Triangulated.intervalProp_of_semistable_slicingDist
#print axioms CategoryTheory.Triangulated.slicingDist_le_of_phase_bounds
#print axioms CategoryTheory.Triangulated.Deformation.basisNhd
#print axioms CategoryTheory.Triangulated.Deformation.mem_basisNhd_iff
#print axioms CategoryTheory.Triangulated.Deformation.self_mem_basisNhd
#print axioms CategoryTheory.Triangulated.Deformation.StabilityCondition.WithClassMap.topologicalSpace
#print axioms CategoryTheory.Triangulated.Deformation.basisNhd_isOpen_generator
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedHN_exists_in_cut_strip
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedHN_exists_of_bounded_cuts
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedHN_exists
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedSlicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedSlicing_isLocallyFinite
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformed
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.slicingDist_deformed_le
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_with_Z_mem_basisNhd
#print axioms CategoryTheory.Triangulated.K₀.of_shift_int
#print axioms CategoryTheory.Triangulated.instWellFoundedLTStrictSubobjectOfIsStrictArtinianObject
#print axioms CategoryTheory.Triangulated.instWellFoundedGTStrictSubobjectOfIsStrictNoetherianObject
#print axioms CategoryTheory.Triangulated.Slicing.zero_of_geProp_ltProp_at
#print axioms CategoryTheory.Triangulated.HNFiltration.chain_obj_gtProp
#print axioms CategoryTheory.Triangulated.HNFiltration.chain_obj_leProp
#print axioms CategoryTheory.Triangulated.Slicing.geProp_of_semistable
#print axioms CategoryTheory.Triangulated.HNFiltration.prefix_phiMinus
#print axioms CategoryTheory.Triangulated.Slicing.exists_split_at_cutoff
#print axioms CategoryTheory.Triangulated.HNFiltration.prefix_phiMinus_gt
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_iso
#print axioms CategoryTheory.Triangulated.Slicing.phiPlus_iso
#print axioms CategoryTheory.Triangulated.Slicing.semistable_of_HN_all_eq
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_of_postnikovTower
#print axioms CategoryTheory.Triangulated.Slicing.semistable_of_triangle
#print axioms CategoryTheory.Triangulated.Slicing.phiMinus_triangle_le
#print axioms CategoryTheory.Triangulated.Slicing.phiPlus_triangle_le
#print axioms CategoryTheory.Triangulated.Slicing.intervalProp_chain_of_postnikovTower
#print axioms CategoryTheory.Triangulated.Slicing.exists_split_at_cutoff_with_upper_bound
#print axioms CategoryTheory.Triangulated.HNFiltration.isZero_factor_zero_of_hom_eq_zero
#print axioms CategoryTheory.Triangulated.Slicing.semistable_of_phiPlus_eq_phiMinus
#print axioms CategoryTheory.Triangulated.Slicing.leProp_zero
#print axioms CategoryTheory.Triangulated.Slicing.phiPlus_eq_phiMinus_of_semistable
#print axioms CategoryTheory.Triangulated.Slicing.zero_of_geProp_ltProp_general
#print axioms CategoryTheory.Triangulated.HNFiltration.isZero_factor_last_of_hom_eq_zero
#print axioms CategoryTheory.Triangulated.Slicing.zero_of_gtProp_leProp_general
#print axioms CategoryTheory.Triangulated.Slicing.gtProp_zero
#print axioms CategoryTheory.Triangulated.TStructure.heart_biprod
#print axioms CategoryTheory.Triangulated.TStructure.truncGE_map_comp_descTruncGE_assoc
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_faithful
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_full
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toLeftHeart_faithful
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.toRightHeart_full
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.inclusion
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.isStrictFiniteLength_of_isFiniteLength
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.isAdmissibleSubobject_of_isStrictSubobject
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.admissibleStrictSubobjectOrderIso
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.strictShortExact_pullback_left
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.strictShortExact_pullback_right
#print axioms CategoryTheory.Triangulated.Deformation.Slicing.IntervalCat.strictShortExact_of_kernel_strictEpi
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_gt_of_geProp_of_phase_range
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedSemistable_of_interval_inclusion
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedSemistable_of_target_subinterval
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedSemistable_of_target_envelope
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.hom_eq_zero_of_deformedPred
#print axioms CategoryTheory.Triangulated.Slicing.IntervalCat.isLimitKernelForkOfDistinguished
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.phase_seesaw_dual
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedSemistable_of_upper_inclusion
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedSemistable_of_lower_inclusion
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedSemistable_of_target_triangleTest
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.phase_add_lt_of_le_of_lt
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.phase_lt_upper_of_destabilizing_subobject
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.comp_mdq_of_destabilizing_with_quotient_bound
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.hom_eq_zero_of_enveloped_semistable
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_strictSubobject_of_phiPlus_gt
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_strictMDQ_with_quotient_bound
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_gt_of_strictQuotient_inner
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.skewedPhase_lt_of_phiPlus_lt
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.hn_exists_with_phiPlus_reduction
#print axioms CategoryTheory.Triangulated.HNFiltration.firstFactor_phiPlus_le_target
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.semistable_has_deformedHN
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.interior_has_enveloped_HN_skewed
#print axioms CategoryTheory.Triangulated.HNFiltration.target_phiMinus_le_lastFactor
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.interior_has_enveloped_HN
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_deformedCut_triangle_of_hn
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.semistable_mem_deformedLt
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.semistable_has_tight_deformedHN
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.semistable_mem_deformedGt
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_global_deformedCut_triangle
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.isZero_of_deformedGtLe
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.hom_eq_zero_of_deformedGtLe
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedHN_of_cut_window
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformedSlicing_P
#print axioms CategoryTheory.Triangulated.interval_strictFiniteLength_of_inclusion
#print axioms CategoryTheory.Triangulated.intervalInclusion_map_strictMono
#print axioms CategoryTheory.Triangulated.intervalSubobject_arrow_strictMono
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformed_intervalProp_subset_old_wide
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformed_Z
#print axioms CategoryTheory.Triangulated.sector_bound'
#print axioms CategoryTheory.Triangulated.stabilitySeminorm_bound_real
#print axioms CategoryTheory.Triangulated.stabilitySeminorm_lt_top_of_near
#print axioms CategoryTheory.Triangulated.finiteSeminormSubgroup
#print axioms CategoryTheory.Triangulated.norm_Z_le_of_tau_semistable
#print axioms CategoryTheory.Triangulated.norm_sum_exp_ge_cos_mul_sum
#print axioms CategoryTheory.Triangulated.stabilitySeminorm_le_of_near
#print axioms CategoryTheory.Triangulated.finiteSeminormSubgroup_eq_of_basisNhd
#print axioms CategoryTheory.Triangulated.intrinsicPhaseBounds_of_semistable_slicingDist
#print axioms CategoryTheory.Triangulated.stabilitySeminorm_lt_top_of_same_Z
#print axioms CategoryTheory.Triangulated.finiteSeminormSubgroup_eq_of_same_Z
#print axioms CategoryTheory.Triangulated.sector_bound
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.false_of_all_hn_phases_below
#print axioms CategoryTheory.Triangulated.gt_phases_of_gtProp
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.phiMinus_le_le_phiPlus
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.phase_eq_of_same_Z
#print axioms CategoryTheory.Triangulated.phiPlus_le_of_leProp
#print axioms CategoryTheory.Triangulated.im_divided_of_semistable
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.P_of_Q_of_P_semistable
#print axioms CategoryTheory.Triangulated.eq_of_pos_mul_exp_eq
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.false_of_all_hn_phases_above
#print axioms CategoryTheory.Triangulated.bridgeland_lemma_6_4
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.false_of_gt_and_le_phases
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.false_of_hn_phases_le_with_lt
#print axioms CategoryTheory.Triangulated.basisNhd_mono
#print axioms CategoryTheory.Triangulated.exists_basisNhd_subset_basisNhd
#print axioms CategoryTheory.Triangulated.linearInterpolationZ_zero
#print axioms CategoryTheory.Triangulated.basisNhd_self
#print axioms CategoryTheory.Triangulated.linearInterpolationZ_sub
#print axioms CategoryTheory.Triangulated.exists_local_lift_sameComponent_in_basisNhd
#print axioms CategoryTheory.Triangulated.wideSectorFiniteLength_mono
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_epsilon0_sixteenth
#print axioms CategoryTheory.Triangulated.linearInterpolationZ_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.eq_of_same_Z_near
#print axioms CategoryTheory.Triangulated.linearInterpolationZ
#print axioms CategoryTheory.Triangulated.basisNhd_subset_connectedComponent_small
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.deformation
#print axioms CategoryTheory.Triangulated.stabilitySeminorm_smul_complex
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.eq_of_same_Z_of_mem_basisNhd
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.exists_eq_Z_and_mem_basisNhd_of_stabilitySeminorm_lt_sin
#print axioms CategoryTheory.Triangulated.stabilitySeminorm_dominated_of_basisNhd
#print axioms CategoryTheory.Triangulated.linearInterpolationZ_sub_sub
#print axioms CategoryTheory.Triangulated.stabilitySeminorm_smul
#print axioms CategoryTheory.Triangulated.stabilitySeminorm_center_dominates_of_basisNhd
#print axioms CategoryTheory.Triangulated.Z_mem_finiteSeminormSubgroup
#print axioms CategoryTheory.Triangulated.exists_basisNhd_subset_connectedComponent
#print axioms CategoryTheory.Triangulated.basisNhdFamily
#print axioms CategoryTheory.Triangulated.stabilitySeminorm_dominated_of_connected
#print axioms CategoryTheory.Triangulated.eq_zero_of_stabilitySeminorm_toReal_eq_zero
#print axioms CategoryTheory.Triangulated.exists_basisNhd_subset_of_mem_nhds
#print axioms CategoryTheory.Triangulated.eq_zero_of_vanishes_on_cl
#print axioms CategoryTheory.Triangulated.finiteSeminormSubgroup_eq_of_connected
#print axioms CategoryTheory.Triangulated.stabilityCondition_isOpen_connectedComponent
#print axioms CategoryTheory.Triangulated.exists_basisNhd_subset_of_mem_open
#print axioms CategoryTheory.Triangulated.isTopologicalBasis_basisNhd
#print axioms CategoryTheory.Triangulated.ComponentTopologicalLinearLocalModel
#print axioms CategoryTheory.Triangulated.componentSeminormTopology_eq_normTopology
#print axioms CategoryTheory.Triangulated.componentSeminormBall
#print axioms CategoryTheory.Triangulated.componentSeminormTopology
#print axioms CategoryTheory.Triangulated.componentNorm_equivalent_of_mem_component
#print axioms CategoryTheory.Triangulated.componentSeminormSubgroup
#print axioms CategoryTheory.Triangulated.isTopologicalBasis_componentSeminormBasis
#print axioms CategoryTheory.Triangulated.componentZMap
#print axioms CategoryTheory.Triangulated.componentTopologicalLinearLocalModel
#print axioms CategoryTheory.Triangulated.componentSeminormBasis
#print axioms CategoryTheory.Triangulated.componentSeminorm_lt_top_of_mem_component
#print axioms CategoryTheory.Triangulated.componentRep
#print axioms CategoryTheory.Triangulated.componentSeminormBall_eq_ball
#print axioms CategoryTheory.Triangulated.componentNormedAddCommGroup
#print axioms CategoryTheory.Triangulated.componentNorm
#print axioms CategoryTheory.Triangulated.componentNormedSpace
#print axioms CategoryTheory.Triangulated.ComponentTopologicalLinearLocalModel.chargeMap
#print axioms CategoryTheory.Triangulated.componentStabilityCondition
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.CentralChargeIsLocalHomeomorphOnConnectedComponents
#print axioms CategoryTheory.Triangulated.componentZ_mem
#print axioms CategoryTheory.Triangulated.mk_componentRep
#print axioms CategoryTheory.Triangulated.centralChargeIsLocalHomeomorphOnConnectedComponents
#print axioms CategoryTheory.Triangulated.componentAddGroupNorm
#print axioms CategoryTheory.Triangulated.StabilityFunction.shortExact_of_mono
#print axioms CategoryTheory.Triangulated.mem_semiClosedUpperHalfPlane_of_arg_pos
#print axioms CategoryTheory.Triangulated.arg_le_of_cross_nonneg
#print axioms CategoryTheory.Triangulated.inf_le_arg_sum_of_semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.cross_pos_of_arg_lt
#print axioms CategoryTheory.Triangulated.cross_nonneg_of_arg_le
#print axioms CategoryTheory.Triangulated.arg_sum_le_sup_of_semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.sum_mem_semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.StabilityFunction.isSemistable_cokernel_mapMono_iff
#print axioms CategoryTheory.Triangulated.StabilityFunction.Subobject.ofLE_map_comp_mapMonoIso_hom
#print axioms CategoryTheory.Triangulated.StabilityFunction.Subobject.mapMonoIso
#print axioms CategoryTheory.Triangulated.StabilityFunction.Subobject.map_eq_mk_mono
#print axioms CategoryTheory.Triangulated.StabilityFunction.exists_hn_with_last_phase_of_semistable
#print axioms CategoryTheory.Triangulated.StabilityFunction.append_hn_filtration_of_mono
#print axioms CategoryTheory.Triangulated.StabilityFunction.Subobject.cokernelMapMonoIso
#print axioms CategoryTheory.Triangulated.StabilityFunction.phase_cokernel_mapMono_eq
#print axioms CategoryTheory.Triangulated.interval_thinFiniteLength_of_inclusion_strict
#print axioms CategoryTheory.Triangulated.intervalInclusion_isAdmissibleSubobject
#print axioms CategoryTheory.Triangulated.interval_finiteLength_of_inclusion
#print axioms CategoryTheory.Triangulated.autFunctor_isAdmissibleSubobject
#print axioms CategoryTheory.Triangulated.chargeHom_norm_le_of_intrinsic_width
#print axioms CategoryTheory.Triangulated.Tilting.TStructure.triangleLTGE_iso_of_amp_negOne_zero
#print axioms CategoryTheory.Triangulated.Tilting.originalHeartCohNegOneIsoOfAmplitude
#print axioms CategoryTheory.Triangulated.Tilting.originalHeartCohZeroIsoOfAmplitude
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_phase_le_phiPlus
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_phase_eq_of_mem_P
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_isSemistable_of_mem_P
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseIndex
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseIndex_le_of_lt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseBase_add_one
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseIndex_eq_zero_of_mem_Ioc
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseBase_mem
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseBase
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseIndex_lt_phase
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseBase_eq_of_mem_Ioc
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phase_le_phaseIndex_add_one
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseBase_add_phaseIndex
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseIndex_add_one

#print axioms CategoryTheory.Triangulated.semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.semiClosedUpperHalfPlane_ne_zero
#print axioms CategoryTheory.Triangulated.arg_pos_of_mem_semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.StabilityFunction
#print axioms CategoryTheory.Triangulated.StabilityFunction.ext
#print axioms CategoryTheory.Triangulated.StabilityFunction.phase
#print axioms CategoryTheory.Triangulated.StabilityFunction.phase_pos
#print axioms CategoryTheory.Triangulated.StabilityFunction.phase_le_one
#print axioms CategoryTheory.Triangulated.StabilityFunction.phase_mem_Ioc
#print axioms CategoryTheory.Triangulated.StabilityFunction.IsSemistable
#print axioms CategoryTheory.Triangulated.StabilityFunction.IsStable
#print axioms CategoryTheory.Triangulated.StabilityFunction.exists_destabilizing_of_not_semistable
#print axioms CategoryTheory.Triangulated.StabilityFunction.charge_eq_of_iso
#print axioms CategoryTheory.Triangulated.StabilityFunction.phase_eq_of_iso
#print axioms CategoryTheory.Triangulated.StabilityFunction.isSemistable_of_iso
#print axioms CategoryTheory.Triangulated.StabilityFunction.isSemistable_iff_of_iso
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.n
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.chain
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.chain_bot
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.chain_top
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.chain_strictMono
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.factor_semistable
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.factor_phase
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phiPlus
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phiMinus
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phase_mem_range
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phiMinus_le_phiPlus
#print axioms CategoryTheory.Triangulated.StabilityFunction.HasHNProperty
#print axioms CategoryTheory.Triangulated.StabilityFunction.subobject_isZero_iff_eq_bot
#print axioms CategoryTheory.Triangulated.StabilityFunction.subobject_ne_bot_of_not_isZero
#print axioms CategoryTheory.Triangulated.StabilityFunction.subobject_not_isZero_of_ne_bot
#print axioms CategoryTheory.Triangulated.StabilityFunction.subobject_top_ne_bot_of_not_isZero
#print axioms CategoryTheory.Triangulated.StabilityFunction.subobject_ofLE_bot
#print axioms CategoryTheory.Triangulated.StabilityFunction.subobjectCokernelBotIso
#print axioms CategoryTheory.Triangulated.StabilityFunction.cokernel_not_isZero_of_ne_top
#print axioms CategoryTheory.Triangulated.StabilityFunction.imageSubobject_epi_comp
#print axioms CategoryTheory.Triangulated.StabilityFunction.imageSubobject_eq_top_of_epi
#print axioms CategoryTheory.Triangulated.StabilityFunction.pullback_obj_injective_of_epi
#print axioms CategoryTheory.Triangulated.im_nonneg_of_mem_semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.add_mem_semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.phaseCross
#print axioms CategoryTheory.Triangulated.phaseCross_eq_norm_mul_sin
#print axioms CategoryTheory.Triangulated.phaseCross_nonneg_of_arg_le
#print axioms CategoryTheory.Triangulated.arg_le_of_phaseCross_nonneg
#print axioms CategoryTheory.Triangulated.phaseCross_pos_of_arg_lt
#print axioms CategoryTheory.Triangulated.arg_lt_of_phaseCross_pos
#print axioms CategoryTheory.Triangulated.arg_add_le_max
#print axioms CategoryTheory.Triangulated.arg_add_lt_max
#print axioms CategoryTheory.Triangulated.min_arg_le_arg_add
#print axioms CategoryTheory.Triangulated.StabilityFunction.phase_le_max_of_shortExact
#print axioms CategoryTheory.Triangulated.StabilityFunction.min_phase_le_of_shortExact
#print axioms CategoryTheory.Triangulated.StabilityFunction.phase_le_of_epi
#print axioms CategoryTheory.Triangulated.StabilityFunction.hom_eq_zero_of_semistable_phase_gt
#print axioms CategoryTheory.Triangulated.StabilityFunction.phase_cokernel_ofLE_congr
#print axioms CategoryTheory.Triangulated.StabilityFunction.isSemistable_cokernel_ofLE_congr
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.n_eq_one_of_semistable
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.isSemistable_of_n_eq_one
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.n_eq_one_iff_isSemistable
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.two_le_n_of_not_isSemistable
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.le_of_arrow_comp_cokernel_zero
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.pullback_cokernel_bot_eq
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.card_subobject_cokernel_lt
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.le_pullback_cokernel
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.ofLE_pullbackπ_cokernel_eq_zero
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.shortExact_ofLE_pullbackπ_cokernel
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.charge_pullback_eq_add
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.pullback_imageSubobject_eq
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.charge_cokernel_pullback_eq
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phase_cokernel_pullback_eq
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.cokernelPullbackIso
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.tail
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.tail_n
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.transport_n
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.n_eq
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.le_of_ofLE_comp_cokernel_zero
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.hom_eq_zero_to_factor
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.le_chain_of_semistable_phase_gt
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.eq_bot_of_semistable_phase_gt_phiPlus
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.chain_one_ne_bot
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phase_chain_one
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.chain_one_isSemistable
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phiPlus_eq
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.chain_one_eq
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.semistable_phase_le_phiPlus
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.le_chain_one_of_semistable_phase_eq_phiPlus
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.chain_one_maximal_semistable_phase
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.hom_eq_zero_to_semistable_of_phase_lt_phiMinus
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phiMinus_eq
#print axioms CategoryTheory.Triangulated.StabilityFunction.phiPlus
#print axioms CategoryTheory.Triangulated.StabilityFunction.phiMinus
#print axioms CategoryTheory.Triangulated.StabilityFunction.maxDestabilizingSubobject
#print axioms CategoryTheory.Triangulated.StabilityFunction.maxDestabilizingSubobject_eq_filtration
#print axioms CategoryTheory.Triangulated.StabilityFunction.maxDestabilizingSubobject_ne_bot
#print axioms CategoryTheory.Triangulated.StabilityFunction.maxDestabilizingSubobject_isSemistable
#print axioms CategoryTheory.Triangulated.StabilityFunction.maxDestabilizingSubobject_eq_top_iff_isSemistable
#print axioms CategoryTheory.Triangulated.StabilityFunction.destabilizingQuotient
#print axioms CategoryTheory.Triangulated.StabilityFunction.isZero_destabilizingQuotient_iff_isSemistable
#print axioms CategoryTheory.Triangulated.StabilityFunction.destabilizingQuotient_not_isZero_of_not_isSemistable
#print axioms CategoryTheory.Triangulated.StabilityFunction.destabilizingShortComplex
#print axioms CategoryTheory.Triangulated.StabilityFunction.destabilizingShortComplex_shortExact
#print axioms CategoryTheory.Triangulated.StabilityFunction.charge_eq_maxDestabilizingSubobject_add_destabilizingQuotient
#print axioms CategoryTheory.Triangulated.StabilityFunction.phiPlus_eq_filtration
#print axioms CategoryTheory.Triangulated.StabilityFunction.phase_maxDestabilizingSubobject
#print axioms CategoryTheory.Triangulated.StabilityFunction.le_maxDestabilizingSubobject_of_semistable_phase_eq_phiPlus
#print axioms CategoryTheory.Triangulated.StabilityFunction.phiMinus_eq_filtration
#print axioms CategoryTheory.Triangulated.StabilityFunction.phiMinus_le_phiPlus
#print axioms CategoryTheory.Triangulated.StabilityFunction.isSemistable_iff_phiPlus_eq_phiMinus

/-! ## Cohomology exactness (#146) -/

#print axioms CategoryTheory.Triangulated.Tilting.originalHeartCoh_exact_of_distTriang
#print axioms CategoryTheory.Triangulated.Tilting.originalHeartCoh_isZero_of_isZero
#print axioms CategoryTheory.Triangulated.Tilting.heart_map_originalHeartCoh

/-! ## TStructure — bounded t-structures and t-exact functors (#146) -/

#print axioms CategoryTheory.Triangulated.TStructure.IsBounded
#print axioms CategoryTheory.Triangulated.TStructure.isBounded_iff
#print axioms CategoryTheory.Triangulated.TStructure.exists_isLE
#print axioms CategoryTheory.Triangulated.TStructure.exists_isGE
#print axioms CategoryTheory.Triangulated.TStructure.IsNondegenerate
#print axioms CategoryTheory.Triangulated.TStructure.isNondegenerate_of_isBounded
#print axioms CategoryTheory.Functor.IsRightTExact
#print axioms CategoryTheory.Functor.IsLeftTExact
#print axioms CategoryTheory.Functor.IsTExact
#print axioms CategoryTheory.Functor.isLE_map_of_isRightTExact
#print axioms CategoryTheory.Functor.isGE_map_of_isLeftTExact
#print axioms CategoryTheory.Functor.isTExact_of
#print axioms CategoryTheory.Functor.isRightTExact_of_isLE_zero
#print axioms CategoryTheory.Functor.isLeftTExact_of_isGE_zero
#print axioms CategoryTheory.Functor.isLeftTExact_rightAdjoint
#print axioms CategoryTheory.Functor.isRightTExact_leftAdjoint
#print axioms CategoryTheory.Functor.heart_map_of_isTExact
#print axioms CategoryTheory.Functor.isRightTExact_comp
#print axioms CategoryTheory.Functor.isLeftTExact_comp
#print axioms CategoryTheory.Functor.isTExact_comp
#print axioms CategoryTheory.Functor.isRightTExact_id
#print axioms CategoryTheory.Functor.isLeftTExact_id
#print axioms CategoryTheory.Functor.isTExact_id

/-! ## Repository-owned t-structure heart bridges -/


/-! ## ForMathlib — results Mathlib lacks at the pin -/

#print axioms Matrix.polarFactor

-- Repository-owned heart results used by weak-tilting cohomology.
#print axioms CategoryTheory.ObjectProperty.FullSubcategory.isZero_of_obj_isZero
#print axioms CategoryTheory.Triangulated.TStructure.heart_hι
#print axioms CategoryTheory.Triangulated.TStructure.heart_containsZero
#print axioms CategoryTheory.Triangulated.TStructure.heart_closedUnderBinaryProducts
#print axioms CategoryTheory.Triangulated.TStructure.heart_closedUnderFiniteProducts
#print axioms CategoryTheory.Triangulated.TStructure.heart_hasFiniteProducts
#print axioms CategoryTheory.Triangulated.TStructure.heart_admissible
#print axioms CategoryTheory.Triangulated.TStructure.heartAbelian
#print axioms CategoryTheory.Triangulated.TStructure.heartFullSubcategoryAbelian
#print axioms CategoryTheory.Triangulated.TStructure.exists_image_factorisation_epi_triangle
#print axioms CategoryTheory.Triangulated.TStructure.exists_distinguished_triangle_of_heart_mono
#print axioms CategoryTheory.Triangulated.TStructure.exists_image_factorisation_triangles
#print axioms CategoryTheory.Triangulated.TStructure.heartFullSubcategory_shortExact_of_distTriang
#print axioms CategoryTheory.Triangulated.TStructure.heartFullSubcategory_shortExact_triangle
#print axioms CategoryTheory.Triangulated.TStructure.truncGE_map_comp_descTruncGE
#print axioms CategoryTheory.Triangulated.TStructure.exists_truncLT_octahedral_split
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

#print axioms IntegralLattice.NumLattice
#print axioms IntegralLattice.eq_zero_of_zsmul_eq_zero
#print axioms IntegralLattice.eq_zero_of_two_zsmul_eq_zero
#print axioms IntegralLattice.zsmul_injective
#print axioms IntegralLattice.zsmul_left_cancel
#print axioms IntegralLattice.finrank_numLattice
#print axioms IntegralLattice.ne_zero_of_apply_ne_zero
#print axioms IntegralLattice.eq_zero_of_two_zsmul_eq_zero_num

/-! ## Mukai lane — the extension `ℤ ⊕ N ⊕ ℤ` of a symmetric bilinear lattice

Pure lattice arithmetic. Nothing here is a statement about a K3 surface, a
Mukai lattice of a variety, or any geometric object; see the module docstrings
in `DerivedAlgGeo/LinearAlgebra/Lattice/Mukai/`. -/

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

#print axioms CategoryTheory.Triangulated.TStructure.shiftedTriangleLTGE
#print axioms CategoryTheory.Triangulated.TStructure.shiftedTriangleLTGE_distinguished
#print axioms CategoryTheory.Triangulated.TStructure.isLE_shiftedTriangleLTGE_obj₁
#print axioms CategoryTheory.Triangulated.TStructure.isGE_shiftedTriangleLTGE_obj₃
#print axioms CategoryTheory.Triangulated.TStructure.exists_shiftedTriangleLTGE_iso
#print axioms CategoryTheory.Triangulated.TStructure.shiftedTriangleLTGEIso
#print axioms CategoryTheory.Triangulated.TStructure.shiftedTriangleLTGEIso_hom₂
#print axioms CategoryTheory.Triangulated.TStructure.truncLTShiftIso
#print axioms CategoryTheory.Triangulated.TStructure.truncGEShiftIso
#print axioms CategoryTheory.Triangulated.TStructure.truncLTShiftIso_hom_comp_truncLTι
#print axioms CategoryTheory.Triangulated.TStructure.truncLTShiftIso_hom_comp_truncLTι_assoc
#print axioms CategoryTheory.Triangulated.TStructure.truncGEπ_comp_truncGEShiftIso_hom
#print axioms CategoryTheory.Triangulated.TStructure.truncGEπ_comp_truncGEShiftIso_hom_assoc
#print axioms CategoryTheory.Triangulated.TStructure.truncGEπ_comp_truncGEShiftIso_inv
#print axioms CategoryTheory.Triangulated.TStructure.truncGEπ_comp_truncGEShiftIso_inv_assoc
#print axioms CategoryTheory.Triangulated.TStructure.truncLTShiftNatIso
#print axioms CategoryTheory.Triangulated.TStructure.truncGEShiftNatIso
#print axioms CategoryTheory.Triangulated.TStructure.truncLEShiftNatIso
#print axioms CategoryTheory.Triangulated.TStructure.truncGELEShiftNatIso
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

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.ofPre
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.ofPre_slicing
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.ofPre_Z
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityFunction
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityFunction.toWeak
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.StabilityFunction.toWeak_Z
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.charge_triangle
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.charge_triangle'
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.charge_isZero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.slope
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.slope_of_im_pos
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.slope_of_im_nonpos
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.IsSemistable
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.IsStable
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.IsStable.isSemistable
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.zeroCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.zeroCharge_def
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.zeroCharge_isClosedUnderIsomorphisms
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.charge_eq_zero_pair
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.zeroCharge_left
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.zeroCharge_right
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.zeroCharge_extension

/-! ## WeakStability lane -- noetherian torsion subcategories

Definition 14.6 in Remark 14.7's chain form (the design decision is in the
module docstring), the free = B-perp identification riding on
free_of_orthogonal, and the zero-subcategory nonvacuity witness. Lemmas
14.8 and 14.11 are deliberately UNDECLARED with their gaps named in the
module -- absent beats sorry-backed. Closes #108. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.IsHeartMono
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.SubobjectChain
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.SubobjectChain.Terminates
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.NoetherianTorsionSubcategory
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.rightOrthogonal
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.free_iff_rightOrthogonal
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.isIso_of_isZero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.zeroTorsionPair
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.zeroNoetherianTorsion
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.noetherian_mono

/-! ## WeakStability lane -- the torsion pair at a phase cutoff

Display (14.1) in phase language, unconditional on the slicing axioms: the
pair (P((b,1]), P((0,b])) as a HeartTorsionPair on the slicing-induced
t-structure, with the HN cut as decomposition and the slicing's own
hom-vanishing as the orthogonality. slicingTilt_heart_iff composes with
tilt_heart_iff (#106) to identify the tilted heart. The normalized
slope--phase ray identity is formalized later in this lane, but the exact
source-facing cutoff equivalence is not packaged or reviewed; the coverage
map therefore remains `mapped`, not a claim. Closes #109. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseTors
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseFree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.leProp_of_iso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.gtProp_of_iso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.mem_heart_of_bounds
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.slicingTorsionPair
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.slicingTorsionPair_tors
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.slicingTorsionPair_free
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.slicingTilt_heart_iff

/-! ## WeakStability lane -- the tilting property

Definition 14.12 in phase language: A0 is the torsion class of a noetherian
torsion subcategory, and every heart object with phiPlus below the boundary
has a heart-triangle envelope with zero-charge quotient and shifted
Hom-vanishing. The later phase-language Lemma 14.17 infrastructure and
phase-language Proposition 14.16 infrastructure make no coverage promotion:
the map stays `mapped`, and the exact source proposition remains undeclared.
The raw Definition 14.12 envelope is now sufficient for the heart-level
assembly. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.IsNoetherianTorsionSubcategory
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.zeroCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.HasFiniteMaxSlope
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.HasTiltingEnvelope
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.HasPhaseTiltingEnvelope
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.HasPhaseTiltingEnvelope.hasTiltingEnvelope
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.TiltingProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.TiltingProperty.hasTiltingEnvelope_of_phaseFree

/-! ## WeakStability lane -- heart equivalence and weak HN infrastructure

The two stacked weak-stability milestones following #110: isomorphism
transport for weak stability functions, the slicing-to-heart forward bridge,
and abelian weak Harder--Narasimhan filtrations with existence for the induced
heart function.  These declarations make no new source-coverage claim. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.charge_eq_of_iso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.isSemistable_of_iso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.slope_eq_of_iso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.isSemistable_iff_of_iso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.isStable_of_iso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.isStable_iff_of_iso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.weakStabilityFunctionOnHeart
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_Z
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_zeroCharge_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.charge_mem_upperHalfPlane_and_arg_le_phiPlus
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.pi_mul_phiMinus_le_charge_arg_of_im_pos
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_isSemistable_of_mem_P_phi
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.mem_P_phiPlus_of_weakStabilityFunctionOnHeart_isSemistable
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_isSemistable_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.SlicingBridge.phiPlus_le_of_heart_subobject
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.heartSlope
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.heartSlope_cokernel_ofLE_congr
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.heartSlope_cokernel_mapMono_eq
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.heartSemistable_cokernel_ofLE_congr
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.heartSemistable_cokernel_mapMono_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakAbelianHNFiltration
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakAbelianHNFiltration.factor
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakAbelianHNFiltration.factor_not_isZero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakAbelianHNFiltration.factor_obj_not_isZero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.HeartSemistable
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.HasHNProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.append_hn_filtration_of_mono
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.exists_hn_with_last_slope_of_semistable
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.HNQuotientStep
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.HasHNQuotientInduction
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.hasHNProperty_of_quotientInduction
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.instAbelianFullSubcategoryHeart_derivedAlgGeo_2
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.charge_arg_eq_pi_mul_of_mem_P_phi_lt_one
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.charge_im_pos_of_mem_P_phi_lt_one
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.slope_lt_of_mem_P_of_phase_lt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.slope_eq_top_of_mem_P_one
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_hasHN
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.instAbelianFullSubcategoryHeart_derivedAlgGeo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.instAbelianFullSubcategoryHeart_derivedAlgGeo_1

/-! ## WeakStability lane -- phase-tilt semistable classification

The rotated weak stability function on the HRS tilt, both directions of the
phase-language counterpart of Lemma 14.17, and the positive-imaginary/stable
Hom-vanishing refinement.  These entries make no source-coverage promotion:
the slope--phase reparameterisation remains the mapped boundary. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltRotation
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltRotation_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltCharge_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltHeart_interval
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltHeart_iff_phaseShiftHeart
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltWeakStabilityFunction
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltWeakStabilityFunction_Z
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltWeakStabilityFunction_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.zeroCharge_mem_P_one
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltWeakStabilityFunction_zeroCharge_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.hom_eq_zero_of_zeroCharge_to_phaseTiltSemistable
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_isSemistable_left_of_zeroCharge_right
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_isSemistable_of_phaseTors_phaseTiltSemistable
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_isSemistable_of_phaseFree_shiftSemistable
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltWeakStabilityFunction_isSemistable_of_ray
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.IsPhaseTiltTypeOne
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.IsPhaseTiltTypeTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.isSemistable_of_isPhaseTiltTypeOne
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.isSemistable_of_isPhaseTiltTypeTwo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltClassification_of_isSemistable
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.isSemistable_of_phaseTiltClassification
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltWeakStabilityFunction_isSemistable_iff_classification

/-! ## WeakStability lane -- Proposition 14.16 heart-level assembly

The maximal-zero-charge-subobject construction, raw-envelope noetherian
assembly, boundary-saturated weak HN assembly over the cohomological `H⁻¹`
and `H⁰` filtrations, and support-property transport. Proposition 14.16
itself remains undeclared, but its heart-level constructive obligations are
assembled directly from Definition 14.12's `TiltingProperty`. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.HasZeroChargeDecompositions
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.zeroChargeTorsionPair
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.zeroChargeTorsionPair_tors
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.zeroChargeTorsionPair_free
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.heartZeroCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.heartZeroCharge_isSerreClass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.rightOrthogonal_of_iso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.cokernelCompShortComplex
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.cokernelCompShortComplex_shortExact
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.kernelCokernelCompMiddleShortComplex
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.kernelCokernelCompMiddleShortComplex_shortExact
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.kernelCompShortComplex
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.kernelCompShortComplex_shortExact
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.isSemistable_middle_of_zeroCharge_quotient
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.isSemistable_quotient_of_zeroCharge_subobject
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.isHeartMono_of_mono
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.mono_of_isHeartMono
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.isNoetherianObject_of_zeroCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.hasZeroChargeDecomposition_of_chainCondition
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.hasZeroChargeDecompositions_of_chainCondition
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.hasZeroChargeDecomposition_of_reduction
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.mono_comp_of_zeroCharge_of_rightOrthogonal
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.mono_in_originalHeart_of_mono_in_phaseTilt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.zeroCharge_phaseTors
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltingEnvelope_gives_shiftedZeroChargeDecomposition
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltingEnvelope_middle_semistable
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_zeroChargeChain_terminates_of_tiltingEnvelope
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_semistableQuotient_of_saturatedExtension
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_zeroChargeChain_terminates_of_rightOrthogonal
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_hasZeroChargeDecompositions_of_freeShiftDecompositions
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_hasZeroChargeDecompositions_of_phaseEnvelopes
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_hasZeroChargeDecompositions_of_tiltingEnvelopes
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_isNoetherianObject_of_zeroCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltNoetherianTorsionSubcategory
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_hasZeroChargeDecompositions_of_chainCondition
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltNoetherianTorsionSubcategoryOfDecompositions
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltNoetherianTorsionSubcategoryOfTiltingProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltNoetherianTorsionSubcategoryOfPhaseEnvelopes
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltNoetherianTorsionSubcategoryOfTiltingEnvelopes
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltNoetherianTorsionSubcategoryOfChainCondition
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltCharge_im_pos_of_phaseTors
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_slope_lt_of_phase_separated
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_slope_shift_lt_shift_of_phase_separated
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_slope_unshifted_lt_shifted_of_phase_separated
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_semistableQuotient_of_extension
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_hnLastQuotient
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_existsHNWithLastSource_of_freeShift_zeroCharge_extension
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_hasHN_of_freeShift_zeroCharge_extension
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_hZeroLastQuotient
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_hasHNProperty_of_zeroChargeDecompositions
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.semistableClasses
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.HasSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.isSemistable_of_zeroCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.class_eq_zero_of_zeroCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseTiltLinearCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.phaseTiltLinearCharge_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.norm_phaseTiltLinearCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_hasSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.QuadraticSupportData
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.QuadraticSupportData.hasSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.QuadraticSupportData.class_eq_zero_of_zeroCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.UniformQuadraticSupportData
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.UniformQuadraticSupportData.fiber
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.UniformQuadraticSupportData.reindex
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.QuadraticSupportData.constant
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.QuotientUniformQuadraticSupportData
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.QuotientUniformQuadraticSupportData.fiber
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.QuotientUniformQuadraticSupportData.zero_class_eq_zero
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.semistableClasses
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.mem_semistableClasses_iff
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.class_mem_semistableClasses
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.HasSupportProperty
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.QuadraticSupportData
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.QuadraticSupportData.charge_compatible
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.QuadraticSupportData.quadratic
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.QuadraticSupportData.hasSupportProperty
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.UniformQuadraticSupportData
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.UniformQuadraticSupportData.charge_compatible
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.UniformQuadraticSupportData.quadratic
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.UniformQuadraticSupportData.fiber
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.UniformQuadraticSupportData.reindex
#print axioms CategoryTheory.Triangulated.PreStabilityCondition.WithClassMap.QuadraticSupportData.constant
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.PhaseTiltHeartObligations
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltHeartObligations
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltHeartObligationsOfPhaseEnvelopes
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltHeartObligationsOfTiltingProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_hasHNPropertyOfTiltingProperty

/-! ## WeakStability lane -- reverse heart--slicing foundations

The extended-slope phase normalization, integer-normalized ambient phase
family, analytic charge-ray identity, heart-HN to ambient-Postnikov
conversion, and phase-tilt prestability assembly. These declarations package
no source statement and make no §14 coverage promotion. -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.weakPhaseOfSlope
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.weakPhaseOfSlope_top
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.weakPhaseOfSlope_coe
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.weakPhaseOfSlope_coe_mem_Ioo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.weakPhaseOfSlope_mem_Ioc
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.weakPhaseOfSlope_strictMono
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.weakPhaseOfSlope_lt_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.complex_eq_pos_mul_exp_weakPhaseOfSlope
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.charge_ray_of_mem_heart
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.negOnePow_mul_exp_pi_eq_exp_add_int
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientPhasePredicate_charge_ray
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.phase
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.phase_mem_Ioc
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.phase_lt_phase_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.phase_eq_of_iso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.heartPhasePredicate
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.heartPhasePredicate_closedUnderIso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.heartPhasePredicate_instClosedUnderIso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.shiftedHeartPhasePredicate
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientPhasePredicate
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.shiftedHeartPhasePredicate_zero_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientPhasePredicate_iff_of_mem_Ioc
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.shiftedHeartPhasePredicate_closedUnderIso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientPhasePredicate_closedUnderIso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientPhasePredicate_instClosedUnderIso
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.shiftedHeartPhasePredicate_shift_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientPhasePredicate_shift_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientPhasePredicate_shift_int
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakAbelianHNFiltration.factorInclusion
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakAbelianHNFiltration.factorInclusion_mono
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.instAbelianFullSubcategoryHeart_derivedAlgGeo_3
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakAbelianHNFiltration.factorTriangle
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakAbelianHNFiltration.factorTriangle_distinguished
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakAbelianHNFiltration.toAmbientHN
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.HNFiltration.relabelPhasePredicate
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakAbelianHNFiltration.toAmbientNormalizedHN
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientHNOfHeart
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientHN_exists_of_mem_heart
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.HNFiltration.shiftWeakAmbient
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.HNFiltration.shiftWeakAmbient_phase
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientHN_exists_of_mem_heart_with_phase_bounds
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientHN_exists_of_pure
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientHN_exists_of_width
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientHN_exists_of_bounded
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientHN_of_bounded
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.heartTorsionPair_tilt_isBounded
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ReverseSlicingObligations
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ReverseSlicingObligations.toSlicing
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ReverseSlicingObligations.toSlicing_P
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ReverseSlicingObligations.toWeakPreStabilityCondition
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ReverseSlicingObligations.toWeakPreStabilityCondition_slicing
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltLatticeCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltLatticeCharge_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTilt_ambientPhasePredicate_charge_ray
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.PhaseTiltHeartObligations.ambientHN_exists_of_mem_tiltedHeart
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.PhaseTiltHeartObligations.ambientHN
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.PhaseTiltHeartObligations.toWeakPreStabilityCondition
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.PhaseTiltHeartObligations.toWeakPreStabilityCondition_Z
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.PhaseTiltHeartObligations.toWeakPreStabilityCondition_P
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltWeakPreStabilityConditionOfTiltingProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltWeakPreStabilityConditionOfTiltingProperty_Z
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.phaseTiltWeakPreStabilityConditionOfTiltingProperty_P

/-! ## WeakStability lane -- source-normalized §14 tilting -/

#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.weakStabilityFunctionOnHeart_phase_eq_of_mem_P_phi
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.ExtremalHNData
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.extremalHNData
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.muPlus
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.muMinus
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.weakPhaseOfSlope_muPlus
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.weakPhaseOfSlope_muMinus
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.slopeCutPhase
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.slopeCutPhase_mem_Ioo
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.muMinus_gt_iff_phiMinus_gt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.muPlus_le_iff_phiPlus_le
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.slopeTors
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.slopeFree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.slopeTors_iff_phaseTors
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.slopeFree_iff_phaseFree
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.slopeTorsionPair
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.slopeTorsionPair_tors
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.slopeTorsionPair_free
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.slopeTilt_heart_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltScale
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltScale_pos
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTilt_multiplier
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltRotation
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltRotation_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltRotation_eq_scale_phaseTiltRotation
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltLatticeCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltLatticeCharge_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltLatticeCharge_eq_scale_phaseTiltLatticeCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltCharge_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltCharge_eq_scale_phaseTiltCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_Z
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_charge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_charge_eq_scale_phaseTilt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_slope_eq_phaseTilt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_isSemistable_iff_phaseTilt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_isStable_iff_phaseTilt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_zeroCharge_iff
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_ambientPhasePredicate_eq_phaseTilt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakPreStabilityConditionOfTiltingProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakPreStabilityConditionOfTiltingProperty_Z
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakPreStabilityConditionOfTiltingProperty_P
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakPreStabilityConditionOfTiltingProperty_P_source
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.sourceTiltLinearCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.sourceTiltLinearCharge_apply
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.sourceTiltLinearCharge_eq_scale_phaseTiltLinearCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.norm_sourceTiltLinearCharge
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTilt_hasSupportProperty
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.SourceTiltConclusion
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltConclusion
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltConclusion_condition_Z
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_isSemistable_iff_phaseClassification
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTilt_typeOne_im_nonneg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTilt_typeTwo_im_neg
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.sourceTiltWeakStabilityFunction_isSemistable_iff_classification
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.hom_eq_zero_of_zeroCharge_to_sourceTiltSemistable
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.slope_between_of_triangle
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.instAbelianFullSubcategoryHeart
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.slope_le_of_heart_epi
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.heart_subobject_slope_le
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.heart_hom_zero_of_semistable_phase_gt
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.ambientPhasePredicate_hom_zero
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakStabilityFunction.reverseSlicingObligationsOfHN

/-! ## Support lane — the Kontsevich-Soibelman quadratic-form reformulation

The basic statements are linear algebra plus one compactness argument over a
finite-dimensional real normed space and keep `S` arbitrary. The later
genuine/uniform/quotient declarations add bundled quadratic forms, a saturated
integral quotient, and a weak-stability adapter whose selected loci are actual
nonzero weak-semistable heart classes. The adapter still supplies no geometric
family, HN structure over a curve, boundedness, or moduli theory. -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasSupportProperty
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.IsHomogTwo
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.IsCompatible
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.slice
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.isCompact_slice
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.norm_inv_smul_mem_slice
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.hasSupportProperty_of_isCompatible
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.exists_isCompatible_of_hasSupportProperty
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.hasSupportProperty_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasSupportProperty.mono
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasSupportProperty.eq_zero_of_charge_eq_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.hasSupportProperty_of_norm_sub_le
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasSupportProperty.exists_tolerance
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.isOpen_hasSupportProperty
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.quadraticForm_isHomogTwo
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasQuadraticSupportProperty
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasQuadraticSupportProperty.hasSupportProperty
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasQuadraticSupportProperty.mono
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.familyLocus
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasUniformQuadraticSupportProperty
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasUniformQuadraticSupportProperty.fiber
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.hasUniformQuadraticSupportProperty_of_union
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.hasUniformQuadraticSupportProperty_iff_union
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasUniformQuadraticSupportProperty.reindex
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasQuadraticSupportProperty.constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.hasUniformQuadraticSupportProperty_constant_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.transportQuadraticForm
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.transportQuadraticForm_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.isCompatible_transport
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasUniformQuadraticSupportProperty.transport
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.hasUniformQuadraticSupportProperty_transport_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.quotientCharge
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.quotientCharge_mkQ
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.quotientFamilyLocus
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasUniformQuadraticSupportPropertyModulo
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.hasUniformQuadraticSupportPropertyModulo_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasUniformQuadraticSupportPropertyModulo.fiber
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasUniformQuadraticSupportPropertyModulo.hasSupportProperty
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.mkQ_eq_zero_of_mem
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.HasQuadraticSupportProperty.constant_modulo
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.IsSaturated
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.saturatedClosure
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.subset_saturatedClosure
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.isSaturated_saturatedClosure
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.saturatedClosure_le
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.neg_mem_saturatedClosure_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.Quotient
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.quotientClass
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.quotientClass_eq_zero_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.quotient_isAddTorsionFree
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.quotient_moduleFinite
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.quotient_moduleFree
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.saturatedClosure_le_ker
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.quotientCharge
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.quotientCharge_quotientClass
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.quotientToRealQuotient
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.quotientToRealQuotient.congr_simp
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.quotientToRealQuotient_quotientClass
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.RealScalarExtension
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.scalarExtensionComparison
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.scalarExtensionComparison_tmul
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.scalarExtensionComparison_quotientClass
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.exists_scalarExtensionEquiv_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.scalarExtensionEquiv
#print axioms CategoryTheory.Triangulated.StabilityCondition.Support.ZeroChargeLattice.scalarExtensionEquiv_apply

/-! ## FiniteLength lane — charges on the free lattice of simples

`Fin n -> Z` is a MODEL of `K_0(A)` for a finite-length abelian category, not
an identification: that is Jordan-Holder, which exists in neither Mathlib nor
the foundational library. Every result is a theorem about `Fin n -> Z`. -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.FiniteLength.mem_cone_smul
#print axioms CategoryTheory.Triangulated.StabilityCondition.FiniteLength.mem_cone_sum
#print axioms CategoryTheory.Triangulated.StabilityCondition.FiniteLength.chargeOf
#print axioms CategoryTheory.Triangulated.StabilityCondition.FiniteLength.chargeOf_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.FiniteLength.chargeOf_single
#print axioms CategoryTheory.Triangulated.StabilityCondition.FiniteLength.eq_chargeOf
#print axioms CategoryTheory.Triangulated.StabilityCondition.FiniteLength.existsUnique_charge
#print axioms CategoryTheory.Triangulated.StabilityCondition.FiniteLength.mem_cone_natCombination
#print axioms CategoryTheory.Triangulated.StabilityCondition.FiniteLength.chargeOf_mem_cone
#print axioms CategoryTheory.Triangulated.StabilityCondition.FiniteLength.chargeOf_ne_zero

/-! ## Wall lane — numerical walls in the (s, t) half plane

Arithmetic on triples of reals. There is NO surface: no coherent sheaf, no
Chern character, no polarisation, and no Bogomolov-Gieseker inequality -- and
none is axiomatised, because the wall equation is an identity and needs none. -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.NumClass
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.NumClass.rk
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.NumClass.deg
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.NumClass.ch2
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.reZ
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.imZ
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.minA
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.minB
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.minC
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.wallExpr
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.wallExpr_eq
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.wall_iff_circle
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.wall_circle_eq
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.wall_line_eq
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.shift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.minA_shift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.minB_shift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.minC_shift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.wallExpr_shift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.charge_eq_zero_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.eq_of_two_walls

/-! ### Wall lane — the nested wall theorem

Still the same arithmetic: `wall_eq_of_meet` is a statement about triples of
reals and says nothing about sheaves. In particular it is NOT the geometric
nested-wall theorem, which additionally asserts that the walls it orders are
walls of actual stability, and that is not expressible at the pin.

`wall_eq_of_meet_needs_charge` is a counterexample, not a theorem about walls:
it exhibits two genuinely different walls meeting at the one point where `v`'s
charge degenerates, which is what makes the charge hypothesis load-bearing
rather than decorative. -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.minor_orth
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.crossAB
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.crossAC
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.crossBC
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.crossAB_swap
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.crossAC_swap
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.crossBC_swap
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.minorCross_eq_zero_of_two_walls
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.wall_subset_of_crossZero
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.wall_eq_of_meet
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.degV
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.degV_charge_eq_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.Wall.wall_eq_of_meet_needs_charge

/-! ## GroupAction lane — NormalizedShift (step 1) -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift.toOrderIso_injective
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift.ext'
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift.symm_map_add_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift.group
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift.mul_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift.one_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift.inv_apply

/-! ## GroupAction lane — ShiftAnalysis (step 3c groundwork) -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift.map_add_nat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift.map_sub_nat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift.map_add_int
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift.uniformContinuous
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.NormalizedShift.exists_radius

/-! ## GroupAction lane — GLTilde (step 2) -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.rayVec
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.rayVec_add_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.rayVec_ne_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.OnRay
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.OnRay.refl
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.OnRay.trans
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.toMat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.toMat_mul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.toMat_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.Compatible
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.compat_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.compat_mul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.compat_inv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.ext'
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.group
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.mul_mat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.mul_shift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.one_mat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.one_shift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.inv_mat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.inv_shift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.toMatHom
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.toShiftHom

/-! ## GroupAction lane — ComplexBridge (step 3 groundwork) -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cplxCoord
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cplxCoord_exp
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.compat_exp
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actC
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actC_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actC_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actC_mul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actC_exp

/-! ## GroupAction lane — SlicingAction (step 3a) -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.relabel
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.relabel_P
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.slicingMulAction
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.smul_slicing_P
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.gltildeSlicingMulAction
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.gltilde_smul_slicing_P
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.relabel_intervalProp_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.relabel_intervalProp

/-! ## GroupAction lane — PreStabilityAction (step 3b) -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actPre
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actPre_slicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actPre_Z
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.preMulAction
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.smul_pre_slicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.smul_pre_Z

/-! ## GroupAction lane — StabilityAction (step 3c) -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.relabel_isLocallyFinite
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actStab
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actStab_slicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actStab_Z
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.stabMulAction
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.smul_stab_slicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.smul_stab_Z

/-! ## AutAction — transport along a triangulated auto-equivalence

These extend the foundational library's own namespace, since they are API for its types. -/

#print axioms CategoryTheory.Triangulated.PostnikovTower.mapF
#print axioms CategoryTheory.Triangulated.HNFiltration.mapF
#print axioms CategoryTheory.Triangulated.Slicing.mapEquiv
#print axioms CategoryTheory.Triangulated.Slicing.mapEquiv_P

/-! ## StrictAutAction — a strict subgroup of autoequivalences -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut.comp_inv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut.inv_comp
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut.obj_inv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut.obj_self
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut.F_inv_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut.F_inv_mul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut.equiv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut.equiv_functor
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut.equiv_inverse
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut.actSlicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut.actSlicing_P
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.StrictAut.mulActionSlicing

/-! ## QuotAutAction — Aut(D) as an honest group, by quotienting -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv.id
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv.comp
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv.symm
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv.act
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv.act_P
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv.act_id
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv.act_comp
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv.act_congr
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv.setoid
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutQuot
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutQuot.group
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutQuot.mulActionSlicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutQuot.mk
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutQuot.mk_smul_P

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

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.rayVec_eq_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.rayVec_eq_of_onRay
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deckShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deckShift_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.compat_one_deckShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deck
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deck_mat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deck_shift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.exists_deckShift_of_mat_eq_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deckHom
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deckHom_injective
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.range_deckHom_eq_ker
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.kerEquiv

/-! ## GLTildeSurj — the projection is surjective

COVERAGE COMPLETE as of 2026-08-07. This section was the single largest gap in
the file: `scripts/StabilityConditionCensus.lean` reported **20** ungated public declarations
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

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cexpI
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cexpI_re
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cexpI_im
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cexpI_add
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.norm_cexpI
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cexpI_ne_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cplxCoord_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cplxCoord_cexpI
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cA
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cB
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.mulVec_rayVec_eq
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.normSq_cA_sub_normSq_cB
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.det_toMat_pos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.normSq_cB_lt_normSq_cA
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cA_ne_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.norm_cB_lt_norm_cA
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.ratio
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.norm_ratio_lt_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.Wmap
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.Wmap_re_pos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.Wmap_ne_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cexpI_neg_two_pi
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.Wmap_add_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.lift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.pi_mul_lift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.mulVec_rayVec_lift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.lift_scale_pos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.compatible_lift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.lift_add_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cross
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cross_rayVec
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cross_mulVec
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.cross_smul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.abs_arg_Wmap_lt
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.lift_lt_lift_of_lt_of_sub_lt_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.lift_add_nat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.lift_strictMono
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.lift_continuous
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.lift_surjective
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.liftShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.liftShift_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.compatible_liftShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.toMatHom_surjective
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.sect
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.sect_mat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.toMatHom_comp_sect
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deck_injective
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.existsUnique_deck_mul_sect
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.exact_deckHom_toMatHom

/-! ## GLTildeTopology — topology and simple connectedness -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.rotationMatrix
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.rotationMatrix_det
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.rotationMatrix_mulVec_rayVec
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.rotationMatrix_neg_mul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.rotationMatrix_mul_neg
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.rotationGLPos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.rotationGLPos_mat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.phaseTranslation
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.phaseTranslation_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.compatible_rotation
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.liftedRotation
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.liftedRotation_mat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.liftedRotation_shift_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.ext_mat_shift_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.PositiveReal
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTildeCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperMatrix
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperMatrix_det
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperMatrixInv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperMatrix_mul_inv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperMatrix_inv_mul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperGLPos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperGLPos_mat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.alignedMatrix
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.alignedMatrix_zero_zero_pos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.alignedMatrix_one_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.alignedMatrix_one_one_pos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glTildeCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.matrixOfCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.matrixOfCoordinates_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperDeckIndex
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperDeckIndex_spec
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperSectionZero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperSectionZero_mat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperSectionZero_shift_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glTildeOfCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glTildeOfCoordinates_shift_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glTildeOfCoordinates_mat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.alignedMatrix_glTildeOfCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glTildeCoordinates_ofCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glTildeCoordinates_injective
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glTildeCoordinates_surjective
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glTildeCoordinateEquiv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glTildeCoordinateEquiv_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.topologicalSpace
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glTildeCoordinateHomeomorph
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.continuous_rotationMatrix
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glTildeOfCoordinates_coordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.continuous_toMat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.contractibleSpace
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.simplyConnectedSpace

/-! ## GLTildeCover — base coordinates and the universal covering map -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.circleMatrix
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.circleMatrixInv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.circleMatrix_det
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.circleMatrix_mul_inv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.circleMatrix_inv_mul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.circleGLPos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.circleGLPos_mat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLPosCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.firstColumnComplex
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.firstColumnComplex_ne_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.firstColumnRadius
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.firstColumnDirection
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.firstColumnDirection_re
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.firstColumnDirection_im
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.secondColumnAlong
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.secondColumnPerp
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.secondColumnPerp_pos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glPosCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glPosOfCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glPosOfCoordinates_mat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.firstColumnDirection_glPosOfCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.secondColumnAlong_glPosOfCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.secondColumnPerp_glPosOfCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glPosCoordinates_ofCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glPosOfCoordinates_coordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.continuous_toMatGLPos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glPosCoordinateHomeomorph
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.isCoveringMap_prodMap_id
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.phaseCircle
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.phaseCircle_isCoveringMap
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.coordinateProjection
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.coordinateProjection_isCoveringMap
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.phaseCircle_coe
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.circleMatrix_phaseCircle
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glPosOfCoordinates_coordinateProjection
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.coordinateProjection_apply_glTildeCoordinates
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.isCoveringMap_toMat
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.universalCoverData

/-! ## GLTildeTopologicalGroup — compatibility of topology and group operations -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.upperSectionZero_shift_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.coordinateShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.glTildeOfCoordinates_shift_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.continuous_shift_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.isTopologicalGroup

/-! ## AutPairAction — the same action, as a genuine `MulAction` -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.id
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.mul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.inv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.setoid
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_slicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_Z
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_id
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_mul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_congr
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.mk
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.group
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.mulAction
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.mk_smul_slicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.mk_smul_Z
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.toAutQuot

/-! ## Phase lane — slicing orders, Bayer bounds, and cofiltrations -/

#print axioms CategoryTheory.Triangulated.Slicing.Precedes
#print axioms CategoryTheory.Triangulated.Slicing.PrecedesWeak
#print axioms CategoryTheory.Triangulated.Slicing.LiPrecedes
#print axioms CategoryTheory.Triangulated.Slicing.LiPrecedesWeak
#print axioms CategoryTheory.Triangulated.Slicing.liPrecedes_iff_precedes
#print axioms CategoryTheory.Triangulated.Slicing.liPrecedesWeak_iff_precedesWeak
#print axioms CategoryTheory.Triangulated.Slicing.precedes_iff_phiPlus_lt
#print axioms CategoryTheory.Triangulated.Slicing.precedesWeak_iff_phiPlus_le
#print axioms CategoryTheory.Triangulated.Slicing.Precedes.weak
#print axioms CategoryTheory.Triangulated.Slicing.precedesWeak_refl
#print axioms CategoryTheory.Triangulated.Slicing.precedes_phaseShift_one
#print axioms CategoryTheory.Triangulated.Slicing.precedes_iff_lt_phiMinus
#print axioms CategoryTheory.Triangulated.Slicing.precedesWeak_iff_le_phiMinus
#print axioms CategoryTheory.Triangulated.Slicing.precedes_iff_extreme_phases_lt
#print axioms CategoryTheory.Triangulated.Slicing.precedesWeak_iff_extreme_phases_le
#print axioms CategoryTheory.Triangulated.Slicing.Precedes.trans
#print axioms CategoryTheory.Triangulated.Slicing.PrecedesWeak.trans
#print axioms CategoryTheory.Triangulated.Slicing.Precedes.trans_weak
#print axioms CategoryTheory.Triangulated.Slicing.PrecedesWeak.trans_strict
#print axioms CategoryTheory.Triangulated.Slicing.mapEquiv_ltProp_iff
#print axioms CategoryTheory.Triangulated.Slicing.mapEquiv_leProp_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv.precedes_act_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv.precedesWeak_act_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutQuot.precedes_smul_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutQuot.precedesWeak_smul_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.smul_slicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.precedes_smul_stability_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.precedesWeak_smul_stability_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.HasBayerProperty
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.SlicingBayerProperty
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.hasBayerProperty_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.hasBayerProperty_one_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.hasBayerProperty_smul_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.BayerProperty
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.bayerProperty_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.bayerProperty_one_zero
#print axioms CategoryTheory.Triangulated.CofiltrationData
#print axioms CategoryTheory.Triangulated.CofiltrationData.remainder
#print axioms CategoryTheory.Triangulated.CofiltrationProperty
#print axioms CategoryTheory.Triangulated.CofiltrationPropertyInfinity
#print axioms CategoryTheory.Triangulated.CofiltrationPropertyInfinity.toCofiltrationProperty
#print axioms CategoryTheory.Triangulated.Slicing.phaseShift_phiPlus
#print axioms CategoryTheory.Triangulated.Slicing.phaseShift_phiMinus
#print axioms CategoryTheory.Triangulated.SlicingOrderPreimageData
#print axioms CategoryTheory.Triangulated.SlicingOrderPreimageData.precedes
#print axioms CategoryTheory.Triangulated.SlicingOrderPreimageData.precedesWeak
#print axioms CategoryTheory.Triangulated.Slicing.Precedes.pushforward_of_preimage
#print axioms CategoryTheory.Triangulated.Slicing.PrecedesWeak.pushforward_of_preimage
#print axioms CategoryTheory.Triangulated.Slicing.Precedes.pullback_of_preimage
#print axioms CategoryTheory.Triangulated.Slicing.PrecedesWeak.pullback_of_preimage
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.bayerProperty_iff_phiPlus_le
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.bayerProperty_iff_le_phiMinus
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.bayerProperty_mk_iff_inverse_phiPlus_le
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.bayerProperty_mk_iff_inverse_le_phiMinus
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.bayerProperty_mk_iff_sub_le_functor_phiMinus

/-! ## Phase lane — sound slicing-transfer boundary -/

#print axioms CategoryTheory.Triangulated.PostnikovTower.mapF
#print axioms CategoryTheory.Triangulated.HNFiltration.mapF
#print axioms CategoryTheory.Triangulated.Slicing.preimagePhase
#print axioms CategoryTheory.Triangulated.Slicing.pullbackPhaseCollection
#print axioms CategoryTheory.Triangulated.Slicing.pushforwardPhaseCollection
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData
#print axioms CategoryTheory.Triangulated.Slicing.preimageData_id
#print axioms CategoryTheory.Triangulated.Slicing.preimage
#print axioms CategoryTheory.Triangulated.Slicing.preimage_P
#print axioms CategoryTheory.Triangulated.Slicing.preimage_id
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.ofFaithful
#print axioms CategoryTheory.Triangulated.Slicing.PreimageData.phaseShift
#print axioms CategoryTheory.Triangulated.Slicing.pullback
#print axioms CategoryTheory.Triangulated.Slicing.pushforward
#print axioms CategoryTheory.Triangulated.ReflectsZeroObjects
#print axioms CategoryTheory.Triangulated.Functor.reflectsZeroObjects_of_faithful
#print axioms CategoryTheory.Triangulated.Functor.reflectsZeroObjects_of_conservative
#print axioms CategoryTheory.Triangulated.HNFiltration.mapPreimage
#print axioms CategoryTheory.Triangulated.HNFiltration.mapPreimage_n
#print axioms CategoryTheory.Triangulated.HNFiltration.mapPreimage_phi
#print axioms CategoryTheory.Triangulated.Slicing.preimage_phiPlus
#print axioms CategoryTheory.Triangulated.Slicing.preimage_phiMinus
#print axioms CategoryTheory.Triangulated.Slicing.preimage_ltProp_iff
#print axioms CategoryTheory.Triangulated.Slicing.preimage_leProp_iff
#print axioms CategoryTheory.Triangulated.Slicing.preimage_phaseShift
#print axioms CategoryTheory.Triangulated.Slicing.preimage_phaseShift_self
#print axioms CategoryTheory.Triangulated.Slicing.preimageOrderData
#print axioms CategoryTheory.Triangulated.Slicing.Precedes.preimage
#print axioms CategoryTheory.Triangulated.Slicing.PrecedesWeak.preimage
#print axioms CategoryTheory.Triangulated.Slicing.preimage_mapEquiv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.preimage_representatives
#print axioms CategoryTheory.Triangulated.Slicing.LeftAdjointInducingPremise
#print axioms CategoryTheory.Triangulated.HasLeftAdjointInducingTheorem

/-! ## Normalized quotient, combined action, and topological action layer -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.TriEquiv.inverseIsoOfFunctorIso

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.relabel_mapEquiv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.gltilde_autPair_smul_comm
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.smulCommClassGLTildeAutPairQuot
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.combinedMulAction
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.prod_mk_smul_slicing
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.prod_mk_smul_Z

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.Slicing.mapEquiv_phiPlus
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.Slicing.mapEquiv_phiMinus
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.slicingDist_mapEquiv_le
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.stabSeminorm_aut_le
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.mapsTo_basisNhd
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.continuous_act
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.autPairQuotContinuousConstSMul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.homeomorph

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.Slicing.relabel_phiPlus
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.Slicing.relabel_phiMinus
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.exists_slicingDist_relabel_control
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actCCLM
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actCCLM_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actC_inv_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actCCondition
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actCCondition_pos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.norm_actC_div_norm_actC_le
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.stabSeminorm_gltilde_le
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.exists_gltilde_basisNhd_control
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.continuous_const_smul_stability
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.gltildeContinuousConstSMulStability
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.combinedContinuousConstSMulStability
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.stabilityHomeomorph
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.combinedStabilityHomeomorph

/-! ## Jointly continuous symmetry actions -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.continuous_shift_displacement
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.eventually_uniform_shift_displacement
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.slicingDist_smul_le_of_displacement
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.actCCLM_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.continuous_actCCLM
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.norm_actC_sub_div_le
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.stabSeminorm_near_identity_le
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.exists_identity_basisNhd_control
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.continuousAt_smul_identity
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.continuousAt_smul_stability
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.continuous_smul_stability
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.gltildeContinuousSMulStability
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.autPairQuotTopologicalSpace
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.autPairQuotDiscreteTopology
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.continuous_smul_stability
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.autPairQuotContinuousSMulStability
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.continuous_combined_smul_stability
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.combinedContinuousSMulStability

/-! ## Components, equivariant periods, and the effective symmetry quotient -/

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.componentSmul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.componentSmul_mk
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.componentMulAction
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.image_connectedComponent_smul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.componentHomeomorph
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.componentHomeomorph_apply_coe
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.componentStabilizer
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.mem_componentStabilizer_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.componentStabilizerMulAction

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.chargeAddEquiv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.chargeAddEquiv_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.chargeAddEquiv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.chargeAddEquiv_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.chargeAddEquiv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.chargeAddEquiv_mk
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.combinedChargeAddEquiv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.combinedChargeAddEquiv_mk_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.GLTilde.centralCharge_equivariant
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPairQuot.centralCharge_equivariant
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.combinedCentralCharge_equivariant
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.combinedCentralCharge_equivariant_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.componentCentralCharge_equivariant

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.shiftFunctorCommShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.shiftTwoMapTriangleIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.shiftTwoIsTriangulated
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.shiftNegTwoMapTriangleIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.shiftNegTwoIsTriangulated
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.shiftTwoTriEquiv
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.K₀.mapF_shift_neg_two
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.shiftTwoPair
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deckShift_neg_one_inv_apply
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.shiftTwoPair_act_eq_deck_neg_one
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deck_mul_deck
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deck_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deck_one_shiftTwo_combined_smul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.combinedActionHom
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.combinedActionKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.EffectiveCombinedSymmetry
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.effectiveCombinedPermHom
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.effectiveCombinedMulAction
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.effectiveCombinedFaithfulSMul
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deck_one_shiftTwo_mem_combinedActionKernel
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.deck_one_shiftTwo_eq_one_in_effective

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
#print axioms CategoryTheory.Triangulated.classCharge
#print axioms CategoryTheory.Triangulated.HNFiltration.classMass
#print axioms CategoryTheory.Triangulated.Slicing.classMass
#print axioms CategoryTheory.Triangulated.HNFiltration.classMass_eq_zero_of_isZero
#print axioms CategoryTheory.Triangulated.HNFiltration.classMass_eq_classMass
#print axioms CategoryTheory.Triangulated.Slicing.classMass_eq_classMass
#print axioms CategoryTheory.Triangulated.Slicing.classMass_ne_top
#print axioms CategoryTheory.Triangulated.Slicing.classMass_lt_top
#print axioms CategoryTheory.Triangulated.Slicing.classMass_toReal_eq_sum
#print axioms CategoryTheory.Triangulated.Slicing.classMass_eq_ofReal_norm_classCharge
#print axioms CategoryTheory.Triangulated.Slicing.exists_headTail_classMass
#print axioms CategoryTheory.Triangulated.HNFiltration.exists_headTail_classMass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.hnMass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.stabilityMass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.hnMass_eq_hnMass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.stabilityMass_eq_hnMass
#print axioms CategoryTheory.Triangulated.WeakStabilityCondition.WeakPreStabilityCondition.stabilityMass_ne_top
#print axioms CategoryTheory.Triangulated.stabilityMass_ne_top
#print axioms CategoryTheory.Triangulated.stabilityMass_lt_top
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_eq_sum
#print axioms CategoryTheory.Triangulated.stabilityMass_eq_zero_iff
#print axioms CategoryTheory.Triangulated.stabilityMass_toReal_pos
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_charge
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.mass_map_inverse
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.mass_map_functor
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_stabilityMass
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_stabilityMass_functor_obj

/-! ## HNPolygon — abelian HN paths and positive-angle support -/

#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.factorObj
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.hnPolygon_le_of_polygonVertex_isMax
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.last_le_phase
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.last_prefix_le_quotient_phase
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.mass
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.norm_charge_le_mass
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.norm_charge_le_polygonLength
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phase_last_prefix_le_of_ne_zero_to_semistable
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.phase_le_first
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonEdge
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonEdge_arg
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonEdge_arg_strictAnti
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonEdge_mem_semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonLength
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonLength_eq_mass
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex_exists_strict_support
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex_exists_strict_support_hnPolygon
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex_last
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex_mem_hnPolygon
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex_succ_sub
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonVertex_zero
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.quotientHNFiltration
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.quotientInfToCokernel
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.quotientInfToCokernel_mono
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.quotient_inf_phase_le
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.semistable_le_chain_of_phase_gt
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.semistable_phase_le_first
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.subobjectCharge_exists_strict_support
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.subobjectCharge_le_of_polygonVertex_isMax
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.subobject_phase_le_first
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.arg_last_edge_le_arg_last_sub_zero
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.arg_last_sub_zero_le_arg_first
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.arg_unitRay
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossFunctional
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossFunctional_apply
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossFunctional_neg_of_arg_lt
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossFunctional_pos_of_arg_lt
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.exists_strict_support_at_interior
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.length
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.norm_last_sub_zero_le_length
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.sum_edges_eq_last_sub_zero
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.unitRay
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.unitRay_im
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.unitRay_mem_semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.unitRay_re
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnPolygon
#print axioms CategoryTheory.Triangulated.StabilityFunction.hnPolygon_mono
#print axioms CategoryTheory.Triangulated.StabilityFunction.subobjectCharge_mem_hnPolygon

/-! ## ConvexPolygonPerimeter — finite perimeter and short-exact mass bounds -/

#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.mass_eq_mass
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.mass_le_add_norm_cokernel_of_mono
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.mass_le_add_norm_of_shortExact
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonLength_le_add_norm_charge_sub_of_mono
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.polygonLength_le_of_vertexHull_subset
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength_comp_monotone_le
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength_cons_cons
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength_mono_sublist
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength_nil
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength_ofFn_eq_length
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.chainLength_singleton
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedEdge
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedLength
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedLength_comp_monotone_le
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedLength_eq_length_add_chord
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedLength_eq_sum_turning
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedLength_le_of_monotone_support
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.closedTangent
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossMaxIndex
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossMaxIndex_max
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.crossMaxIndex_mono_of_angle_gt
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional_apply
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional_le_norm_mul
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional_sub_left
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional_sub_right
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional_unitDirection_self
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.dotFunctional_unitRay_sub
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorBisector
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorBisector_mem_Ioo
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorBisector_strictAnti
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorNextEdge
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorPrevEdge
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorTurnScale
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.interiorTurnScale_pos
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.last_sub_zero_mem_semiClosedUpperHalfPlane
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.length_le_of_convexHull_subset
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.length_snoc
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.norm_unitDirection_le_one
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.sub_mem_semiClosedUpperHalfPlane_of_lt
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.turningFunctional
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.turningFunctional_interior_eq_cross
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.unitDirection
#print axioms CategoryTheory.Triangulated.ComplexPolygonalPath.unitDirection_eq_unitRay_arg

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
#print axioms CategoryTheory.Triangulated.stabilitySeminorm_le_of_stabilityDist_lt
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
#print axioms CategoryTheory.Triangulated.StabilityCondition.WithClassMap.observableStabilityFunctionOnHeart_charge
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

#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_phiPlusDist
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_phiMinusDist
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_massDist
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_stabilityDistTerm
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_stabilityDistTerm_functor_obj
#print axioms CategoryTheory.Triangulated.StabilityCondition.GroupAction.AutPair.act_stabilityDist
#print axioms CategoryTheory.Triangulated.AutPairQuot_smul_stabilityDist

/-! ## Group-law spot checks

`#print axioms` audits the proof term; these check the instance actually
computes the intended composition rather than some other group structure that
happens to typecheck. Both are `rfl`, so a wrong `mul` would fail here.
-/

section SpotChecks

open CategoryTheory.Triangulated.StabilityCondition.GroupAction

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
open CategoryTheory.Triangulated
  CategoryTheory.Triangulated.StabilityCondition.GroupAction

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

#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.mk.inj
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.fibers
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.fiberPreadditive
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.fiberZero
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.fiberShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.fiberShiftAdditive
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.fiberPretriangulated
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.pullAdditive
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.pullCommShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.pullTriangulated
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.Fiber
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.pull
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.pullK₀
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.pullK₀_of
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.pullK₀_id
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.pullK₀_comp
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.CompatibleClassMaps
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.CompatibleClassMaps.pull_compatible
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.CompatibleClassMaps.class_pull
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.TriangulatedFiberFamily.CompatibleClassMaps.constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.FiberPreStabilityBaseChangeData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.FiberPreStabilityBaseChangeData.classMap_compatible
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.FiberPreStabilityBaseChangeData.charge_compatible
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.FiberPreStabilityBaseChangeData.preimageData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.FiberPreStabilityBaseChangeData.slicing_compatible
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.FiberPreStabilityBaseChangeData.phase_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.FiberPreStabilityBaseChangeData.class_pull
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.FiberPreStabilityBaseChangeData.charge_pull
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.FiberPreStabilityBaseChangeData.constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.FiberPreStabilityBaseChangeData.class_mem_semistableClasses_pull
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.CategoricalOrdinaryFiberStabilityInFamiliesData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.CategoricalOrdinaryFiberStabilityInFamiliesData.ordinary
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.CategoricalOrdinaryFiberStabilityInFamiliesData.baseChange
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.CategoricalOrdinaryFiberStabilityInFamiliesData.toTheorem22_2SourceClauses
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.CategoricalOrdinaryFiberStabilityInFamiliesData.class_mem_semistableClasses_pull
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.CategoricalOrdinaryFiberStabilityInFamiliesData.commonCharge_pull
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.CategoricalOrdinaryFiberStabilityInFamiliesData.punit
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeTriangulatedFiberFamily
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeTriangulatedFiberFamily.constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.ChargeProbe.ofScheme
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.ChargeProbe.ofScheme_isLocallyConstant_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OpenLocusProbe.ofScheme
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OpenLocusProbe.ofScheme_isOpen_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.GenericSemistabilityProbe.ofScheme
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.GenericSemistabilityProbe.ofScheme_isGenericallyOpen_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.residue
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.residue_left
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.residue_hom
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.residueTo
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.residueTo_left
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeTriangulatedFiberFamily.ResidueFiber
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeTriangulatedFiberFamily.pullToResidue
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeTriangulatedFiberFamily.pullK₀ToResidue
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeTriangulatedFiberFamily.pullK₀ToResidue_of
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeDerivedCategory
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBoundedDerivedCategory
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeDerivedCategory.Q
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeDerivedCategory.boundedInclusion
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.DerivedFiber
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.BoundedDerivedFiber
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.ResidueDerivedFiber
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.ResidueBoundedDerivedFiber
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.residueDerivedFiber_eq
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.residueBoundedDerivedFiber_eq
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeTriangulatedFiberFamily.DerivedRealization
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeTriangulatedFiberFamily.DerivedRealization.residueFiberEquivalence
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeTriangulatedFiberFamily.BoundedDerivedRealization
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeTriangulatedFiberFamily.BoundedDerivedRealization.residueFiberEquivalence
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.schemeModulesHasDerivedCategory
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.modulePullback
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.modulePullbackId
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.modulePullbackComp
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullback
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.IsExactPullback
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.IsExactPullback.preservesFiniteLimits
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.IsExactPullback.preservesFiniteColimits
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.modulePullback_preservesFiniteColimits
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.IsExactPullback.of_preservesFiniteLimits
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.isExactPullback_iff_preservesFiniteLimits
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.moduleStalkRingCocone
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.moduleStalkRingIsColimit
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.presheafModuleStalkFunctor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.moduleStalkFunctor
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.presheafModuleStalkToSheafificationApp
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.presheafModuleStalkToSheafificationApp_isIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.presheafModuleStalkSheafificationIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.moduleStalkForgetIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.moduleStalkFunctor_preservesFiniteLimits
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.flatStalkMap_preservesFiniteLimits
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.flatPullbackStalkModel_preservesFiniteLimits
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.presheafModulePullback
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.modulePullbackStalkPresheafIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.moduleStalkFunctors_jointlyReflectIsomorphisms
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.preservesFiniteLimits_of_stalkwise
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.PresheafPullbackStalkComparison
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.PresheafPullbackStalkComparison.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.PresheafPullbackStalkComparison.mk.inj
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.PresheafPullbackStalkComparison.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.PullbackStalkComparison
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.PullbackStalkComparison.iso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.PullbackStalkComparison.mk.inj
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.PullbackStalkComparison.mk.sizeOf_spec
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.PresheafPullbackStalkComparison.toPullbackStalkComparison
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.pullbackStalkComparisonId
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.PullbackStalkComparison.comp
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.modulePullback_preservesFiniteLimits_of_flat_of_stalkComparison
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.isExactPullback_of_flat_of_stalkComparison
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.isExactPullback_of_flat_of_presheafStalkComparison
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.openImmersionPullbackStalkForgetIso
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.openImmersionPullbackStalk_preservesFiniteLimits
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.openImmersionModulePullback_preservesFiniteLimits
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.isExactPullback_of_isOpenImmersion
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.isExactPullbackOfIsOpenImmersion
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullback
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullback.congr_simp
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullbackFactors
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.instCommShiftDerivedFiberDerivedPullbackInt
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.instIsTriangulatedDerivedFiberDerivedPullback
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullK₀
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullK₀_of
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullToResidue
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullK₀ToResidue
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullK₀ToResidue_of
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.isExactPullbackId
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.isExactPullbackComp
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullbackId
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullbackComp
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.identityDerivedPullback
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.compositeDerivedPullback
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullbackIdLocalized
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullbackId
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullbackCompLocalized
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullbackComp
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullK₀_id
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullK₀_comp
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullback_associativity
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullback_associativity_assoc
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullback_left_unitality
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullback_left_unitality_assoc
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullback_right_unitality
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullback_right_unitality_assoc
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullbackCongr
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullbackCongr.congr_simp
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullbackCongr
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullbackCongr.congr_simp
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullback_left_unitality
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullback_left_unitality_assoc
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullback_right_unitality
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullback_right_unitality_assoc
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullback_associativity
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullback_associativity_assoc
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullbackFactors_commShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullbackId_commShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullbackComp_commShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullbackIdLocalized_commShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.complexPullbackCompLocalized_commShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullbackId_commShift
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.SchemeBaseChange.derivedPullbackComp_commShift
#print axioms CategoryTheory.Abelian.image.congr_simp
#print axioms CategoryTheory.Functor.IsLeftTExact.isGE_map
#print axioms CategoryTheory.Functor.IsRightTExact.isLE_map
#print axioms CategoryTheory.Functor.IsTExact.toIsLeftTExact
#print axioms CategoryTheory.Functor.IsTExact.toIsRightTExact
#print axioms CategoryTheory.Limits.imageSubobject.congr_simp
#print axioms CategoryTheory.ObjectProperty.FullSubcategory.mk.hcongr_5
#print axioms CategoryTheory.ObjectProperty.ιOfLE.congr_simp
#print axioms CategoryTheory.Pretriangulated.shortComplexOfDistTriangle.congr_simp
#print axioms CategoryTheory.ShortComplex.LeftHomologyData.ofHasKernelOfHasCokernel.congr_simp
#print axioms CategoryTheory.ShortComplex.RightHomologyData.ofHasCokernelOfHasKernel.congr_simp
#print axioms CategoryTheory.ShortComplex.ShortExact.fIsKernel.congr_simp
#print axioms CategoryTheory.ShortComplex.ShortExact.gIsCokernel.congr_simp
#print axioms CategoryTheory.Subobject.isoOfEqMk.congr_simp
#print axioms CategoryTheory.Triangulated.AbelianHNFiltration.mk.inj
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.ChargeProbe
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.ChargeProbe.IsLocallyConstant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.UniversallyLocallyConstantCharge
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.ChargeProbe.constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.ChargeProbe.constant_isLocallyConstant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.universallyLocallyConstantCharge_constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OpenLocusProbe
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OpenLocusProbe.IsOpen
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.UniversalOpenness
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OpenLocusProbe.full
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OpenLocusProbe.full_isOpen
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.universalOpenness_full
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.GenericSemistabilityProbe
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.GenericSemistabilityProbe.IsGenericallyOpen
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.UniversalGenericOpenness
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.GenericSemistabilityProbe.full
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.GenericSemistabilityProbe.full_isGenericallyOpen
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.universalGenericOpenness_full
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.DedekindHNProblem
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.IntegratesAfterDedekindBaseChange
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.DedekindHNProblem.constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.integratesAfterDedekindBaseChange_constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakDedekindHNProblem
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakIntegratesAfterDedekindBaseChange
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakDedekindHNProblem.constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.weakIntegratesAfterDedekindBaseChange_constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.BoundednessProblem
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.UniversalBoundedness
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.BoundednessProblem.trivial
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.universalBoundedness_trivial
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryDefinition20_5Conditions
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakDefinition20_5Conditions
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryStabilityInFamiliesData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryStabilityInFamiliesData.punit
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.ordinary_punit_locallyConstantCharge
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.ordinaryFiberSemistableClasses
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.mem_ordinaryFiberSemistableClasses_iff
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.class_mem_ordinaryFiberSemistableClasses
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberUniformQuadraticSupportData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberUniformQuadraticSupportData.charge_compatible
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberUniformQuadraticSupportData.quadratic
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberUniformQuadraticSupportData.fiber
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberUniformQuadraticSupportData.reindex
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.ordinaryFiberUniformQuadraticSupportData_constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.ordinaryFiberUniformQuadraticSupportData_punit
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberStabilityInFamiliesData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberStabilityInFamiliesData.definition20_5
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberStabilityInFamiliesData.charge_compatible
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberStabilityInFamiliesData.uniformSupport
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberStabilityInFamiliesData.bounded
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberStabilityInFamiliesData.toOrdinaryStabilityInFamiliesData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberStabilityInFamiliesData.toTheorem22_2SourceClauses
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberStabilityInFamiliesData.fiberSupport
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberStabilityInFamiliesData.quotientCharge_mkQ
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.OrdinaryFiberStabilityInFamiliesData.punit
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.HasGaussianRationalValues
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.hasGaussianRationalValues_zero
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakChargeProbe
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakChargeProbe.toChargeProbe
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakChargeProbe.constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakChargeProbe.constant_isLocallyConstant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakSemistabilityProbe
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakSemistabilityProbe.toGenericProbe
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakSemistabilityProbe.constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakSemistabilityProbe.constant_isGenericallyOpen
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakDefinition20_5ClauseZero
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakDefinition20_5ClauseZero.reindex
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.weakDefinition20_5ClauseZero_constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakQuotientQuadraticSupportData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakQuotientQuadraticSupportData.constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.quotientUniformQuadraticSupportData_reindex
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakStabilityInFamiliesData
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakStabilityInFamiliesData.constant
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.WeakStabilityInFamiliesData.punit
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.Theorem22_2SourceClauses
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.Theorem22_2DependencyContract
#print axioms CategoryTheory.Triangulated.StabilityCondition.Families.Theorem22_2DependencyContract.hasSourceClauses
