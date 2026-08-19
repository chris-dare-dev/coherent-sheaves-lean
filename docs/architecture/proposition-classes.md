# When a proposition-valued class is justified

This document records the contract for `Prop`-valued typeclasses in the
stability-condition subsystem. It exists because
`Slicing.HasPhaseTruncations` was a class that distinguished no objects: an
unconditional global instance derived it for every slicing from the
`hn_exists` field already present in `Slicing`, so the class carried no
information and served only as a second instance-search path to a theorem.

## Rule

A `Prop`-valued class is justified only when all three hold.

1. **It can fail.** Some inhabitant of the base structure does not satisfy it.
   If a single unconditional global instance discharges the class for every
   inhabitant, the content belongs in the base structure or in a theorem.
2. **It is selected.** At least one declaration is stated or proved only under
   the hypothesis, and at least one consumer supplies it from something other
   than the universal instance.
3. **Instance search is the right carrier.** The hypothesis propagates through
   enough call sites that threading it explicitly would dominate the API. A
   hypothesis used by one or two declarations should be an explicit argument.

Failing any of the three, prefer, in order: a field on the base structure, a
theorem, or an explicit hypothesis.

## Applying the rule

`Slicing` already carries `hn_exists`. Phase truncation at the boundary `0` is
therefore a theorem of every slicing, not a property of some slicings:

```lean
theorem Slicing.exists_phase_truncation_zero (s : Slicing C) (A : C) :
    ∃ (X Y : C) (_ : s.gtProp C 0 X) (_ : s.leProp C 0 Y)
      (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧),
      Triangle.mk f g h ∈ distTriang C
```

`Slicing.toTStructure` consumes that theorem directly and takes no instance
parameter. `Slicing.toDualTStructure` in
`Foundation/Slicing/TwoHeartEmbedding.lean` was already written this way and is
the pattern to follow for further boundary constructions.

## Genuine classes in this subsystem

Classes that do discriminate — for example finiteness, boundedness, or
support hypotheses that hold for some triangulated categories and fail for
others — remain classes. The test is the first rule above: exhibit, or be able
to exhibit, an inhabitant that fails the class. A class whose only instance is
unconditional and global is a theorem wearing a class's clothes.

## Audit, 2026-08

Every `Prop`-valued class in the library was checked against rule 1. The
fifteen classes outside `HasPhaseTruncations` all pass: their instances are
either conditional on the same class (transport along a construction, as in
`IsExactPullback` and `IsTriangleAdditive`) or specialized to a single named
object (`𝟭 C` for the t-exactness classes, `free PUnit` and `unit R` for
`IsInvertible`, `Cdg A` for `IsPretriangulated`, `P.of` for `IsAdditive`,
`ProjectiveVariety` for `IsProjective`). None is discharged unconditionally
for every inhabitant of its base type. `HasPhaseTruncations` was the only
instance of the pattern.
