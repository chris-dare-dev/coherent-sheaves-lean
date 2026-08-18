# e6 — the maps out of a dg cone, and what `HasShift` left behind — 2026-08-17 (UTC)

For `dg-enhancements-e6` (#377).

## First, a correction to the record

`H0Shift.lean`'s module docstring said `assoc_hom_app` was unproved and that
"no `HasShift` instance is claimed". Both statements were false when they merged:
`shiftFunctorAddIso'_assoc`, `shiftMkCore` and `hasShift` are all in the file and
all proved. The prose was written against an earlier draft of the PR and was not
updated when the proof landed. It is corrected in this change.

So **`HasShift (H0 C) ℤ` is done**, and e6's remaining cost is not the shift. It is
the six fields of `Pretriangulated`.

## What lands here

`DGCategory/Cone.lean`, the maps *out* of a cone.

`IsConeOf` states its universal property for maps *into* `Z`: `Hom(W, Z)` splits as
`Hom(W, X)` in degree `+1` against `Hom(W, Y)`. A triangle needs the other
direction, and this file extracts it by applying the splitting to `dgId Z`:

* `fst : (dgHom Z X).X 1`, `snd : (dgHom Z Y).X 0`, `fst_inl_add_snd_inr`;
* `delta_fst : δ fst = 0` — **the projection is closed**;
* `inr_comp_fst = 0` and `inr_comp_snd = dgId Y` — the cone's two inclusions and
  two projections are orthogonal in the way a biproduct's are;
* `toShift s = fst ≫ s.hom` for a shift `s : IsShiftBy X 1 X'`, its closedness,
  and `inr ≫ toShift = 0`.

## Why `delta_fst` is the content

Nothing in `IsConeOf` mentions `δ fst`. `fst` is one half of a splitting of an
identity, and a splitting is data with no differential condition attached. What
forces closedness is **uniqueness**: differentiate `fst ≫ inl + snd ≫ inr = dgId Z`,
use `δ (dgId Z) = 0` and `δ inl = f ≫ inr`, and the result is a second splitting of
`0`. The splitting map is injective, so both components vanish, which gives
`δ fst = 0` and — the same equation, read at the other component —
`δ snd = -(fst ≫ f)`.

That asymmetry is not an accident of the proof. `snd` is *not* closed, and the term
by which it fails is exactly the one that makes the triangle rotate. Recorded here
because a later slice will need it.

## Traps

`dgComp_leibniz` produces its degrees as `-1 + 1`, `0 + 1`, `1 + 1`, while `δ_inl`
and `inr_closed` are stated at `0` and `1`. The numerals are definitionally equal,
so a restatement by `have h' : ... := h` goes through — but `rw` cannot cross the
gap, because the indices sit inside `HomologicalComplex.d` and the motive fails.
This is the third file in the track to hit it; `H0Shift.lean`'s "free degrees"
section is the same problem solved a different way.

`Int.negOnePow` lands in `ℤˣ`, not `ℤ`. The sign normalizes with
`Units.neg_smul` and `one_smul`; `neg_smul` does not fire, and `smul_smul` does not
either. And this subsystem does not import `linarith` or `linear_combination`, so
the rearrangement is `abel` on a stated identity followed by `rw` with the
hypothesis, not a one-liner.

## What e6 still owes

The transport theorem, `IsPretriangulated C → Pretriangulated (H0 C)`. Its six
fields, with what each now needs:

1. `distinguishedTriangles` — definable now: triangles isomorphic to
   `X → Y → Z → X⟦1⟧` built from `inr` and `toShift`.
2. `isomorphic_distinguished` — free from that definition.
3. `distinguished_cocone_triangle` — `exists_cone` plus this file's `toShift`.
4. `contractible_distinguished` — needs the cone of `dgId X` to be a *zero object of
   `H⁰`*, i.e. `dgId (cone (dgId X))` a coboundary. Not proved; a real computation.
5. `rotate_distinguished_triangle` — the hard one, and where `δ snd = -(fst ≫ f)`
   is expected to earn its place.
6. `complete_distinguished_triangle_morphism` — the splitting property again, in the
   form that lifts a square to a map of cones.

Acceptance criterion 4 of #377 — whether `Localization.pretriangulated` is reusable —
is answered *no* for this route, and the reason is worth recording: that lemma
transports a pretriangulated structure along a localization functor, and needs a
pretriangulated category to start from. Here there is none. `H⁰` of a dg category is
the first triangulated object in sight, so its structure has to be built, not moved.
