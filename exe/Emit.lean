/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeoSweep
import MathFormalContract

/-!
# The emitter, pointed at this repository's combined library

`lake exe emit --out attest/lean-emission.json` sweeps `Environment.constants`
and calls `Lean.collectAxioms`. **It never parses Lean source**, which is what
makes `set_option maxHeartbeats 400000 in theorem sneaky : False := by sorry`
structurally unable to hide rather than merely caught — there is no text for it
to hide in. The contract package ships a compiled fixture for exactly that
(`testdata/lean/set-option-evasion.lean`).

This complements `scripts/Audit.lean` and `scripts/BridgelandAudit.lean` rather
than replacing them. Each audit prints `#print axioms` for a hand-maintained
list of names, so it fails to *build* when a name it lists disappears — useful,
and orthogonal. A raw `#print axioms` run is not itself a gate because it prints
`[sorryAx]` and exits 0; the coherent audit is checked directly in CI and the
Bridgeland audit is checked by `scripts/check_audit.py`. The emitter is the
combined gate: `emitMain` returns non-zero when any constant's axiom closure
contains `sorryAx`, and it writes the artifact either way, because the record
is most useful exactly when the build is not clean.

It is also the only check that is complete across the combined environment.
The subsystem audits structurally cannot name private declarations; this
sweeps `Environment.constants`, so a declaration nobody remembered to list
cannot slip past it.

## It replaced the per-file source sweep (2026-08-14, #361)

CI used to also run `lake env lean` once per tracked `.lean` file and grep the
output for `declaration uses 'sorry'`. That loop was 39 m 23 s of a 54 m 01 s
run — 72.9 % of CI wall clock — to re-elaborate from source what the build step
had just built, and it was the *weaker* of the two mechanisms: it reads text,
which is what the `set_option` evasion above hides in.

Deleting it required closing a real coverage gap first. `rootLib` is what
`emitToFileForRootsImpl` **imports**; `additionalRoots` only widens the scope
filter over what that import brought in. Pointed at `DerivedAlgGeoLean`, this
emitter therefore covered 406 of 419 tracked modules, silently: `DGLean`,
`CohLean.Development` and the former vendor umbrella were outside the stable
umbrella, so no import reached them. `rootLib` is now `DerivedAlgGeoSweep`,
whose only job is to import every tracked module, and
`scripts/check_emission_coverage.py` fails the build if that ever stops being
true. A tracked module that nothing imports now fails the coverage check
instead of being swept in isolation.

The one file no emission can cover is this one: an `lean_exe` root is not a
library module and cannot appear in the environment built from its own
imports. CI keeps a single `lake env lean exe/Emit.lean` for it.

## When CI actually started running this

**From `6259180` (2026-08-06), not before.** That commit's message is
*"fix(ci): actually link the emitter, which I claimed CI did and it did not"*.
Everything above describes a gate that was real in this file's prose and absent
from `.github/workflows/ci.yml` for the whole of the `56c7531` theorem baseline.
Any claim about the emitter gate must name a commit at or after `6259180`; at or
before `56c7531`, the only axiom gate CI ran was `scripts/Audit.lean` plus a
grep of the build log for `declaration uses 'sorry'`.

Note also that this exe **cannot be linked on Windows** — `supportInterpreter`
pushes a Mathlib-scale environment past the PE export table
(`ld.lld: too many exported symbols (got 134112, max 65535)`) — so the owner's
own workstation cannot run this gate. On that platform the two subsystem audits
remain the available axiom checks, which is why they are kept despite the
coverage gap above.

## `leanOptions` is declared here, not observed

Elaboration options are compile flags and are not recorded in the `.olean`, so
the emitter cannot read them back out of the environment; reporting the process
defaults would make the artifact claim a setting the build did not use.

It must therefore mirror the `[leanOptions]` block of `lakefile.toml`
**character for character**, and `mfc lint` fails a mismatch. If you change one,
change the other in the same commit.
-/

def main (args : List String) : IO UInt32 :=
  MathFormalContract.emitMainForRoots
    (rootLib := `DerivedAlgGeoSweep)
    (additionalRoots := [`DerivedAlgGeoLean, `CohLean, `BridgelandStabLean,
                         `DGLean])
    (leanOptions := [("autoImplicit", .bool false),
                     ("relaxedAutoImplicit", .bool false)])
    args
