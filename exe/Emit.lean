/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import DerivedAlgGeoLean
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
    (rootLib := `DerivedAlgGeoLean)
    (additionalRoots := [`CohLean, `BridgelandStabLean, `BridgelandStability])
    (leanOptions := [("autoImplicit", .bool false),
                     ("relaxedAutoImplicit", .bool false)])
    args
