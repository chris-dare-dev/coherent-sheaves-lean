---
project: coherent-sheaves-lean
type: contributing
status: active
authorship: agent-generated
tags:
- project/coherent-sheaves-lean
- type/contributing
- authorship/agent-generated
---

# Contributing to CohLean

This file is the whole of what a fresh session — human or agent — needs in order to work
this repo correctly. You should not have to read the commit history to get a change right.

Read [README.md](README.md) for what the library is and [ROADMAP.md](ROADMAP.md) for what
is left to do. Work is tracked as
[milestones and issues](https://github.com/chris-dare-dev/coherent-sheaves-lean/issues);
issues labelled `ready` have no unmet dependency and can be started immediately.

## Namespaces

Declarations go in **Mathlib-style namespaces** — `AlgebraicGeometry`,
`AlgebraicGeometry.Numerical`, and so on. Never `CohLean.*`.

`CohLean` is the *package* name and the module-path root; it is not a namespace and no
declaration may live inside one. The reason is upstreaming: Layer B is written to be
contributed to Mathlib a stage at a time, and a stage that already sits in
`AlgebraicGeometry` goes up as a file move. A stage in `CohLean.Coh` goes up as a rename
touching every reference, which is the kind of diff that does not get reviewed.

Follow Mathlib naming for declarations too (`snake_case` for theorems named after their
statement, `UpperCamelCase` for types and classes, `lowerCamelCase` for definitions), and
give every file a module docstring with a `#` header, a summary, and references.

## No `sorry`

There is no `sorry` in this library and there should never be one.

Work that is not done is written up as **not done in the module docstring** of the file it
belongs to, in prose, saying what is missing and what it is waiting on. It is not stubbed
with a `sorry`, a `native_decide`, or an axiom.

This is not fastidiousness. Layer A is an *axiomatic interface* whose entire claim is that
its trust boundary is exactly the fields of `NumericalVariety` and nothing else. One
`sorry` anywhere downstream of that and the claim is false, silently, in a way that
`lake build` will not tell you about — `sorry` is a warning, not an error, so a green build
proves nothing on its own. Hence the audit.

## The audit

`scripts/Audit.lean` is the gate. **Every new public theorem goes in it**, in the section
for its layer, in the order the file introduces it.

```bash
lake build && lake env lean scripts/Audit.lean
```

Every line must print either `does not depend on any axioms` or exactly
`[propext, Classical.choice, Quot.sound]`. Anything else is a failure to investigate before
you push — in particular `sorryAx`, which means a listed declaration is backed by a hole.

CI enforces two separate things, and you need both:

1. **Axiom audit.** Runs `scripts/Audit.lean` and fails on `sorryAx`. This catches a hole
   under a declaration you *did* list.
2. **No declaration uses sorry.** Re-elaborates every tracked `.lean` file outside
   `scripts/` and fails on the `declaration uses 'sorry'` warning. This catches a hole in a
   declaration you did *not* list, including one reached through a macro. It re-elaborates
   rather than grepping the sources, so a docstring that discusses the word "sorry" — there
   is one in `CohLean/Coh/Defs.lean` — does not trip it.

Check 2 exists because check 1 only sees what you remembered to add. Adding your theorem to
the audit is still the rule: check 2 tells you a hole exists, check 1 is what pins the
axiom set of the results anyone downstream depends on.

## The trust boundary

`NumericalVariety`'s fields are **axioms**, not theorems. That includes `rank`, `chComp`,
`toddComp`, `chi` and their laws, and above all `hirzebruch_riemannRoch`:

```lean
hirzebruch_riemannRoch : ∀ E : N,
  (chi E : ℚ) = degree ((∑ i ∈ Finset.range (n + 1), chComp E i) *
    (∑ j ∈ Finset.range (n + 1), toddComp j))
```

They are visible in the type of the class, which is the point — the assumption is stated,
not hidden in a hole. Layer B (`CohLean.Coh`) exists to discharge them from Mathlib's
scheme theory; until it does, they are assumed.

Two rules follow, and neither is negotiable:

* **Nothing downstream of `CohLean/Numerical/Defs.lean` may treat these fields as proved.**
  Consuming them is fine and is what the interface is for. Asserting anywhere — in a
  docstring, a README, a commit message, a PR description — that Riemann–Roch is *proved*
  in this repo is not.
* **No new axiom may be added to Layer A** without a line in [ROADMAP.md](ROADMAP.md)
  naming the Layer B stage that will discharge it. An axiom with no discharge plan is a
  permanent hole wearing a different hat.

The counterweight to an axiomatic interface is models. `Numerical/Examples/Point.lean`
(dimension zero) and `Numerical/Examples/K3Model.lean` (a K3 surface of degree `H² = 2d`)
both satisfy the axioms, so nothing in Layer A is vacuously true. If you add axioms, check
they still hold in the models — and if a model gets a new instance, audit it.

## Toolchain

Pinned to **`leanprover/lean4:v4.29.0`**, matching `bridgeland-stab-lean` and `bstab`, both
of which are intended to `require` this package. That is the whole reason for the pin: a
bump here forces a bump in two downstream repos, so it needs a reason.

The first real reason is Layer B stage 2, the divisor work, which wants upstream
`Mathlib/AlgebraicGeometry/AlgebraicCycle/` and `OrderOfVanishing.lean` — both landed after
v4.29.0. Do not bump before then.

When the bump does happen, four things move together:

1. `lean-toolchain`
2. the `mathlib` `rev` in `lakefile.toml`
3. the `doc-gen4` `rev` in `docbuild/lakefile.toml` — it must match the toolchain
4. the toolchain pin in `bridgeland-stab-lean` and `bstab`

## One file per issue

Issues in this repo name the exact file they create. That is what lets several `ready`
issues run in parallel sessions without a merge conflict, and it only works if everyone
keeps to it.

* Create the file your issue names. Do not opportunistically refactor a file another issue
  owns, even if the fix is obvious — open an issue for it instead.
* **`lakefile.toml` is the one genuinely shared file.** Coordinate before touching it. This
  is also why `doc-gen4` lives in the nested `docbuild/` package rather than in a
  `[[require]]` block at the top level: it keeps the docs work off the shared file, and it
  keeps every downstream package that requires `CohLean` from having to fetch a
  documentation generator it will never run.
* Add your new module to the `import` list in `CohLean.lean` and your new theorems to
  `scripts/Audit.lean`. These two files are append-only in practice, so concurrent
  additions merge cleanly; adding at the end of the relevant section keeps it that way.

## Before you push

1. `lake build` — clean.
2. `lake env lean scripts/Audit.lean` — no `sorryAx`, no unexpected axioms.
3. Your new theorems are in `scripts/Audit.lean`; your new module is imported from
   `CohLean.lean`.
4. Your file has a module docstring with a header, a design note, and references, and says
   what it does *not* do.
5. Commit message closes the issue it implements (`closes #N`).

## Docs

API documentation is generated by `doc-gen4` from the nested `docbuild/` package and
published to GitHub Pages on every push to `main`. To build it locally:

```bash
lake build && cd docbuild && lake build CohLean:docs
```

The result is `docbuild/.lake/build/doc/index.html`. Serve it over HTTP rather than opening
the file directly — the same-origin policy breaks the search and navigation otherwise:

```bash
python3 -m http.server -d docbuild/.lake/build/doc
```

`docbuild` shares the parent's `.lake/packages`, so it reuses the Mathlib build you already
have and does not re-download anything.
