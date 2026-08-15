---
name: land-pr
description: Run one unattended landing iteration — take the base of the open PR stack, rebase it, gate it locally, review it, push fixes, mark it ready, then stop. Never merges. Pair with /loop.
---

# One landing iteration

The open PR queue, not the issue tracker, is where this repository's work is
stuck. This is **one** iteration against that queue and it **halts** before the
merge. Merging is a human action, always.

## What the queue actually is

Every open PR is based on `main`, but they are a **cumulative stack**: each
slice contains all of its predecessors, so diffs run +65, +134, +168, … +2925
along one chain. Two consequences drive everything below:

- **Land the base, not the tip.** Merging the tip would land 26 issues in one
  unreviewable commit. Merging the base makes the next PR's diff collapse to its
  own slice.
- **The queue is CI-bound, not review-bound.** One 90-minute build job serialises
  28 PRs. Local gates answer the same question in minutes, so never wait on
  GitHub CI — gate locally and let CI confirm afterwards.

## 0a. This skill needs its own tooling on `main`

`gh pr checkout` puts you on a branch cut before this tooling existed, so
`scripts/gates.sh`, `scripts/check_mathlib_style.py`, and the edit hook are all
absent there until the tooling commit is on `main` and the PR has been rebased.

Check first:

```bash
git ls-tree origin/main --name-only scripts/gates.sh
```

Empty output? Stop: land the tooling PR before running this loop. Running the
gates from another branch's copy works for a one-off dry run but leaves the
branch's own edits ungated, which is the opposite of the point.

## 0. Refuse to start if the tree is dirty

```bash
git status --porcelain
```

Non-empty? **Stop and report.** Do not stash. The previous iteration did not
finish, and a human decides what happens to its work.

## 1. Pick the target

```bash
git fetch origin
python3 scripts/pr_queue.py
```

Take the **first row**. The ranking already encodes the landing order: `READY`
before `GATE` before `FIX` before `CONFLICT`, then smallest diff first.

Never take a row out of order to find easier work — the stack means a later PR's
diff is a lie until its predecessors land.

If the first row is `CONFLICT`, that is the iteration: rebase it, resolve, gate,
push, and halt.

**Exit code 2 means stop the loop, and it means two different things.** The
script prints which:

- `BLOCKED ON YOU` — every open PR is already gated and reviewed at its current
  head, and is waiting on a human to merge. **Stop the loop** and say so, naming
  the PRs and the count. Do not re-review an unchanged head: the verdict is
  already posted and repeating it costs a full build to say nothing. This is the
  failure mode worth naming out loud, because a loop that reports "nothing to
  do" when the real answer is "eleven PRs need you" has failed silently — the
  two look identical from the outside.
- `QUEUE DRAINED` — there are genuinely no open PRs needing an iteration. Stop
  the loop and say that instead.

Either way the loop ends. It restarts the moment a merge or a new push changes
the queue, and that is the human's cue, not a reason to keep waking up.

## 2. Check out and rebase

```bash
gh pr checkout <N> -R chris-dare-dev/derived-alg-geo-lean || exit 1
git rebase origin/main
```

**The `|| exit 1` is load-bearing.** If the checkout fails, `git rebase
origin/main` rebases whatever branch you happen to be standing on — which is
not the PR, and may be unmerged work. Never run the two as separate steps that
both execute regardless.

**This repository uses ~22 git worktrees**, and `gh pr checkout` fails outright
when the PR's branch is checked out in one of them:

> fatal: 'agent/…' is already used by worktree at '…'

That is not a reason to skip the PR. Find the worktree and run the whole
iteration there instead:

```bash
git worktree list | grep '\[agent/<branch>\]'
```

Two things to check before working in someone else's worktree:

- **It must be clean.** A dirty worktree is unfinished human work — halt and
  report, exactly as in step 0. Never stash it.
- **Its `.lake/packages` is often a symlink to a sibling worktree**, and those
  siblings get deleted. A dangling symlink shows up as a baffling
  `mkdir: .lake/packages: No such file or directory` from `lake build` even
  though `.lake` plainly exists. Check with `ls -la .lake`, and repoint it at
  the main checkout's packages when it dangles:

  ```bash
  ls -d "$(readlink .lake/packages)" 2>/dev/null || {
    rm .lake/packages
    ln -s /Users/chris.dare/Personal/SourceCode/coherent-sheaves-lean/.lake/packages .lake/packages
  }
  ```

  Only do this once `lean-toolchain` and `lakefile.toml` are identical to
  `origin/main`, which after step 2's rebase they are. Sharing a package set
  across differing pins would be silent corruption, not a repair.

A conflict here is normal for a stacked queue and is your work to resolve. Resolve
it in favour of `origin/main` for anything outside this slice's own leaf path —
a stacked branch carrying a stale copy of an earlier slice is the usual cause.

If the rebase cannot be resolved without guessing at mathematical intent, abort
it (`git rebase --abort`), comment on the PR with the exact conflicting hunks,
and halt. Do not guess.

## 3. Gate locally

```bash
scripts/gates.sh fast   # build, style, both axiom audits — minutes
scripts/gates.sh        # everything CI runs, once fast is green
```

A failing gate is the iteration's work, not a reason to weaken the gate. The
usual failures on this queue, in order of frequency:

- a new public theorem missing from `scripts/StabilityConditionAudit.lean`,
  `scripts/AlgebraicGeometryAudit.lean`, or `scripts/DGCategoryAudit.lean`;
- `check_source_independence.py` rejecting a retired or external source root;
- convention errors the edit hook would have caught had the branch been written
  with it installed. Fix them; they are one-line fixes.

Never introduce a `sorry` to get a gate green. If the branch already contains
one, that is a `NEEDS REWORK` verdict, not something to work around.

## 4. Review

Run the `mathlib-reviewer` agent over `git diff origin/main...HEAD`. Apply its
`blocker` and `should-fix` findings yourself when they are mechanical — a name
that does not transcribe its statement, a docstring that restates the signature.
Leave anything requiring mathematical judgement for the PR comment.

## 5. Push and report

```bash
git push --force-with-lease
gh pr comment <N> -R chris-dare-dev/derived-alg-geo-lean --body "<verdict>"
```

The verdict comment states, in this order: which gates passed locally and at
what commit, what you fixed, what you left for a human and why, and the
reviewer's verdict with finding counts by severity.

If the PR is a draft and every gate passed and the reviewer said `MERGE`:

```bash
gh pr ready <N> -R chris-dare-dev/derived-alg-geo-lean
```

## 6. Halt

Return to a detached-free clean state on `origin/main`. If the iteration ran in
another worktree, leave that worktree on its own branch and clean — do not
switch it to `main`, since a human may be using it. Report three lines: the
PR touched, its new state, and the one thing a human must decide.

**Do not merge. Do not start the next PR.** The next iteration re-reads the
queue, which is the point: once a human merges the base, the rest of the stack
shrinks and the ranking changes underneath you.
