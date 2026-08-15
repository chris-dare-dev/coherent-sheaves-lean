---
name: formalize-issue
description: Run one unattended formalization iteration — claim a ready GitHub issue, formalize it on a branch, run the gates, open a PR, then stop. Use for hands-off sessions; pair with /loop for repeats.
---

# One formalization iteration

This is **one** iteration and it **halts** at the PR. It never merges, never
pushes to `main`, and never leaves a `sorry` behind. Under `/loop` it will be
re-entered from a clean state, so everything below must be safe to re-run.

Issues live on `chris-dare-dev/derived-alg-geo-lean`.

## 0. Refuse to start if the tree is dirty

```bash
git status --porcelain
```

Non-empty, or the current branch is not `main`? **Stop and report.** Do not
stash, do not commit stray work, do not switch branches over uncommitted
changes. A dirty tree means the previous iteration did not finish; a human
decides what happens to it.

## 1. Claim an issue

```bash
gh issue list -R chris-dare-dev/derived-alg-geo-lean --state open \
  --limit 40 --json number,title,labels,body
```

Pick the **first** eligible issue, preferring the lowest number — the tracker is
ordered by dependency, not priority. Eligible means, in order of preference:

1. labelled `ready`;
2. otherwise unlabelled or plainly-labelled implementation work.

Never eligible: anything labelled `blocked`, `epic`, `type:spike`, or
`research`. Those are coordination or investigation items, not one-sitting
formalizations. Also skip any issue whose named leaf path already exists with
the theorem proved.

**Never eligible, and this is the one that actually bites:** an issue that
already has an open PR or an existing `agent/` branch. At the time of writing,
28 of the 30-odd open implementation issues were already in flight, so an
iteration that skips this check will silently redo finished work. Compute the
exclusion before choosing:

```bash
gh pr list -R chris-dare-dev/derived-alg-geo-lean --state open --limit 200 \
  --json number,headRefName,body \
  --jq '.[] | "\(.headRefName)\t\(.body)"' | grep -oiE '(closes|fixes|resolves) #[0-9]+'
git branch -a --list 'agent/*'
```

If every eligible issue is already claimed, **stop and say so.** The bottleneck
is review, not formalization; report the open-PR count and halt. Do not pick a
claimed issue, and do not invent work.

Most open issues carry no `ready` label today, so do not filter on it with
`--label`; read the labels and decide.

If nothing is ready, stop and say so. Do not invent work.

Post a claim comment so a parallel session does not take the same issue:

```bash
gh issue comment <N> -R chris-dare-dev/derived-alg-geo-lean \
  --body "Claimed by an unattended formalization run at $(date -u +%FT%TZ)."
```

## 2. Branch

```bash
git switch main && git pull --ff-only
git switch -c agent/<short-slug-from-the-issue-title>
```

## 3. Formalize

Read `CLAUDE.md` and `.claude/references/mathlib-style.md` before writing Lean.
The rules that bite most often in unattended runs:

- **No `sorry`, ever** — not even temporarily, not even in a file you intend to
  finish this iteration. The edit hook blocks it. If the proof will not close,
  that is a step-5 outcome, not something to paper over.
- One issue owns one leaf path. Do not refactor an unrelated subsystem because
  you noticed something; note it for step 6 instead.
- Foundational subject modules must remain independent of specialized consumers.
- Export the new leaf through its nearest subsystem umbrella.
- Add every new public theorem to `scripts/AlgebraicGeometryAudit.lean`,
  `scripts/StabilityConditionAudit.lean`, or `scripts/DGCategoryAudit.lean`.
- Write the module docstring and declaration docstrings **as you go**, to the
  standard in the style reference: say why the hypothesis is needed and what the
  proof idea is, not what the signature already says.

The `PostToolUse` hook runs `scripts/check_mathlib_style.py` after every edit
and blocks on convention errors. Fix them immediately; do not batch them.

**Budget the iteration.** If the proof has not closed after roughly 45 minutes
of work, or you are on the third distinct proof strategy, go to step 5 and
report the obstruction. A well-written obstruction report is a successful
iteration. Grinding is not.

## 4. Gates

```bash
scripts/gates.sh fast
```

Then, only once `fast` is green:

```bash
scripts/gates.sh
```

Every gate must pass. A failing gate is not a reason to weaken the gate.

## 5. If it did not close

Do not open a PR. Do not leave the branch half-committed.

```bash
git switch main
git branch -D agent/<slug>          # only if nothing worth keeping
```

Comment on the issue with: the statement you tried to prove (verbatim Lean), the
strategies attempted, the exact goal state you got stuck on, and what Mathlib
lemma you looked for and could not find. Then **stop the iteration**.

## 6. PR

```bash
git add <only the files this change owns>   # inspect `git status` first
git commit -m "feat: <what was proved>

Closes #<N>."
git push -u origin agent/<slug>
gh pr create -R chris-dare-dev/derived-alg-geo-lean --fill
```

Then run the `mathlib-reviewer` agent on the branch diff and post its findings
as a PR comment. If it returns `NEEDS REWORK`, fix the findings and re-run the
gates before halting — the point of a hands-off run is that the PR is reviewable
when the human returns, not that it exists.

Finally, if step 3 turned up unrelated work worth doing, file it as its own
issue now.

## 7. Halt

Return to `main`. Report in three lines: the issue closed, the PR URL, and the
reviewer verdict. Do not start another issue.
