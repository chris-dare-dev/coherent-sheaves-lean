#!/usr/bin/env python3
"""Assert `.claude/roadmap/*.yaml` still agrees with the GitHub tracker.

Every other `check_*.py` here is offline. This one is not, and that is the
whole difficulty: the roadmap's `gh_issue` / `gh_sub_issues` / `blocked_by`
fields are the only mapping from planning to tracker, and nothing verified them
until this script existed. By then three of eleven epic entries were wrong --
found by hand, not by a gate.

## It reports; it never repairs

The obvious shape is a syncer. That shape is wrong, and #620 records why: when
this file listed #188 under `contract-v1-e9` and GitHub had no parent on #188
at all, the ROADMAP held the correct intent. A syncer treating GitHub as
authoritative would have "fixed" it by deleting #188 -- making the two agree by
discarding the record of where the work belonged.

So every finding names which side is missing what, and the fix is a human
decision about which side was right.

## A check that could not look is not a check that passed

Without `gh`, or without auth, this prints NOT_RUN and says why. It does not
print PASS. `--require-api` turns that into exit 1, and CI passes it: the one
environment guaranteed to have the API must not silently skip. Locally the
default is a degraded report rather than a failure, so a contributor without
`gh` is not blocked from running the other gates.

## Rules

  RM-01  every issue the roadmap references exists on the tracker
  RM-02  an epic's `gh_sub_issues` equals its GitHub children, both ways
  RM-03  a `deliverable`'s GitHub parent is its entry's parent
  RM-04  a `task` is milestone-direct: no GitHub parent, milestone agrees
  RM-05  `blocked_by` mirrors GitHub's blocked-by, on OPEN items
  RM-06  no LIVE issue on a roadmap-owned milestone goes unreferenced
         (live = the issue is open, or its milestone is)

RM-05 is scoped to open items on purpose. A closed item's blockers are history:
#618 was closed as a decision while still marked blocked by #134 and #178, and
re-litigating that in a build gate would be noise, not signal.

RM-06 is the rule the others cannot express. Every one of RM-02..RM-05 checks
something the roadmap already mentions, so an issue the roadmap has never heard
of is invisible to all of them -- which is exactly how #618 sat outside the file
until `kind: task` was added. It is the `C-12` shape, one layer out.

Usage:  python3 scripts/check_roadmap.py [--require-api] [repo_root]
"""

import json
import pathlib
import subprocess
import sys

REPO = "chris-dare-dev/derived-alg-geo-lean"
LEAF_KINDS = ("deliverable", "task")

#: RM-06 gaps that predate this rule's scoping, recorded rather than tolerated
#: silently. THIS LIST MAY ONLY SHRINK: adding to it records a new gap instead
#: of fixing one, and the next reader cannot tell those apart.
#:
#: It was 27 entries for a few hours, and 26 of those were closed issues on
#: CLOSED milestones -- SF0 (33 closed, description "Complete") and DG1 (7
#: closed). Finished work that was never itemized cannot be work the roadmap
#: loses track of, so flagging it bought nothing and cost something: a list
#: reading "27 known gaps" invites being ignored, and #554 -- the one live gap
#: -- was buried in it. See the scoping in RM-06 below, and #639.
RM06_KNOWN_GAPS = {
    554,   # SF8.5, open, on the open SF8 milestone. A real gap: give it a
           # roadmap entry and this list is empty.
}


def fail(rule, detail):
    print(f"FAIL  {rule}  {detail}")


def not_run(reason, require_api):
    print(f"NOT_RUN  scripts/check_roadmap.py -- {reason}")
    print("NOT_RUN is not a pass: nothing was compared.")
    if require_api:
        print("FAIL  --require-api was passed; the API is mandatory here")
        return 1
    return 0


def load_items(root):
    """Every roadmap entry, with the file it came from."""
    try:
        import yaml
    except ImportError:
        return None, "PyYAML is not importable"
    out = []
    for path in sorted((root / ".claude" / "roadmap").glob("*.yaml")):
        doc = yaml.safe_load(path.read_text(encoding="utf-8"))
        if not isinstance(doc, dict):
            continue
        for item in doc.get("items") or []:
            if isinstance(item, dict) and item.get("id"):
                item["_file"] = path.name
                out.append(item)
    return out, None


def fetch_issues():
    """number -> {state, parent, milestone, blocked_by} for the whole tracker."""
    try:
        proc = subprocess.run(
            ["gh", "issue", "list", "--repo", REPO, "--state", "all",
             "--limit", "1000", "--json",
             "number,state,parent,milestone,blockedBy,title"],
            capture_output=True, text=True, timeout=180)
    except (OSError, subprocess.SubprocessError) as exc:
        return None, f"could not run gh: {exc}"
    if proc.returncode != 0:
        return None, f"gh exited {proc.returncode}: {proc.stderr.strip()[:200]}"
    try:
        raw = json.loads(proc.stdout)
    except json.JSONDecodeError as exc:
        return None, f"gh returned unparseable JSON: {exc}"
    return {
        i["number"]: {
            "state": i["state"],
            "title": i["title"],
            "parent": (i.get("parent") or {}).get("number"),
            "milestone": (i.get("milestone") or {}).get("number"),
            "blocked_by": sorted(n["number"]
                                 for n in (i.get("blockedBy") or {}).get("nodes", [])),
        }
        for i in raw
    }, None


def fetch_open_milestones():
    """Milestone numbers whose milestone is still OPEN."""
    try:
        proc = subprocess.run(
            ["gh", "api", f"repos/{REPO}/milestones?state=all&per_page=100",
             "--jq", ".[] | [.number, .state] | @tsv"],
            capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError) as exc:
        return None, f"could not run gh: {exc}"
    if proc.returncode != 0:
        return None, f"gh api milestones exited {proc.returncode}: {proc.stderr.strip()[:200]}"
    open_ms = set()
    for line in proc.stdout.splitlines():
        num, _, state = line.partition("\t")
        if state.strip() == "open":
            open_ms.add(int(num))
    return open_ms, None


def main(argv):
    require_api = "--require-api" in argv
    rest = [a for a in argv if not a.startswith("--")]
    root = pathlib.Path(rest[0]).resolve() if rest else pathlib.Path(__file__).resolve().parent.parent

    items, problem = load_items(root)
    if items is None:
        return not_run(problem, require_api)
    if not items:
        print("FAIL  RM-00  no roadmap items found; this check would pass vacuously")
        return 1

    live, problem = fetch_issues()
    if live is None:
        return not_run(problem, require_api)
    open_milestones, problem = fetch_open_milestones()
    if open_milestones is None:
        return not_run(problem, require_api)

    by_id = {i["id"]: i for i in items}
    failures = 0
    referenced = set()
    for e in items:
        if e.get("gh_issue"):
            referenced.add(e["gh_issue"])
        referenced.update(e.get("gh_sub_issues") or [])

    # RM-01 -----------------------------------------------------------------
    for n in sorted(referenced):
        if n not in live:
            owners = sorted(e["id"] for e in items
                            if e.get("gh_issue") == n or n in (e.get("gh_sub_issues") or []))
            fail("RM-01", f"#{n} is referenced by {', '.join(owners)} but does not exist")
            failures += 1

    # RM-02 -----------------------------------------------------------------
    for e in items:
        if e.get("kind") != "epic" or not e.get("gh_issue"):
            continue
        declared = sorted(e.get("gh_sub_issues") or [])
        actual = sorted(n for n, i in live.items() if i["parent"] == e["gh_issue"])
        for n in sorted(set(actual) - set(declared)):
            fail("RM-02", f"{e['id']}: GitHub parents #{n} to #{e['gh_issue']}, "
                          f"roadmap does not list it -- THE ROADMAP IS STALE")
            failures += 1
        for n in sorted(set(declared) - set(actual)):
            fail("RM-02", f"{e['id']}: roadmap lists #{n}, GitHub does not parent it "
                          f"to #{e['gh_issue']} -- THE TRACKER IS STALE")
            failures += 1

    # RM-03 / RM-04 ---------------------------------------------------------
    for e in items:
        kind = e.get("kind")
        if kind not in LEAF_KINDS or not e.get("gh_issue"):
            continue
        gh = live.get(e["gh_issue"])
        if gh is None:
            continue  # already reported by RM-01
        parent_entry = by_id.get(e.get("parent"))
        if parent_entry is None:
            fail("RM-03" if kind == "deliverable" else "RM-04",
                 f"{e['id']}: parent {e.get('parent')!r} is not an entry in this roadmap")
            failures += 1
            continue
        if kind == "deliverable":
            want = parent_entry.get("gh_issue")
            if gh["parent"] != want:
                fail("RM-03", f"{e['id']}: #{e['gh_issue']} has GitHub parent "
                              f"#{gh['parent']}, entry parent {e['parent']} is #{want}")
                failures += 1
        else:
            if gh["parent"] is not None:
                fail("RM-04", f"{e['id']}: #{e['gh_issue']} is a task but GitHub parents "
                              f"it to #{gh['parent']}; a task is milestone-direct")
                failures += 1
            want_ms = parent_entry.get("gh_milestone")
            if gh["milestone"] != want_ms:
                fail("RM-04", f"{e['id']}: #{e['gh_issue']} is on milestone "
                              f"{gh['milestone']}, entry parent {e['parent']} is "
                              f"milestone {want_ms}")
                failures += 1

    # RM-05 -----------------------------------------------------------------
    for e in items:
        n = e.get("gh_issue")
        if not n or n not in live or live[n]["state"] != "OPEN":
            continue
        declared = sorted(e.get("blocked_by") or [])
        actual = live[n]["blocked_by"]
        if declared != actual:
            fail("RM-05", f"{e['id']}: #{n} blocked_by roadmap={declared} "
                          f"github={actual}")
            failures += 1

    # RM-06 -----------------------------------------------------------------
    owned = {e["gh_milestone"] for e in items
             if e.get("kind") == "milestone" and e.get("gh_milestone")}
    #
    # SCOPED TO WHERE THE ROADMAP CAN STILL LOSE SOMETHING: an issue is only a
    # finding when the issue is open, or its milestone is. A closed issue on a
    # closed milestone is finished work that was never itemized -- it cannot go
    # missing, and flagging it drowns the live gaps. #639 measured the
    # difference: 27 findings before, 1 after, and the 1 was invisible inside
    # the 27.
    known_hit = set()
    for n, i in sorted(live.items()):
        if i["milestone"] not in owned or n in referenced:
            continue
        if i["state"] != "OPEN" and i["milestone"] not in open_milestones:
            continue
        if n in RM06_KNOWN_GAPS:
            known_hit.add(n)
            continue
        fail("RM-06", f"#{n} is on milestone {i['milestone']}, which this roadmap "
                      f"owns, but no entry references it -- {i['title'][:56]}")
        failures += 1

    # Stale entries in the allowlist are themselves a finding: a gap that was
    # closed leaves a number behind that makes the backlog look larger than it
    # is, and the list is supposed to burn down visibly.
    for n in sorted(RM06_KNOWN_GAPS - known_hit):
        fail("RM-06", f"#{n} is in RM06_KNOWN_GAPS but is no longer an unreferenced "
                      f"issue on an owned milestone -- remove it from the list")
        failures += 1

    files = sorted({e["_file"] for e in items})
    print(f"checked {len(items)} entries across {len(files)} file(s): {', '.join(files)}")
    print(f"        {len(referenced)} issue(s) referenced, {len(owned)} milestone(s) owned")
    if known_hit:
        print(f"        RM-06: {len(known_hit)} known gap(s) still open "
              f"(this number must go down, never up)")
    if failures:
        print(f"FAIL  {failures} finding(s). Each names which side is stale; "
              f"decide which was right, then fix that side.")
        return 1
    print("ok: roadmap and tracker agree")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
