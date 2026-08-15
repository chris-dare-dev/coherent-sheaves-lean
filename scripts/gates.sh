#!/usr/bin/env bash
# The pre-push gate list from CONTRIBUTING.md, as one command.
#
# An unattended formalization loop needs a single exit code to branch on, and it
# needs the gates in cheapest-first order so a failure is reported in two minutes
# rather than forty. Every gate below also runs in `.github/workflows/ci.yml`,
# with ONE deliberate exception: `workflows`. That one cannot be a CI gate,
# because a workflow file too invalid to parse is also too invalid to run the
# job that would have checked it -- GitHub just fails a run named after the file
# and reports no checks at all. It has to fire before the file reaches GitHub,
# which means here. See scripts/check_workflows.sh.
#
#   scripts/gates.sh fast   build + style + axiom audits          (~minutes)
#   scripts/gates.sh        everything CI runs, in CI's order
#
# Each gate prints `GATE <name>: pass|FAIL`. The script does not stop at the
# first failure -- an unattended run wants the whole picture in one pass -- and
# exits 1 if any gate failed.

set -uo pipefail
cd "$(dirname "$0")/.."

MODE="${1:-full}"
FAILED=()

gate() {
  local name="$1"; shift
  local log
  log="$(mktemp)"
  if "$@" >"$log" 2>&1; then
    echo "GATE $name: pass"
  else
    echo "GATE $name: FAIL"
    echo "--- last 40 lines of $name ---"
    if [ -s "$log" ]; then
      tail -40 "$log"
    else
      # A gate whose body redirects its own output leaves this empty. An
      # unattended run then reports a failure with no reason, which is worse
      # than the failure: say so rather than printing nothing.
      echo "(no output captured -- this gate redirects internally;"
      echo " check /tmp/${name%%-*}-*.txt or run the command directly)"
    fi
    echo "--- end $name ---"
    FAILED+=("$name")
  fi
  rm -f "$log"
}

algebraic_geometry_audit() {
  # The algebraic-geometry audit imports development probes and dimension
  # specializations, none of which the default target reaches -- `lake build`
  # builds DerivedAlgGeo, and the umbrella does not import the probes. CI builds
  # them explicitly before the audit; so must this, or the gate fails with a
  # missing-olean error in any tree where they were not already built by hand.
  lake build DerivedAlgGeo.Development \
    DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface \
    DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Threefold \
    DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Fourfold || return 1
  lake env lean scripts/AlgebraicGeometryAudit.lean > /tmp/algebraic-geometry-audit.txt 2>&1 || {
    # Show the reason: this function redirects its own output, so without this
    # the wrapper's log is empty and the gate fails silently.
    tail -20 /tmp/algebraic-geometry-audit.txt
    return 1
  }
  grep -q 'sorryAx' /tmp/algebraic-geometry-audit.txt && { echo "sorryAx reached the audit"; return 1; }
  return 0
}

dg_audit() {
  lake env lean scripts/DGCategoryAudit.lean > /tmp/dg-audit.txt 2>&1 || {
    tail -20 /tmp/dg-audit.txt
    return 1
  }
  python3 scripts/check_audit.py /tmp/dg-audit.txt scripts/DGCategoryAudit.lean
}

audit_complete() {
  # The other direction from check_audit.py: a new public declaration nobody
  # listed. Needs the same prerequisite build as coh_audit, because the sweep
  # imports Development and the dimension specializations.
  lake build DerivedAlgGeo.Development \
    DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Surface \
    DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Threefold \
    DerivedAlgGeo.AlgebraicGeometry.Numerical.Specializations.Fourfold || return 1
  lake env lean scripts/EnumDecls.lean > /tmp/enum-decls.txt 2>&1 || {
    tail -20 /tmp/enum-decls.txt
    return 1
  }
  python3 scripts/check_audit_complete.py /tmp/enum-decls.txt
}

stability_condition_audit() {
  lake env lean scripts/StabilityConditionAudit.lean > /tmp/stability-condition-audit.txt 2>&1 || {
    tail -20 /tmp/stability-condition-audit.txt
    return 1
  }
  python3 scripts/check_audit.py /tmp/stability-condition-audit.txt
}

exe_sorry() {
  # The one file the emitter cannot cover: an `lean_exe` root is not part of the
  # environment built from its own imports. CI runs the same loop; see the
  # "No declaration uses sorry" step in .github/workflows/ci.yml.
  local log=/tmp/exe-sorry-check.txt
  : > "$log"
  for f in exe/*.lean; do
    lake env lean "$f" >> "$log" 2>&1 || { tail -20 "$log"; return 1; }
  done
  if grep -q "declaration uses 'sorry'" "$log"; then
    echo "a declaration uses sorry"
    return 1
  fi
  return 0
}

changed_lean_files() {
  # `origin/main`, not `main`: the local `main` in this clone is hundreds of
  # commits stale, and diffing against it would hand every gate the whole
  # library instead of the branch's own changes.
  git diff --name-only origin/main...HEAD -- '*.lean'
  git diff --name-only -- '*.lean'
}

mathlib_style() {
  local files
  files="$(changed_lean_files | sort -u)"
  [ -z "$files" ] && return 0
  # --diff-only: judge the lines this branch wrote, not the pre-existing debt in
  # a file it happens to touch. The edit hook stays strict on what you just
  # typed; a branch gate that demanded you also refactor everything around it
  # would make touching any legacy file an unbounded task.
  # shellcheck disable=SC2086
  python3 scripts/check_mathlib_style.py --diff-only origin/main $files
}

echo "== gates ($MODE) =="

# First because it is the cheapest gate here by three orders of magnitude
# (~100ms against minutes) and because it is the one whose failure is otherwise
# invisible: an invalid workflow does not produce a red check, it produces no
# checks. In `fast` mode too, for the same reason.
gate workflows scripts/check_workflows.sh
gate mathlib-style mathlib_style
gate build lake build
gate algebraic-geometry-audit algebraic_geometry_audit
gate stability-condition-audit stability_condition_audit
gate dg-audit dg_audit

if [ "$MODE" != "fast" ]; then
  gate runLinter lake exe runLinter DerivedAlgGeo
  gate nolints-ratchet python3 scripts/check_nolints.py
  gate lint-style lake exe lint-style
  gate pin python3 scripts/check_pin.py
  gate source-independence python3 scripts/check_source_independence.py
  gate coverage-map python3 scripts/check_coverage_map.py
  gate audit-complete audit_complete
  gate emit-build lake build emit
  gate emit lake exe emit --out /tmp/derived-alg-geo-emission.json
  # The emit gate above is the repository-wide sorry gate. This one checks that
  # it swept everything -- without it, a library root nobody imported into
  # DerivedAlgGeoSweep.lean drops out of coverage with every gate still green.
  gate emission-coverage python3 scripts/check_emission_coverage.py \
    /tmp/derived-alg-geo-emission.json
  gate exe-sorry exe_sorry
fi

echo
if [ ${#FAILED[@]} -eq 0 ]; then
  echo "all gates passed ($MODE)"
  exit 0
fi
echo "FAILED: ${FAILED[*]}"
exit 1
