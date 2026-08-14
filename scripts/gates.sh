#!/usr/bin/env bash
# The pre-push gate list from CONTRIBUTING.md, as one command.
#
# An unattended formalization loop needs a single exit code to branch on, and it
# needs the gates in cheapest-first order so a failure is reported in two minutes
# rather than forty. Nothing here is new policy: every gate already runs in
# `.github/workflows/ci.yml`.
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
    tail -40 "$log"
    echo "--- end $name ---"
    FAILED+=("$name")
  fi
  rm -f "$log"
}

coh_audit() {
  lake env lean scripts/Audit.lean > /tmp/coh-audit.txt 2>&1 || return 1
  ! grep -q 'sorryAx' /tmp/coh-audit.txt
}

bridgeland_audit() {
  lake env lean scripts/BridgelandAudit.lean > /tmp/bridgeland-audit.txt 2>&1 || return 1
  python3 scripts/check_audit.py /tmp/bridgeland-audit.txt
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

gate mathlib-style mathlib_style
gate build lake build
gate coh-audit coh_audit
gate bridgeland-audit bridgeland_audit

if [ "$MODE" != "fast" ]; then
  gate runLinter-foundation lake exe runLinter BridgelandStability
  gate runLinter-stability lake exe runLinter BridgelandStabLean
  gate runLinter-coh lake exe runLinter CohLean
  gate nolints-ratchet python3 scripts/check_nolints.py
  gate lint-style lake exe lint-style
  gate pin python3 scripts/check_pin.py
  gate anchor-free python3 scripts/check_anchor_free.py
  gate coverage-map python3 scripts/check_coverage_map.py
  gate emit-build lake build emit
  gate emit lake exe emit --out /tmp/derived-alg-geo-emission.json
fi

echo
if [ ${#FAILED[@]} -eq 0 ]; then
  echo "all gates passed ($MODE)"
  exit 0
fi
echo "FAILED: ${FAILED[*]}"
exit 1
