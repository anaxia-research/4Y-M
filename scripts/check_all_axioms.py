"""Validate the complete Lean theorem-dependency audit; fail closed.

The log must come from a successful Lean invocation. Prefer the subprocess
runner in run_all_axioms.py, which checks Lean's exit status before parsing.
Counts include generated/private theorem declarations and may exceed source
counts of `theorem`/`lemma` keywords. This checks proof dependencies, not the
truth of a conditional theorem's hypotheses or completeness of a manuscript.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

PREFIX = "YM_AXIOM_AUDIT "
SCHEMA = "yang-mills-axiom-audit-v1"
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})


class AuditError(ValueError):
    """Malformed, incomplete, or inadmissible Lean audit."""


def _count(value: object, field: str) -> int:
    if type(value) is not int or value < 1:
        raise AuditError(f"{field} must be a positive integer")
    return value


def validate_audit(text: str, minimum_theorems: int = 741) -> dict[str, object]:
    """Require one complete report with one entry per enumerated theorem."""
    if "sorryAx" in text:
        raise AuditError("An admitted proof dependency (sorryAx) was detected")
    # Even if an external shell loses Lean's exit code, do not silently accept
    # a log containing Lean error diagnostics.
    if re.search(r"(?:^|\n).*\berror:\s", text, flags=re.IGNORECASE):
        raise AuditError("The log contains a Lean error diagnostic")
    records: list[dict[str, object]] = []
    for number, line in enumerate(text.splitlines(), 1):
        if PREFIX not in line:
            continue
        if not line.startswith(PREFIX):
            raise AuditError(f"Malformed audit marker at line {number}")
        try:
            record = json.loads(line[len(PREFIX):])
        except json.JSONDecodeError as exc:
            raise AuditError(f"Invalid audit JSON at line {number}") from exc
        if not isinstance(record, dict):
            raise AuditError(f"Audit entry at line {number} is not an object")
        records.append(record)
    if len(records) < 3:
        raise AuditError("Missing audit header, theorem records, or completion footer")
    header, *theorems, footer = records
    if header.get("kind") != "begin" or header.get("schema") != SCHEMA:
        raise AuditError("Missing or incompatible audit header")
    if footer.get("kind") != "end" or footer.get("schema") != SCHEMA:
        raise AuditError("Missing or incompatible audit completion footer")
    expected = _count(header.get("expected_count"), "expected_count")
    checked = _count(footer.get("checked_count"), "checked_count")
    if expected != checked or len(theorems) != expected:
        raise AuditError(
            f"Incomplete coverage: header={expected}, footer={checked}, "
            f"theorem records={len(theorems)}")
    if expected < minimum_theorems:
        raise AuditError(
            f"Only {expected} theorems audited; at least {minimum_theorems} required")
    seen: set[str] = set()
    union: set[str] = set()
    for entry in theorems:
        if entry.get("kind") != "theorem":
            raise AuditError("Unexpected or repeated header/footer inside theorem records")
        name, user_name, axioms = (
            entry.get("declaration"), entry.get("user_name"), entry.get("axioms"))
        if not isinstance(name, str) or not name or name in seen:
            raise AuditError("Missing, empty, or duplicate theorem declaration")
        if not isinstance(user_name, str) or not user_name.startswith("YangMills."):
            raise AuditError(f"Theorem outside the YangMills user namespace: {name}")
        if not isinstance(axioms, list) or any(not isinstance(x, str) for x in axioms):
            raise AuditError(f"Malformed axiom dependency list for {name}")
        if len(axioms) != len(set(axioms)):
            raise AuditError(f"Duplicate axiom dependency for {name}")
        unexpected = set(axioms) - ALLOWED_AXIOMS
        if unexpected:
            raise AuditError(f"Unexpected proof dependencies for {name}: "
                             + ", ".join(sorted(unexpected)))
        seen.add(name)
        union.update(axioms)
    return {"schema": SCHEMA, "theorem_count": expected,
            "axioms": sorted(union), "status": "passed"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path)
    parser.add_argument("--minimum-theorems", type=int, default=741,
                        help="minimum expected theorem count (default: current 741 source declarations)")
    parser.add_argument("--json-output", type=Path)
    args = parser.parse_args()
    if args.minimum_theorems < 1:
        parser.error("--minimum-theorems must be positive")
    try:
        result = validate_audit(args.log.read_text(encoding="utf-8-sig"), args.minimum_theorems)
    except (AuditError, OSError, UnicodeError) as exc:
        print(f"AXIOM AUDIT FAILED: {exc}", file=sys.stderr)
        return 1
    if args.json_output:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"All {result['theorem_count']} enumerated theorems use only permitted standard axioms.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
