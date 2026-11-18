"""Run the complete Lean audit without losing its process exit status.

First run `lake build`. This command then audits the resulting imported
library; it does not rebuild or independently check a paper's hypotheses.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys

from check_all_axioms import AuditError, validate_audit


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake", default="lake", help="Lake executable path")
    parser.add_argument("--log", type=Path, default=Path("verification/all-axioms.jsonl"))
    parser.add_argument("--minimum-theorems", type=int, default=741)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    log = args.log if args.log.is_absolute() else root / args.log
    log.parent.mkdir(parents=True, exist_ok=True)
    command = [args.lake, "env", "lean", "scripts/AllAxioms.lean"]
    try:
        with log.open("w", encoding="utf-8", newline="\n") as output:
            process = subprocess.run(command, cwd=root, stdout=output,
                                     stderr=subprocess.STDOUT, check=False,
                                     encoding="utf-8")
    except OSError as exc:
        print(f"Unable to execute Lean audit: {exc}", file=sys.stderr)
        return 1
    if process.returncode != 0:
        print(f"Lean audit exited with status {process.returncode}; see {log}", file=sys.stderr)
        return 1
    try:
        result = validate_audit(log.read_text(encoding="utf-8"), args.minimum_theorems)
    except (AuditError, OSError, UnicodeError) as exc:
        print(f"AXIOM AUDIT FAILED: {exc}", file=sys.stderr)
        return 1
    summary = log.with_suffix(".summary.json")
    summary.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"All {result['theorem_count']} enumerated theorem dependencies passed; log: {log}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
