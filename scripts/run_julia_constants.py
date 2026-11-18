"""Run the legacy Julia constant checks and turn printed failures into failure.

Run from any directory:
    python scripts/run_julia_constants.py --julia /path/to/julia

The script checks finite numerical calculations; it does not certify a
weak-coupling Wilson estimate or the Yang--Mills continuum mass gap.
"""
from pathlib import Path
import argparse
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


class VerificationFailure(RuntimeError):
    """The Julia process did not provide a successful complete check run."""


def validate_output(returncode: int, output: str) -> int:
    """Return the number of OK lines, rejecting failed or empty runs."""
    if returncode != 0:
        raise VerificationFailure(f"Julia exited with status {returncode}")
    failures = [line for line in output.splitlines() if re.search(r"\bFAIL\b", line)]
    if failures:
        raise VerificationFailure(f"{len(failures)} printed Julia check(s) failed")
    passed = sum(bool(re.search(r"\bOK\s*$", line)) for line in output.splitlines())
    if not passed:
        raise VerificationFailure("Julia reported no successful constant checks")
    return passed


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--julia", default="julia", help="Julia executable")
    parser.add_argument("--output", type=Path, help="Optional captured UTF-8 log")
    args = parser.parse_args(argv)
    command = [args.julia, "--startup-file=no", "--history-file=no",
               str(ROOT / "julia" / "constants.jl")]
    try:
        result = subprocess.run(command, cwd=ROOT, text=True, encoding="utf-8",
                                errors="replace", stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, check=False)
    except OSError as exc:
        print(f"FAIL: could not start Julia: {exc}", file=sys.stderr)
        return 1
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(result.stdout, encoding="utf-8")
    sys.stdout.write(result.stdout)
    try:
        passed = validate_output(result.returncode, result.stdout)
    except VerificationFailure as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1
    print(f"PASS: {passed} Julia constant checks; no printed failures.")
    return 0


if __name__ == "__main__":
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    raise SystemExit(main())
