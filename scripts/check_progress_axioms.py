"""Reject proof dependencies beyond Lean's standard mathematical axioms."""
from pathlib import Path
import re
import sys

source = Path(sys.argv[1]).read_text(encoding="utf-8")
reports = re.findall(
    r"'(YangMills\.ErrorStableAscent\.[A-Za-z0-9_]+)' "
    r"(?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)",
    source, re.S)
expected = {"dyadic_power_succ", "variable_budget_ascent", "error_stable_ascent",
            "rescale_recurrence", "scaled_error_stable_ascent",
            "exponential_error_stable_ascent"}
if len(reports) != 6 or {name.rsplit(".", 1)[1] for name, _ in reports} != expected:
    raise SystemExit(f"Expected the six named theorem dependency reports, received {len(reports)}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for _, entry in reports:
    found = {name.strip() for name in entry.split(",") if name.strip()}
    if not found <= allowed:
        raise SystemExit("Unexpected proof dependency: " + ", ".join(sorted(found - allowed)))
if "sorryAx" in source:
    raise SystemExit("An incomplete proof was detected")
print("Six new theorem dependency reports use only standard axioms.")
