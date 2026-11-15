"""Reject proof dependencies beyond Lean's standard mathematical axioms."""
from pathlib import Path
import re
import sys

source = Path(sys.argv[1]).read_text(encoding="utf-8")
names = re.findall(r"depends on axioms:\s*\[([^]]*)\]", source, re.S)
if len(names) != 6:
    raise SystemExit(f"Expected six theorem dependency reports, received {len(names)}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for entry in names:
    found = {name.strip() for name in entry.split(",") if name.strip()}
    if not found <= allowed:
        raise SystemExit("Unexpected proof dependency: " + ", ".join(sorted(found - allowed)))
if "sorryAx" in source:
    raise SystemExit("An incomplete proof was detected")
print("Six new theorem dependency reports use only standard axioms.")
