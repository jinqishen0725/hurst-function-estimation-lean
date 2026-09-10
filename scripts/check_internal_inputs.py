"""Fail closed until every internal statistical input is discharged.

This audit is intentionally separate from Lean's axiom audit: ordinary theorem
parameters are legal Lean, but an internal convergence or moment statement is
not accepted merely because it is supplied as a parameter.
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
inventory = json.loads((ROOT / "verification/internal_input_inventory.json").read_text())
conditional = json.loads((ROOT / "verification/conditional_results.json").read_text())

open_inputs = [row for row in inventory["inputs"] if row["status"] != "discharged"]
assert inventory["mainline_complete"] == (not open_inputs)
assert conditional["mainline_complete"] is False or not open_inputs

result = {
    "mainline_complete": not open_inputs,
    "open_internal_inputs": [row["id"] for row in open_inputs],
    "acceptance_rule": inventory["acceptance_rule"],
}
(ROOT / "verification/internal_input_audit.json").write_text(
    json.dumps(result, indent=2, ensure_ascii=False) + "\n"
)
print(json.dumps(result, indent=2, ensure_ascii=False))
