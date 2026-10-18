#!/usr/bin/env python3
"""Combine the static (``out/analysis.json``) and dynamic (``out/dynamic.json``) results into
``summary.json`` and the generated tables of ``MATRIX.md``.

Each version boundary where some operation's normalized helper closure changes gets the
classification recorded in ``BOUNDARIES`` (from reading its diffs under ``out/diffs``), and the
dynamic evidence: the scenarios whose observable behaviour changes at that version.
"""

import json
from collections import defaultdict
from pathlib import Path

from run_matrix import version_key

HERE = Path(__file__).resolve().parent
OUT = HERE / "out"

# version where the change appears -> (classification, what changed)
BOUNDARIES = {
    "0.8.1": ("unverified", "Experimental IR codegen being completed (struct/array copies, pushes, packed reads). "
                            "0.8.0 emits no via-IR bytecode, so only the IR can be compared."),
    "0.8.2": ("refactoring", "`storage_set_to_zero` binds the zero value with `let`; push/pop convert the storage "
                             "reference to a storage pointer first."),
    "0.8.4": ("refactoring", "Index access into long bytes factored into `long_byte_array_index_access_no_checks`; "
                             "same slot and offset."),
    "0.8.5": ("refactoring", "Tail clearing factored into `cleanup_storage_array_end` / `clean_up_bytearray_end_slots`; "
                             "literals copied straight to storage."),
    "0.8.7": ("representation", "Internal function pointers are stored as sequential dispatch ids instead of AST ids; "
                                "contract-type conversions go through `uint160`."),
    "0.8.8": ("cosmetic", "Same-type conversions wrap the value in `identity`."),
    "0.8.15": ("memory-only", "Copying an empty short bytes value from storage to memory no longer allocates a "
                              "32-byte data word. Return data unchanged."),
    "0.8.16": ("semantic, non-canonical states only",
               "Packed arrays are copied into storage one whole slot at a time (bytes past the last element are "
               "zeroed) instead of element-by-element read-modify-write (those bytes were kept). Checked "
               "arithmetic restructured; memory copies clean up after themselves."),
    "0.8.17": ("refactoring", "`checked_mul` overflow test restructured (`div(product, x) == y`)."),
    "0.8.25": ("memory-only", "Memory-to-memory copies use `mcopy`."),
    "0.8.32": ("semantic (bug fix)", "Clearing loops count from zero instead of comparing absolute slots, so arrays "
                                     "straddling 2**256 are cleared (`LostStorageArrayWriteOnSlotOverflow`)."),
    "0.8.34": ("semantic (bug fix)", "Transient clearing gets its own helper. In 0.8.28-0.8.33 `delete` on a persistent "
                                     "variable could clear the transient variable of the same type instead "
                                     "(`TransientStorageClearingHelperCollision`)."),
}
FEATURES = {"0.8.28": "transient storage (value types)", "0.8.29": "`layout at` custom base slot"}


def main():
    analysis = json.loads((OUT / "analysis.json").read_text())
    dynamic = json.loads((OUT / "dynamic.json").read_text())
    layouts = json.loads((OUT / "layouts.json").read_text())

    static_ops = defaultdict(set)
    for op, info in analysis["ops"].items():
        for b in info["boundaries"]:
            if b.get("kind") != "presence":
                static_ops[b["to"]].add(op)
    helper_changes = defaultdict(int)
    for change in analysis["changes"]:
        helper_changes[change["to"]] += 1
    dynamic_scenarios = defaultdict(set)
    for key, info in dynamic.items():
        for (_, _, h_old), (first, _, h_new) in zip(info["classes"], info["classes"][1:]):
            if h_old and h_new and h_old != h_new:
                dynamic_scenarios[first].add(key)

    unexplained = sorted(set(dynamic_scenarios) - set(static_ops))
    unclassified = sorted(set(static_ops) - set(BOUNDARIES))
    boundaries = []
    for version in sorted(static_ops, key=version_key):
        kind, text = BOUNDARIES.get(version, ("UNCLASSIFIED", ""))
        boundaries.append({"version": version, "classification": kind, "change": text,
                           "ops": sorted(static_ops[version]), "helperChanges": helper_changes[version],
                           "behaviourChanges": sorted(dynamic_scenarios.get(version, ()))})
    summary = {"versions": analysis["versions"], "boundaries": boundaries, "features": FEATURES,
               "layoutClasses": {p: r["classes"] for p, r in layouts.items()},
               "dynamicChangesWithoutStaticBoundary": unexplained, "unclassifiedBoundaries": unclassified,
               "scenarios": {k: {"ops": v["ops"], "note": v["note"],
                                 "classes": [[a, b, h] for a, b, h in v["classes"]]} for k, v in dynamic.items()}}
    (HERE / "summary.json").write_text(json.dumps(summary, indent=1) + "\n")

    lines = ["# Generated tables", "",
             "Generated by `report.py` from `out/analysis.json`, `out/dynamic.json` and `out/layouts.json`. "
             "See `REPORT.md` for the discussion.", "",
             "## Version boundaries", "",
             "| from | classification | ops (static) | origin helper changes | scenarios whose behaviour changes |",
             "|---|---|---:|---:|---|"]
    for b in boundaries:
        dyn = ", ".join(f"`{s}`" for s in b["behaviourChanges"]) or "none"
        lines.append(f"| {b['version']} | {b['classification']} | {len(b['ops'])} | {b['helperChanges']} | {dyn} |")
    lines += ["", "## Operations by version class (static)", "",
              "Operations whose normalized helper closure is identical across 0.8.2-0.8.37 are omitted.", "",
              "| operation | classes |", "|---|---|"]
    for op, info in sorted(analysis["ops"].items()):
        classes = [c for c, h in zip(info["classes"], info["hashes"]) if h]
        if len(classes) > 1 and not (len(classes) == 2 and version_key(classes[0][1]) < (0, 8, 2)):
            lines.append(f"| `{op}` | " + " · ".join(f"{a}–{b}" for a, b in classes) + " |")
    lines += ["", "## Scenarios by version class (dynamic)", "",
              "Version groups with identical per-call results and final storage. `—` marks versions where the "
              "scenario cannot run (feature absent, or no via-IR bytecode).", "",
              "| scenario | classes |", "|---|---|"]
    for key, info in dynamic.items():
        groups = " · ".join(f"{a}–{b}" + ("" if h else " —") for a, b, h in info["classes"])
        lines.append(f"| `{key}` | {groups} |")
    lines += ["", "## Storage layout", "",
              "| probe | layout classes |", "|---|---|"]
    for probe, r in layouts.items():
        lines.append(f"| {probe} | " + " · ".join(f"{a}–{b}" for a, b in r["classes"]) + " |")
    (HERE / "MATRIX.md").write_text("\n".join(lines) + "\n")

    print(f"{len(boundaries)} boundaries; dynamic changes without a static boundary: {unexplained or 'none'}; "
          f"unclassified: {unclassified or 'none'}")


if __name__ == "__main__":
    main()
