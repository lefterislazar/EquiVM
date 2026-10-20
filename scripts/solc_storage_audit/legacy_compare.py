#!/usr/bin/env python3
"""Run the dynamic scenarios on legacy-pipeline bytecode (no `--via-ir`) and report every scenario
whose observable behaviour differs from the via-IR bytecode of the same release.

Needs `out/dynamic.json` (run `dynamic.py` first), anvil and cast.

    python3 legacy_compare.py
"""
import json

import dynamic
import run_matrix
import scenarios
from pathlib import Path

VERSIONS = ["0.8.4", "0.8.13", "0.8.23", "0.8.37"]

def legacy_runtime(version, probe, ops):
    """Legacy runtime code of the probe; when it does not compile as a whole (the legacy code
    generator does not copy memory arrays of structs to storage), of a contract with just the
    scenario's operations.  None when those do not compile either."""
    src = (run_matrix.PROBES / f"{probe}.sol").read_text()
    if run_matrix.version_key(version) < run_matrix.version_key(run_matrix.probe_directives(src)["min"]):
        return None
    contracts, errors = run_matrix.compile_source(version, f"{probe}.sol", src, via_ir=False)
    if errors:
        header, functions, trailer = run_matrix.split_probe(src)
        # setters of storage-to-storage copy sources are shared declarations: keep the ones used
        header = [line for line in header
                  if not line.startswith("  function set_") or line.split("(")[0].split()[-1] in ops]
        wanted = [body for name, body in functions if name in ops]
        if len(wanted) < len(ops):
            return None
        unit = "\n".join(header + [line for body in wanted for line in body] + trailer) + "\n"
        contracts, errors = run_matrix.compile_source(version, f"{probe}.sol", unit, via_ir=False)
    return None if errors or not contracts[probe]["runtime"] else "0x" + contracts[probe]["runtime"]


via = json.loads((Path(dynamic.OUT) / "dynamic.json").read_text())
anvil = dynamic.Anvil()
try:
    fwd = dynamic.forwarder_runtime()
    cache = {}
    for sc in scenarios.SCENARIOS:
        row = []
        for v in VERSIONS:
            key = (v, sc.probe, frozenset(sc.ops()))
            if key not in cache: cache[key] = legacy_runtime(v, sc.probe, frozenset(sc.ops()))
            code = cache[key]
            if code is None: row.append("-"); continue
            res = dynamic.run(anvil, code, fwd, sc)
            vh = next((h for a, b, h in via[sc.key]["classes"]
                       if run_matrix.version_key(a) <= run_matrix.version_key(v) <= run_matrix.version_key(b)), None)
            same = vh is not None and dynamic.fingerprint(res) == vh
            row.append("=" if same else "DIFF")
            if not same and vh:
                o = via[sc.key]["observed"][vh]
                diffslots = {s for s in set(o["storage"]) | set(res["storage"]) if o["storage"].get(s) != res["storage"].get(s)}
                stepdiff = [i for i, (x, y) in enumerate(zip(o["steps"], res["steps"])) if x != y]
                row[-1] = f"DIFF(slots={len(diffslots)},steps={stepdiff[:4]})"
        if any(r.startswith("DIFF") or r == "-" for r in row):
            print(f"{sc.key:42}", " ".join(f"{v}:{r}" for v, r in zip(VERSIONS, row)))
finally:
    anvil.close()
