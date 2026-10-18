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
orig = run_matrix.standard_json
run_matrix.standard_json = lambda name, src, via_ir=True: orig(name, src, via_ir=False)

def legacy_runtime(version, probe):
    src = (run_matrix.PROBES / f"{probe}.sol").read_text()
    if run_matrix.version_key(version) < run_matrix.version_key(run_matrix.probe_directives(src)["min"]):
        return None
    contracts, errors = run_matrix.compile_source(version, f"{probe}.sol", src)
    return None if errors else "0x" + contracts[probe]["runtime"]

via = json.loads((Path(dynamic.OUT) / "dynamic.json").read_text())
anvil = dynamic.Anvil()
try:
    fwd = dynamic.forwarder_runtime()
    cache = {}
    for sc in scenarios.SCENARIOS:
        row = []
        for v in VERSIONS:
            key = (v, sc.probe)
            if key not in cache: cache[key] = legacy_runtime(v, sc.probe)
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
        if any(r.startswith("DIFF") for r in row):
            print(f"{sc.key:42}", " ".join(f"{v}:{r}" for v, r in zip(VERSIONS, row)))
finally:
    anvil.close()
