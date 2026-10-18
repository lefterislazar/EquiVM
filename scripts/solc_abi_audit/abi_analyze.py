#!/usr/bin/env python3
"""Cluster 0.8.13–0.8.37 by the normalized Yul closure of each external function (ABI decoding,
body, ABI encoding) and write the helpers whose own code changes at each boundary.

Reads ``out/closures``; writes ``out/analysis.json`` and ``out/diffs/<from>..<to>/<helper>.diff``.
"""
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "solc_storage_audit"))

import analyze  # noqa: E402
from run_matrix import version_key  # noqa: E402

OUT = HERE / "out"


def main():
    analyze.OUT = OUT
    versions, data = analyze.load_versions()
    per_op, distinct = analyze.analyze_closures(versions, data)
    entries = analyze.write_diffs(distinct)
    (OUT / "analysis.json").write_text(json.dumps({"versions": versions, "ops": per_op, "changes": entries}, indent=1))
    by_boundary = {}
    for e in entries:
        by_boundary.setdefault(f"{e['from']}..{e['to']}", []).append(e)
    print(f"{len(per_op)} operations, {len(entries)} distinct helper changes")
    for b in sorted(by_boundary, key=lambda b: version_key(b.split("..")[1])):
        es = by_boundary[b]
        print(f"  {b:16} {len(es):3} helper changes over {len({o for e in es for o in e['ops']})} ops")


if __name__ == "__main__":
    main()
