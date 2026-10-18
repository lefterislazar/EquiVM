#!/usr/bin/env python3
"""Run every ABI case (each call of `abi_cases.CALLS` and its malformed variants) on the runtime code
of every version and pipeline, and group versions by the observable result: success, and the return
or revert data.

Each case is one anvil `debug_traceCall` with the probe's code as a state override.  Writes
``out/dynamic.json``: per case, the version classes of each pipeline and the observed results.

    python3 abi_dynamic.py [--versions 0.8.36,0.8.37] [--jobs N]
"""

import argparse
import concurrent.futures
import hashlib
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "solc_storage_audit"))

from abi_calldata import mutations  # noqa: E402
from abi_cases import CALLS, signature  # noqa: E402
from abi_matrix import PIPELINES, VERSIONS  # noqa: E402
from dynamic import Anvil  # noqa: E402
from run_matrix import version_key  # noqa: E402

OUT = HERE / "out"
TARGET = "0x00000000000000000000000000000000000c0de1"


def runtime(pipeline, version, probe, fn):
    path = OUT / "raw" / pipeline / version / f"{probe}.json"
    if not path.exists():
        return None
    record = json.loads(path.read_text())
    unit = record["units"].get("*") or record["units"].get(fn)
    if not unit or unit["errors"]:
        return None
    code = unit["contracts"].get(probe, {}).get("runtime", "")
    return "0x" + code if code else None


def call(anvil, code, calldata):
    tx = {"to": TARGET, "data": "0x" + calldata.hex(), "gas": hex(30_000_000)}
    trace = anvil.rpc("debug_traceCall", [tx, "latest", {"tracer": "callTracer",
                                                         "stateOverrides": {TARGET: {"code": code}}}])
    return {"ok": "error" not in trace, "out": trace.get("output", "0x"), "error": trace.get("error", "")}


def fingerprint(result):
    return hashlib.sha256(json.dumps(result, sort_keys=True).encode()).hexdigest()[:12]


def runs(series):
    out = []
    for v, h in series:
        if out and out[-1][2] == h:
            out[-1][1] = v
        else:
            out.append([v, v, h])
    return out


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--versions", default=",".join(VERSIONS))
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()
    versions = sorted(args.versions.split(","), key=version_key)

    cases = []
    for n, (probe, fn, types, values) in enumerate(CALLS):
        sig = signature(fn, types)
        for label, calldata in mutations(sig, types, values):
            cases.append((f"{probe}.{fn}#{n} {label}", probe, fn, calldata))

    anvil = Anvil()
    try:
        jobs = [(c, p, v) for c in cases for p in PIPELINES for v in versions]
        codes = {(p, v, probe, fn): runtime(p, v, probe, fn)
                 for p in PIPELINES for v in versions for (_, probe, fn, _) in cases}

        def work(job):
            (key, probe, fn, calldata), p, v = job
            code = codes[(p, v, probe, fn)]
            return key, p, v, (None if code is None else call(anvil, code, calldata))

        results = {}
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
            for key, p, v, r in pool.map(work, jobs):
                results.setdefault(key, {}).setdefault(p, {})[v] = r
    finally:
        anvil.close()

    summary = {}
    for key, per_pipeline in results.items():
        entry = {"classes": {}, "observed": {}}
        for p, per_version in per_pipeline.items():
            series = []
            for v in versions:
                r = per_version.get(v)
                h = None if r is None else fingerprint(r)
                if r is not None:
                    entry["observed"][h] = r
                series.append((v, h))
            entry["classes"][p] = runs(series)
        summary[key] = entry
    (OUT / "dynamic.json").write_text(json.dumps(summary, indent=1))
    print(f"{len(cases)} cases × {len(PIPELINES)} pipelines × {len(versions)} versions")


if __name__ == "__main__":
    main()
