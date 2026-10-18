#!/usr/bin/env python3
"""Compile the ABI probes with solc 0.8.13–0.8.37, through both code generators, and extract the
normalized Yul closure of every external function (its ABI decoder, body and ABI encoder).

For each (pipeline, version, probe), ``out/raw/<pipeline>/<version>/<probe>.json`` holds the runtime
code and the unoptimized IR; ``out/closures/<version>.json`` holds the closures of the IR, which
does not depend on the pipeline setting (the legacy code generator uses the same ABI routines).
A probe that does not compile as a whole is split into one contract per function.

    python3 abi_matrix.py [--versions 0.8.36,0.8.37] [--jobs N]
"""

import argparse
import concurrent.futures
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "solc_storage_audit"))

import yul_extract  # noqa: E402
from run_matrix import compile_source, probe_directives, solc_path, version_key  # noqa: E402

PROBES = HERE / "probes"
OUT = HERE / "out"
VERSIONS = [f"0.8.{n}" for n in range(13, 38)]
PIPELINES = {"viair": True, "legacy": False}
FUNCTION = re.compile(r"^  function (\w+)\(")


def ops_of(source):
    """External functions of a probe; `target` and other helpers are ops too (they are cheap)."""
    return [m.group(1) for line in source.splitlines() if (m := FUNCTION.match(line))]


def split_probe(source):
    """(header lines, [(name, lines)], trailer lines), by brace depth at two-space indentation."""
    lines = source.splitlines()
    header, fns, trailer, i = [], [], [], 0
    while i < len(lines):
        m = FUNCTION.match(lines[i])
        if m:
            depth, opened, body = 0, False, []
            while True:
                body.append(lines[i])
                depth += lines[i].count("{") - lines[i].count("}")
                opened = opened or "{" in lines[i]
                i += 1
                if opened and depth == 0:
                    break
            fns.append((m.group(1), body))
            continue
        (trailer if fns and lines[i].startswith("}") else header).append(lines[i])
        i += 1
    return header, fns, trailer


def compile_probe(pipeline, version, probe_path):
    source = probe_path.read_text()
    record = {"pipeline": pipeline, "version": version, "probe": probe_path.stem, "mode": "skipped",
              "units": {}}
    if version_key(version) < version_key(probe_directives(source)["min"]):
        return record
    via_ir = PIPELINES[pipeline]
    contracts, errors = compile_source(version, probe_path.name, source, via_ir)
    if not errors:
        record["mode"] = "whole"
        record["units"]["*"] = {"contracts": contracts, "errors": []}
        return record
    record["mode"], record["wholeErrors"] = "split", errors
    header, fns, trailer = split_probe(source)
    for name, body in fns:
        unit = "\n".join(header + body + trailer) + "\n"
        contracts, errors = compile_source(version, probe_path.name, unit, via_ir)
        record["units"][name] = {"contracts": contracts, "errors": errors}
    return record


def external_closures(ir, ops):
    """Closure of `external_fun_<op>_<id>` for each op, as `yul_extract.closures_for_ir` does for
    `fun_<op>_<id>`."""
    functions = yul_extract.split_functions(yul_extract.deployed_code(ir))
    defined = set(functions)
    result = {}
    for op in ops:
        roots = [f for f in functions if re.fullmatch(rf"external_fun_{re.escape(op)}_\d+", f)]
        if not roots:
            continue
        members = yul_extract.closure_of(roots[0], functions)
        canon = yul_extract.canonical_name
        bodies = {canon(f): yul_extract.normalize_function(functions[f], defined) for f in members}
        calls = {canon(f): sorted(canon(c) for c in yul_extract.callees(functions[f], defined)) for f in members}
        result[op] = {"root": canon(roots[0]), "merkle": yul_extract.merkle_hashes(bodies, calls)[canon(roots[0])],
                      "functions": bodies, "calls": calls}
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--versions", default=",".join(VERSIONS))
    parser.add_argument("--jobs", type=int, default=12)
    args = parser.parse_args()
    versions = args.versions.split(",")
    missing = [v for v in versions if not solc_path(v).exists()]
    if missing:
        sys.exit(f"missing compilers: {' '.join(missing)}")
    probes = sorted(PROBES.glob("*.sol"))

    jobs = [(p, v, f) for p in PIPELINES for v in versions for f in probes]
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        for record in pool.map(lambda j: compile_probe(*j), jobs):
            target = OUT / "raw" / record["pipeline"] / record["version"] / f"{record['probe']}.json"
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(json.dumps(record, indent=1, sort_keys=True))
            failed = [u for u, d in record["units"].items() if d["errors"]]
            if record["mode"] != "whole":
                print(f"{record['pipeline']:6} {record['version']:7} {record['probe']:16} {record['mode']:7} "
                      f"failed={failed}", flush=True)

    (OUT / "closures").mkdir(parents=True, exist_ok=True)
    for v in versions:
        closures = {}
        for probe in probes:
            record = json.loads((OUT / "raw" / "viair" / v / f"{probe.stem}.json").read_text())
            ops = ops_of(probe.read_text())
            for unit, data in record["units"].items():
                contract = data["contracts"].get(probe.stem)
                if contract and contract["ir"]:
                    for op, c in external_closures(contract["ir"], ops if unit == "*" else [unit]).items():
                        closures[f"{probe.stem}.{op}"] = c
        (OUT / "closures" / f"{v}.json").write_text(json.dumps({"closures": closures}, indent=1, sort_keys=True))
        print(f"{v}: {len(closures)} closures", flush=True)


if __name__ == "__main__":
    main()
