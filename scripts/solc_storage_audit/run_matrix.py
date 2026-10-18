#!/usr/bin/env python3
"""Compile every storage probe with every solc 0.8.x release through the IR pipeline.

For each (version, probe) the unoptimized Yul IR, the storage layout, and the via-IR runtime
bytecode (optimizer off) are written to ``out/raw/<version>/<probe>.json``.  A probe that does
not compile as a whole (typically ``UnimplementedFeatureError`` in early IR releases) is split
into one contract per operation, so a single unsupported construct only loses that operation.
Compile failures are recorded, not raised.

    python3 run_matrix.py [--versions 0.8.13,0.8.14] [--probes Bytes,DynArrays] [--jobs N]
"""

import argparse
import concurrent.futures
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROBES = HERE / "probes"
OUT = HERE / "out" / "raw"
ARTIFACTS = Path.home() / ".solc-select" / "artifacts"

ALL_VERSIONS = [f"0.8.{n}" for n in range(0, 38)]
# Probe operations are named `<op>_<target>`; other functions are shared declarations.
OP_FUNCTION = re.compile(r"^  function ((?:w|r|d|wf|rf|wi|ri|di|len|push0|pushv|pop|rmw)_\w+)\(")


def version_key(v):
    return tuple(int(x) for x in v.split("."))


def solc_path(version):
    return ARTIFACTS / f"solc-{version}" / f"solc-{version}"


def probe_directives(source):
    """`// @min 0.8.28` and `// @nosplit` comments in the probe header."""
    min_version = re.search(r"// @min (\S+)", source)
    return {
        "min": min_version.group(1) if min_version else "0.8.0",
        "nosplit": "// @nosplit" in source,
    }


def split_probe(source):
    """(header lines, [(op name, function lines)], trailer lines) of a one-contract probe."""
    lines = source.splitlines()
    header, ops, trailer = [], [], []
    i = 0
    while i < len(lines):
        line = lines[i]
        match = OP_FUNCTION.match(line)
        if match:
            depth, body = 0, []
            while True:
                body.append(lines[i])
                depth += lines[i].count("{") - lines[i].count("}")
                i += 1
                if depth == 0:
                    break
            ops.append((match.group(1), body))
            continue
        (trailer if ops and line.startswith("}") else header).append(line)
        i += 1
    return header, ops, trailer


def standard_json(source_name, source, via_ir=True):
    return json.dumps({
        "language": "Solidity",
        "sources": {source_name: {"content": source}},
        "settings": {
            "viaIR": via_ir,
            "optimizer": {"enabled": False},
            "outputSelection": {"*": {"*": ["ir", "storageLayout", "evm.deployedBytecode.object"]}},
        },
    })


def compile_source(version, source_name, source):
    """{contract: {ir, storageLayout, runtime}} and the list of error messages."""
    proc = subprocess.run([str(solc_path(version)), "--standard-json"],
                          input=standard_json(source_name, source),
                          capture_output=True, text=True, timeout=600)
    try:
        result = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return {}, [f"solc crashed: {proc.stderr.strip()[:2000]}"]
    errors = [e.get("formattedMessage", e.get("message", ""))
              for e in result.get("errors", []) if e.get("severity") == "error"]
    contracts = {}
    for name, c in result.get("contracts", {}).get(source_name, {}).items():
        contracts[name] = {
            "ir": c.get("ir", ""),
            "storageLayout": c.get("storageLayout"),
            "runtime": c.get("evm", {}).get("deployedBytecode", {}).get("object", ""),
        }
    if contracts and not errors and not any(c["runtime"] for c in contracts.values()):
        # Early releases ignore `settings.viaIR`; the CLI flag still produces via-IR bytecode.
        for name, runtime in cli_via_ir_runtime(version, source_name, source).items():
            if name in contracts:
                contracts[name]["runtime"] = runtime
    return contracts, errors


def cli_via_ir_runtime(version, source_name, source):
    scratch = OUT.parent / "cli" / version
    scratch.mkdir(parents=True, exist_ok=True)
    path = scratch / source_name
    path.write_text(source)
    flag = "--via-ir" if version_key(version) >= (0, 8, 13) else "--experimental-via-ir"
    proc = subprocess.run([str(solc_path(version)), flag, "--bin-runtime", path.name],
                          cwd=scratch, capture_output=True, text=True, timeout=600)
    runtimes = {}
    for match in re.finditer(r"======= [^:]+:(\w+) =======\nBinary of the runtime part:\n([0-9a-f]*)",
                             proc.stdout):
        runtimes[match.group(1)] = match.group(2)
    return runtimes


def compile_probe(version, probe_path):
    source = probe_path.read_text()
    directives = probe_directives(source)
    record = {"version": version, "probe": probe_path.stem, "mode": "skipped", "units": {}}
    if version_key(version) < version_key(directives["min"]):
        return record
    contracts, errors = compile_source(version, probe_path.name, source)
    if not errors:
        record["mode"] = "whole"
        record["units"]["*"] = {"contracts": contracts, "errors": []}
        return record
    record["wholeErrors"] = errors
    if directives["nosplit"]:
        record["mode"] = "failed"
        return record
    record["mode"] = "split"
    header, ops, trailer = split_probe(source)
    for op, body in ops:
        unit = "\n".join(header + body + trailer) + "\n"
        contracts, errors = compile_source(version, probe_path.name, unit)
        record["units"][op] = {"contracts": contracts, "errors": errors}
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--versions", default=",".join(ALL_VERSIONS))
    parser.add_argument("--probes", default="")
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()

    versions = args.versions.split(",")
    probes = sorted(PROBES.glob("*.sol"))
    if args.probes:
        wanted = set(args.probes.split(","))
        probes = [p for p in probes if p.stem in wanted]
    missing = [v for v in versions if not solc_path(v).exists()]
    if missing:
        sys.exit(f"missing compilers (solc-select install …): {' '.join(missing)}")

    manifest = {"compilers": {v: hashlib.sha256(solc_path(v).read_bytes()).hexdigest() for v in versions},
                "probes": {p.stem: hashlib.sha256(p.read_bytes()).hexdigest() for p in probes}}
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "manifest.json").write_text(json.dumps(manifest, indent=1, sort_keys=True))

    jobs = [(v, p) for v in versions for p in probes]
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        futures = {pool.submit(compile_probe, v, p): (v, p) for v, p in jobs}
        for future in concurrent.futures.as_completed(futures):
            v, p = futures[future]
            record = future.result()
            target = OUT / v / f"{p.stem}.json"
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_text(json.dumps(record, indent=1, sort_keys=True))
            failed = sum(1 for u in record["units"].values() if u["errors"])
            print(f"{v:8} {p.stem:20} {record['mode']:7} units={len(record['units'])} failed={failed}",
                  flush=True)


if __name__ == "__main__":
    main()
