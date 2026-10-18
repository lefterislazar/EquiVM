#!/usr/bin/env python3
"""Run every scenario against the via-IR runtime code of every solc version and group versions
by what is observable: each call's success flag and return/revert data, and the target's final
storage.  Versions in different groups behave differently on that scenario.

The calls of a scenario run inside one transaction through a forwarder, so transient storage
persists across them.  Nothing is committed: each run is an anvil ``debug_traceCall`` with the
probe's code and the scenario's initial storage given as state overrides, traced with
``callTracer`` (per-call results) and ``prestateTracer`` in diff mode (storage writes).

Needs ``anvil`` (started here on a free port) and ``cast`` (ABI encoding, keccak).

    python3 dynamic.py [--probes Bytes] [--versions 0.8.30,0.8.31]

Writes ``out/dynamic.json``.
"""

import argparse
import hashlib
import json
import socket
import subprocess
import time
import urllib.request
from pathlib import Path

import functools

from run_matrix import ALL_VERSIONS, ARTIFACTS, PROBES, compile_source, split_probe, version_key
from scenarios import SCENARIOS, TARGET

HERE = Path(__file__).resolve().parent
OUT = HERE / "out"
FORWARDER_ADDRESS = "0x00000000000000000000000000000000000f0d00"
FORWARDER_SOURCE = """
// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.34;
contract Forwarder {
  fallback(bytes calldata input) external returns (bytes memory) {
    (address target, bytes[] memory calls) = abi.decode(input, (address, bytes[]));
    for (uint256 i = 0; i < calls.length; i++) { target.call(calls[i]); }
    return "";
  }
}
"""


class Anvil:
    def __init__(self):
        with socket.socket() as s:
            s.bind(("127.0.0.1", 0))
            self.port = s.getsockname()[1]
        self.proc = subprocess.Popen(["anvil", "--port", str(self.port), "--silent", "--hardfork", "prague",
                                      "--gas-limit", "1000000000"],
                                     stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        for _ in range(100):
            try:
                self.rpc("eth_chainId", [])
                return
            except OSError:
                time.sleep(0.1)
        raise RuntimeError("anvil did not start")

    def rpc(self, method, params):
        request = urllib.request.Request(f"http://127.0.0.1:{self.port}",
                                         json.dumps({"jsonrpc": "2.0", "id": 1, "method": method,
                                                     "params": params}).encode(),
                                         {"Content-Type": "application/json"})
        reply = json.loads(urllib.request.urlopen(request, timeout=120).read())
        if "error" in reply:
            raise RuntimeError(f"{method}: {reply['error']}")
        return reply["result"]

    def close(self):
        self.proc.terminate()


def forwarder_runtime():
    solc = ARTIFACTS / "solc-0.8.34" / "solc-0.8.34"
    request = json.dumps({"language": "Solidity", "sources": {"F.sol": {"content": FORWARDER_SOURCE}},
                          "settings": {"outputSelection": {"*": {"*": ["evm.deployedBytecode.object"]}}}})
    out = json.loads(subprocess.run([str(solc), "--standard-json"], input=request, capture_output=True,
                                    text=True, check=True).stdout)
    return "0x" + out["contracts"]["F.sol"]["Forwarder"]["evm"]["deployedBytecode"]["object"]


def encode_forward(calls):
    return subprocess.run(["cast", "abi-encode", "f(address,bytes[])", TARGET, "[" + ",".join(calls) + "]"],
                          capture_output=True, text=True, check=True).stdout.strip()


def word(n):
    return "0x" + format(n % 2**256, "064x")


@functools.lru_cache(maxsize=None)
def runtime_of(version, probe, ops):
    """The probe's runtime code; when the probe only compiled split into single operations,
    a contract with just the scenario's operations (and the shared declarations)."""
    path = OUT / "raw" / version / f"{probe}.json"
    if not path.exists():
        return None
    record = json.loads(path.read_text())
    if record["mode"] == "whole":
        code = record["units"]["*"]["contracts"][probe]["runtime"]
    elif record["mode"] == "split":
        header, functions, trailer = split_probe((PROBES / f"{probe}.sol").read_text())
        wanted = [body for name, body in functions if name in ops]
        if len(wanted) < len(ops):
            return None
        source = "\n".join(header + [line for body in wanted for line in body] + trailer) + "\n"
        contracts, errors = compile_source(version, f"{probe}.sol", source)
        code = "" if errors else contracts[probe]["runtime"]
    else:
        return None
    return "0x" + code if code else None


def run(anvil, code, forwarder, scenario):
    storage = {word(k): word(v) for k, v in scenario.storage.items()}
    overrides = {TARGET: {"code": code, "state": storage}, FORWARDER_ADDRESS: {"code": forwarder}}
    tx = {"to": FORWARDER_ADDRESS, "data": encode_forward(scenario.calldata()), "gas": hex(500_000_000)}
    calls = anvil.rpc("debug_traceCall", [tx, "latest", {"tracer": "callTracer", "stateOverrides": overrides}])
    diff = anvil.rpc("debug_traceCall", [tx, "latest", {"tracer": "prestateTracer",
                                                        "tracerConfig": {"diffMode": True},
                                                        "stateOverrides": overrides}])
    steps = []
    for sub in calls.get("calls", []):
        if sub.get("to", "").lower() != TARGET.lower():
            continue
        steps.append({"ok": "error" not in sub, "out": sub.get("output", "0x")})
    final = {int(k, 16): int(v, 16) for k, v in storage.items()}
    pre = diff["pre"].get(TARGET, {}).get("storage", {})
    post = diff["post"].get(TARGET, {}).get("storage", {})
    for slot in pre:
        if slot not in post:
            final[int(slot, 16)] = 0  # diff mode omits slots that became zero
    for slot, value in post.items():
        final[int(slot, 16)] = int(value, 16)
    final = {hex(k): hex(v) for k, v in sorted(final.items()) if v}
    return {"steps": steps, "storage": final}


def fingerprint(result):
    return hashlib.sha256(json.dumps(result, sort_keys=True).encode()).hexdigest()[:12]


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--versions", default=",".join(ALL_VERSIONS))
    parser.add_argument("--probes", default="")
    args = parser.parse_args()
    versions = sorted(args.versions.split(","), key=version_key)
    probes = set(args.probes.split(",")) if args.probes else None

    anvil = Anvil()
    try:
        forwarder = forwarder_runtime()
        results = {}
        for scenario in SCENARIOS:
            if probes and scenario.probe not in probes:
                continue
            per_version, observed = {}, {}
            for v in versions:
                code = runtime_of(v, scenario.probe, frozenset(scenario.ops()))
                if code is None:
                    per_version[v] = None
                    continue
                result = run(anvil, code, forwarder, scenario)
                h = fingerprint(result)
                per_version[v] = h
                observed.setdefault(h, result)
            runs = []
            for v in versions:
                if runs and runs[-1][2] == per_version[v]:
                    runs[-1][1] = v
                else:
                    runs.append([v, v, per_version[v]])
            results[scenario.key] = {"probe": scenario.probe, "ops": scenario.ops(), "note": scenario.note,
                                     "classes": runs, "observed": observed}
            label = " | ".join(f"{a}..{b}:{h or '-'}" for a, b, h in runs)
            print(f"{scenario.key:40} {label}", flush=True)
    finally:
        anvil.close()
    (OUT / "dynamic.json").write_text(json.dumps(results, indent=1))


if __name__ == "__main__":
    main()
