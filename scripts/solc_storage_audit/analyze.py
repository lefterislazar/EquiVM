#!/usr/bin/env python3
"""Cluster solc versions by normalized helper closure and diff every class boundary.

Reads ``out/closures/<version>.json`` and ``out/raw`` (storage layouts) and writes:

* ``out/analysis.json``: per operation, the version classes; per boundary, which helpers were
  added, removed, renamed (same body) or changed; and the distinct helper changes deduplicated
  across operations, which are what gets triaged;
* ``out/diffs/<from>..<to>/<helper>.diff``: unified diffs of every changed helper;
* ``out/layouts.json``: storage layout classes per probe (slot/offset/type of every variable).
"""

import difflib
import hashlib
import json
from pathlib import Path

from run_matrix import version_key
from yul_extract import erase_callees

HERE = Path(__file__).resolve().parent
OUT = HERE / "out"


def body_hash(body):
    return hashlib.sha256(body.encode()).hexdigest()[:12]


def load_versions():
    versions = sorted((p.stem for p in (OUT / "closures").glob("*.json")), key=version_key)
    return versions, {v: json.loads((OUT / "closures" / f"{v}.json").read_text()) for v in versions}


def classes(series):
    """Maximal runs of consecutive versions with the same value: [(first, last, value)]."""
    runs = []
    for version, value in series:
        if runs and runs[-1][2] == value:
            runs[-1][1] = version
        else:
            runs.append([version, version, value])
    return [tuple(r) for r in runs]


def erased(closure):
    return {name: erase_callees(body, closure["calls"][name]) for name, body in closure["functions"].items()}


def origin_delta(old, new):
    """Helpers whose own code changed between two closures, ignoring renames and changes that
    only propagate from a callee.  A helper is an origin if its erased body differs from the
    same-named helper's, or, when its name is new, matches no erased body on the other side."""
    old_e, new_e = erased(old), erased(new)
    old_bodies, new_bodies = set(old_e.values()), set(new_e.values())
    changed = sorted(n for n in new_e if n in old_e and new_e[n] != old_e[n])
    added = sorted(n for n in new_e if n not in old_e and new_e[n] not in old_bodies)
    removed = sorted(n for n in old_e if n not in new_e and old_e[n] not in new_bodies)
    return {"added": added, "removed": removed, "changed": changed}


def analyze_closures(versions, data):
    ops = sorted({op for v in versions for op in data[v]["closures"]})
    per_op, distinct = {}, {}
    for op in ops:
        series = [(v, data[v]["closures"].get(op, {}).get("merkle")) for v in versions]
        runs = classes(series)
        boundaries = []
        for (_, last, h_old), (first, _, h_new) in zip(runs, runs[1:]):
            if h_old is None or h_new is None:
                boundaries.append({"from": last, "to": first, "kind": "presence"})
                continue
            old = data[last]["closures"][op]
            new = data[first]["closures"][op]
            delta = origin_delta(old, new)
            boundaries.append({"from": last, "to": first, **delta})
            for name in delta["changed"]:
                key = (last, first, name, body_hash(old["functions"][name]), body_hash(new["functions"][name]))
                distinct.setdefault(key, {"ops": [], "old": old["functions"][name],
                                          "new": new["functions"][name]})["ops"].append(op)
            for name in delta["added"] + delta["removed"]:
                side = new if name in delta["added"] else old
                key = (last, first, name, "+" if name in delta["added"] else "-", body_hash(side["functions"][name]))
                distinct.setdefault(key, {"ops": [], "body": side["functions"][name]})["ops"].append(op)
        per_op[op] = {"classes": [[a, b] for a, b, _ in runs], "hashes": [h for _, _, h in runs],
                      "boundaries": boundaries}
    return per_op, distinct


def write_diffs(distinct):
    diffs = OUT / "diffs"
    entries = []
    for key, info in sorted(distinct.items(), key=lambda kv: (version_key(kv[0][1]), kv[0][2])):
        last, first, name = key[:3]
        target = diffs / f"{last}..{first}" / f"{name}.diff"
        target.parent.mkdir(parents=True, exist_ok=True)
        if "old" in info:
            text = "".join(difflib.unified_diff(info["old"].splitlines(True), info["new"].splitlines(True),
                                                f"{last}/{name}", f"{first}/{name}", n=3))
            kind = "changed"
        else:
            kind = "added" if key[3] == "+" else "removed"
            text = f"# {kind} in {first}\n" + info["body"] + "\n"
        target.write_text(text)
        entries.append({"from": last, "to": first, "helper": name, "kind": kind,
                        "ops": sorted(set(info["ops"])), "diff": str(target.relative_to(OUT))})
    return entries


def layout_signature(layout):
    if not layout:
        return None
    types = layout.get("types") or {}

    def type_sig(t):
        info = types.get(t, {})
        return {k: info.get(k) for k in ("encoding", "numberOfBytes")}
    return [(e["label"], e["slot"], e["offset"], type_sig(e["type"])) for e in layout.get("storage", [])]


def analyze_layouts(versions):
    probes = sorted({p.stem for v in versions for p in (OUT / "raw" / v).glob("*.json")})
    result = {}
    for probe in probes:
        series = []
        for v in versions:
            path = OUT / "raw" / v / f"{probe}.json"
            sig = None
            if path.exists():
                record = json.loads(path.read_text())
                for unit in record["units"].values():
                    contract = unit["contracts"].get(probe)
                    if contract and contract["storageLayout"]:
                        sig = layout_signature(contract["storageLayout"])
                        break
            series.append((v, json.dumps(sig)))
        runs = classes(series)
        result[probe] = {"classes": [[a, b] for a, b, _ in runs],
                         "layouts": [json.loads(s) for _, _, s in runs]}
    return result


def main():
    versions, data = load_versions()
    per_op, distinct = analyze_closures(versions, data)
    entries = write_diffs(distinct)
    (OUT / "analysis.json").write_text(json.dumps({"versions": versions, "ops": per_op, "changes": entries},
                                                  indent=1))
    layouts = analyze_layouts(versions)
    (OUT / "layouts.json").write_text(json.dumps(layouts, indent=1))

    boundary_versions = {}
    for e in entries:
        boundary_versions.setdefault(f"{e['from']}..{e['to']}", []).append(e)
    print(f"{len(per_op)} operations, {len(entries)} distinct helper changes")
    for boundary in sorted(boundary_versions, key=lambda b: version_key(b.split("..")[1])):
        es = boundary_versions[boundary]
        print(f"  {boundary:16} {len(es):3} helper changes over "
              f"{len({o for e in es for o in e['ops']})} ops")
    print("layout classes:", {p: len(r["classes"]) for p, r in layouts.items()})


if __name__ == "__main__":
    main()
