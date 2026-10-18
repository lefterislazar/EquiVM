#!/usr/bin/env python3
"""Extract and normalize the Yul helper closure of every probe operation.

The unoptimized IR prints one statement per line, so normalization works line by line:
comments are dropped, AST ids are stripped from function and type names, local variables are
renamed by order of first occurrence within each function, and number literals are printed in
decimal.  Two closures with the same normalized text implement the same algorithm.

Reads ``out/raw/<version>/<probe>.json`` and writes ``out/closures/<version>.json``:
``{"<probe>.<op>": {"hash", "functions": {name: normalized body}}}``.
"""

import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
RAW = HERE / "out" / "raw"
CLOSURES = HERE / "out" / "closures"

TOKEN = re.compile(r"""
    (?P<string>hex"[0-9a-fA-F]*"|"(?:[^"\\]|\\.)*")
  | (?P<number>0x[0-9a-fA-F]+|[0-9]+)
  | (?P<ident>[A-Za-z_$][A-Za-z0-9_$.]*)
  | (?P<arrow>->)
  | (?P<assign>:=)
  | (?P<punct>[{}(),:])
  | (?P<space>\s+)
""", re.VERBOSE)
COMMENT = re.compile(r"/\*.*?\*/|//[^\n]*", re.DOTALL)
KEYWORDS = {"function", "let", "if", "switch", "case", "default", "for", "break", "continue",
            "leave", "true", "false"}
# Names whose trailing `_<digits>` is an AST id: user functions, modifiers, constructors, getters.
AST_SUFFIXED = re.compile(r"^((?:external_)?fun|modifier|constructor|getter_fun|usr\$)\w*?_\d+$")


def tokenize(line):
    tokens, pos = [], 0
    while pos < len(line):
        match = TOKEN.match(line, pos)
        if not match:
            raise ValueError(f"cannot tokenize {line[pos:pos + 40]!r}")
        pos = match.end()
        if match.lastgroup != "space":
            tokens.append((match.lastgroup, match.group()))
    return tokens


def canonical_name(name):
    """Drop AST ids: `fun_w_p_123` -> `fun_w_p`, `t_struct$_S_$16_storage` -> `t_struct$_S_$_storage`."""
    name = re.sub(r"\$(\d+)", "$", name)
    if AST_SUFFIXED.match(name):
        name = re.sub(r"_\d+$", "", name)
    return name


def deployed_code(ir):
    """The source text of the `<C>_deployed` object's code block (function definitions only)."""
    ir = COMMENT.sub("", ir)
    start = re.search(r'object\s+"[^"]*_deployed"\s*\{\s*code\s*\{', ir)
    if not start:
        return ""
    depth, pos = 1, start.end()
    while depth and pos < len(ir):
        depth += {"{": 1, "}": -1}.get(ir[pos], 0)
        pos += 1
    return ir[start.end():pos - 1]


def split_functions(code):
    """{name: [token lines]} for every top-level `function` in the code block."""
    functions, current, depth = {}, None, 0
    for raw in code.splitlines():
        tokens = tokenize(raw)
        if not tokens:
            continue
        if depth == 0 and tokens[0] == ("ident", "function"):
            current = tokens[1][1]
            functions[current] = []
        if current is not None:
            functions[current].append(tokens)
        depth += sum(1 for k, t in tokens if t == "{") - sum(1 for k, t in tokens if t == "}")
        if depth == 0:
            current = None
    return functions


def callees(lines, defined):
    called = set()
    for tokens in lines:
        for i, (k, t) in enumerate(tokens):
            nxt = tokens[i + 1][1] if i + 1 < len(tokens) else ""
            if k == "ident" and t in defined and nxt == "(" and not (i and tokens[i - 1][1] == "function"):
                called.add(t)
    return called


def normalize_function(lines, defined):
    """Pretty-printed body with canonical function names and positionally renamed locals."""
    renames, out, depth = {}, [], 0
    for tokens in lines:
        words = []
        for i, (kind, text) in enumerate(tokens):
            nxt = tokens[i + 1][1] if i + 1 < len(tokens) else ""
            if kind == "number":
                words.append(str(int(text, 0)))
            elif kind != "ident" or text in KEYWORDS:
                words.append(text)
            elif text in defined:
                words.append(canonical_name(text))
            elif nxt == "(" and not (i > 0 and tokens[i - 1][1] == "function"):
                words.append(text)  # EVM builtin
            else:
                words.append(renames.setdefault(text, f"v{len(renames)}"))
        line = " ".join(words).replace(" (", "(").replace("( ", "(").replace(" )", ")").replace(" ,", ",")
        depth -= line.startswith("}")
        out.append("    " * max(depth, 0) + line)
        depth += line.count("{") - line.count("}") + line.startswith("}")
    return "\n".join(out)


def closure_of(root, functions):
    seen, todo = set(), [root]
    defined = set(functions)
    while todo:
        name = todo.pop()
        if name in seen:
            continue
        seen.add(name)
        todo.extend(callees(functions[name], defined) - seen)
    return seen


def erase_callees(body, calls):
    """The body with its own name and every callee name replaced by `@`: what the function
    itself computes, independent of how its helpers are named."""
    names = sorted(set(calls) | {body.split("(", 1)[0].split()[-1]}, key=len, reverse=True)
    if not names:
        return body
    return re.sub(r"(?<![\w$.])(?:" + "|".join(re.escape(n) for n in names) + r")(?=\()", "@", body)


def merkle_hashes(bodies, calls):
    """Name-insensitive hash of every function: its erased body plus its callees' hashes, in
    call order.  Helper renames do not change it; any change in what is computed does."""
    memo = {}

    def go(name, stack=()):
        if name in memo:
            return memo[name]
        if name in stack:  # recursion: cut the cycle
            return "rec"
        body = bodies[name]
        order = [m.group(0)[:-1] for m in re.finditer(r"[A-Za-z_$][\w$.]*\(", body)
                 if m.group(0)[:-1] in calls[name]]
        parts = [erase_callees(body, calls[name])] + [go(c, stack + (name,)) for c in order]
        memo[name] = hashlib.sha256("\x00".join(parts).encode()).hexdigest()[:16]
        return memo[name]

    return {name: go(name) for name in bodies}


def op_root(functions, op):
    candidates = [f for f in functions if re.fullmatch(rf"fun_{re.escape(op)}_\d+", f)]
    return candidates[0] if candidates else None


def closures_for_ir(ir, ops):
    functions = split_functions(deployed_code(ir))
    defined = set(functions)
    result = {}
    for op in ops:
        root = op_root(functions, op)
        if root is None:
            continue
        members = closure_of(root, functions)
        bodies = {canonical_name(f): normalize_function(functions[f], defined) for f in members}
        calls = {canonical_name(f): sorted(canonical_name(c) for c in callees(functions[f], defined))
                 for f in members}
        text = "\n\n".join(bodies[n] for n in sorted(bodies))
        result[op] = {"root": canonical_name(root), "hash": hashlib.sha256(text.encode()).hexdigest()[:16],
                      "merkle": merkle_hashes(bodies, calls)[canonical_name(root)],
                      "functions": bodies, "calls": calls}
    return result


def probe_ops(probe_file):
    from run_matrix import OP_FUNCTION
    return [m.group(1) for line in probe_file.read_text().splitlines() if (m := OP_FUNCTION.match(line))]


def extract_version(version_dir):
    from run_matrix import PROBES
    closures, helpers = {}, {}
    for raw_file in sorted(version_dir.glob("*.json")):
        record = json.loads(raw_file.read_text())
        ops = probe_ops(PROBES / f"{record['probe']}.sol")
        for unit, data in record["units"].items():
            contract = data["contracts"].get(record["probe"])
            if not contract or not contract["ir"]:
                continue
            unit_ops = ops if unit == "*" else [unit]
            for op, closure in closures_for_ir(contract["ir"], unit_ops).items():
                closures[f"{record['probe']}.{op}"] = closure
                for name, body in closure["functions"].items():
                    if not name.startswith("fun_"):  # user functions repeat across probes
                        helpers.setdefault(name, body)
    return {"closures": closures, "helpers": helpers}


def main():
    CLOSURES.mkdir(parents=True, exist_ok=True)
    for version_dir in sorted(RAW.iterdir()):
        if not version_dir.is_dir():
            continue
        data = extract_version(version_dir)
        (CLOSURES / f"{version_dir.name}.json").write_text(json.dumps(data, indent=1, sort_keys=True))
        print(f"{version_dir.name:8} closures={len(data['closures'])} helpers={len(data['helpers'])}")


if __name__ == "__main__":
    main()
