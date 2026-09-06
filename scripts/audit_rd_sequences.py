#!/usr/bin/env python3
"""Audit reusable multi-opcode RD summaries and benchmark-local candidates.

The scanner is intentionally source based: it understands Lean comments, declaration
boundaries, decode hypotheses, ``evm_run`` lists, and ordinary RD step chains.  It does
not modify Lean sources.  The generated Markdown is deterministic for a fixed working
tree.
"""

from __future__ import annotations

import argparse
import dataclasses
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
REPORT = ROOT / "Reasoning" / "BYTECODE_SEQUENCE_REPORT.md"

DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:protected|private)\s+)?(theorem|lemma|def|abbrev)\s+([^\s({:]+)"
)
THEOREM_KINDS = {"theorem", "lemma"}
GENERATED_FIXTURE_RE = re.compile(r"Reasoning/ReachGenerated.*Test\.lean$")

PRIMITIVES = {
    "stop": "STOP", "add": "ADD", "mul": "MUL", "sub": "SUB", "div": "DIV",
    "sdiv": "SDIV", "mod": "MOD", "smod": "SMOD", "addmod": "ADDMOD",
    "mulmod": "MULMOD", "exp": "EXP", "signextend": "SIGNEXTEND",
    "lt": "LT", "gt": "GT", "slt": "SLT", "sgt": "SGT", "eq": "EQ",
    "iszero": "ISZERO", "and": "AND", "or": "OR", "xor": "XOR", "not": "NOT",
    "byte": "BYTE", "shl": "SHL", "shr": "SHR", "sar": "SAR",
    "keccak256": "KECCAK256", "address": "ADDRESS", "balance": "BALANCE",
    "origin": "ORIGIN", "caller": "CALLER", "callvalue": "CALLVALUE",
    "calldataload": "CALLDATALOAD", "calldatasize": "CALLDATASIZE",
    "calldatacopy": "CALLDATACOPY", "codesize": "CODESIZE", "codecopy": "CODECOPY",
    "gasprice": "GASPRICE", "extcodesize": "EXTCODESIZE", "extcodecopy": "EXTCODECOPY",
    "returndatasize": "RETURNDATASIZE", "returndatacopy": "RETURNDATACOPY",
    "extcodehash": "EXTCODEHASH", "blockhash": "BLOCKHASH", "coinbase": "COINBASE",
    "timestamp": "TIMESTAMP", "number": "NUMBER", "prevrandao": "PREVRANDAO",
    "gaslimit": "GASLIMIT", "chainid": "CHAINID", "selfbalance": "SELFBALANCE",
    "basefee": "BASEFEE", "blobhash": "BLOBHASH", "blobbasefee": "BLOBBASEFEE",
    "pop": "POP", "mload": "MLOAD", "mstore": "MSTORE", "mstore8": "MSTORE8",
    "sload": "SLOAD", "sstore": "SSTORE", "jump": "JUMP",
    "jumpiT": "JUMPI[taken]", "jumpiNT": "JUMPI[fallthrough]",
    "jumpdest": "JUMPDEST", "tload": "TLOAD", "tstore": "TSTORE",
    "mcopy": "MCOPY", "gas": "GAS", "log0": "LOG0", "log1": "LOG1",
    "log2": "LOG2", "log3": "LOG3", "log4": "LOG4", "create": "CREATE",
    "call": "CALL", "callcode": "CALLCODE", "ret": "RETURN",
    "delegatecall": "DELEGATECALL", "create2": "CREATE2", "staticcall": "STATICCALL",
    "rev": "REVERT", "invalid": "INVALID", "selfdestruct": "SELFDESTRUCT",
}
for _i in range(1, 33):
    PRIMITIVES[f"push{_i}"] = f"PUSH{_i}"
for _i in range(1, 17):
    PRIMITIVES[f"dup{_i}"] = f"DUP{_i}"
    PRIMITIVES[f"swap{_i}"] = f"SWAP{_i}"
PRIMITIVES["push0"] = "PUSH0"
PRIMITIVES["pushConst"] = "PUSH{width}"

# Reach helpers whose operational meaning is one EVM opcode.
PRIMITIVES.update({
    "routine1": "JUMP", "routine2": "JUMP", "routine3": "JUMP",
    "routine4": "JUMP", "routine5": "JUMP", "routine6": "JUMP",
    "routine7": "JUMP", "routine8": "JUMP", "routine9": "JUMP",
    "routine9c": "JUMP", "routine10": "JUMP", "routine11": "JUMP",
    "routine12": "JUMP", "routine13": "JUMP", "routine14": "JUMP",
    # High-level Reach wrappers still execute exactly one opcode.  Keeping
    # these aliases here is important: otherwise extraction silently stops at
    # the first wrapper and reports a truncated Solidity sequence.
    "rawGas": "GAS", "rawReturndatacopy": "RETURNDATACOPY",
    "rawMstore": "MSTORE", "rawCalldatacopy": "CALLDATACOPY",
    "rawCodecopy": "CODECOPY", "rawMload": "MLOAD",
    "rawSstore": "SSTORE", "rawKeccak256": "KECCAK256",
    "rawSload": "SLOAD", "rawLog1": "LOG1", "rawLog3": "LOG3",
    "rawLog4": "LOG4", "rawRet": "RETURN", "rawRev": "REVERT",
})


@dataclasses.dataclass
class Decl:
    path: Path
    line: int
    kind: str
    name: str
    text: str
    header: str
    body: str
    marker: str = ""
    ops: list[str] = dataclasses.field(default_factory=list)
    extraction: str = ""
    components: list[str] = dataclasses.field(default_factory=list)
    uses: Counter = dataclasses.field(default_factory=Counter)
    ambiguous_uses: int = 0

    @property
    def rel(self) -> str:
        return self.path.relative_to(ROOT).as_posix()

    @property
    def surface(self) -> str:
        return self.name


def source_files() -> list[Path]:
    """Return non-ignored Lean files, including untracked working-tree sources."""
    proc = subprocess.run(
        ["rg", "--files", "-g", "*.lean"], cwd=ROOT, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True,
    )
    return sorted((ROOT / line) for line in proc.stdout.splitlines() if line)


def dss_summary_pattern_occurrences() -> list[tuple[str, int, int]]:
    """Count registered summariser patterns in DSS bytecode, within basic blocks.

    These counts are deliberately separate from Lean source-use counts: one is
    compiled-bytecode evidence, while the other measures proof-library reuse.
    """
    import check_rd_blocks_corpus as corpus
    import generate_rd_blocks as generator

    counts: Counter[str] = Counter()
    artifacts: dict[str, set[str]] = defaultdict(set)
    cases = corpus.discover([ROOT / "Benchmarks" / "Dss"])
    for case in cases:
        code = generator.strip_solidity_metadata(case.code)
        for block in generator.blocks(generator.disassemble(code)):
            for index in range(len(block)):
                pattern = generator.match_sequence(block, index)
                if pattern is not None:
                    counts[pattern.name] += 1
                    artifacts[pattern.name].add(case.label)
    return [(pattern.name, counts[pattern.name], len(artifacts[pattern.name]))
            for pattern in generator.SEQUENCE_PATTERNS if counts[pattern.name]]


def strip_comments(text: str) -> str:
    """Replace nested Lean comments with whitespace while preserving lines and strings."""
    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    escaped = False
    while i < len(text):
        c = text[i]
        n = text[i + 1] if i + 1 < len(text) else ""
        if depth:
            if c == "/" and n == "-":
                depth += 1
                out.extend("  ")
                i += 2
            elif c == "-" and n == "/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
            continue
        if in_string:
            out.append("\n" if c == "\n" else " ")
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                in_string = False
            i += 1
            continue
        if c == '"':
            in_string = True
            out.append(c)
            i += 1
        elif c == "/" and n == "-":
            depth = 1
            out.extend("  ")
            i += 2
        elif c == "-" and n == "-":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def declarations(path: Path) -> list[Decl]:
    raw = path.read_text(encoding="utf-8")
    clean = strip_comments(raw)
    matches = list(DECL_RE.finditer(clean))
    result: list[Decl] = []
    raw_lines = raw.splitlines()
    for idx, match in enumerate(matches):
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(clean)
        chunk = clean[match.start():end]
        split = re.search(r":=\s*(?:by\b)?", chunk)
        if split:
            header, body = chunk[:split.start()], chunk[split.end():]
        else:
            header, body = chunk, ""
        line = clean.count("\n", 0, match.start()) + 1
        nearby = "\n".join(raw_lines[max(0, line - 8):line])
        marker_hits = re.findall(r"(?i)(LIBRARY CANDIDATE|GENERALIZES)", nearby)
        result.append(Decl(
            path=path, line=line, kind=match.group(1), name=match.group(2), text=chunk,
            header=header, body=body,
            marker=" + ".join(dict.fromkeys(x.upper() for x in marker_hits)),
        ))
    return result


PUSH_DECODE_RE = re.compile(
    r"some\s*\(\s*\.Push\s+\.PUSH(\d+)\s*,\s*some\s*\(\s*([^,\n]+?)\s*,\s*\d+\s*\)\s*\)",
    re.S,
)
GENERIC_PUSH_DECODE_RE = re.compile(
    r"some\s*\(\s*\.Push\s+([A-Za-z0-9_.]+)\s*,\s*some\s*\(\s*([^,\n]+?)\s*,",
    re.S,
)
OP_DECODE_RE = re.compile(r"some\s*\(\s*\.([A-Z][A-Z0-9]*)\s*,\s*\.none\s*\)")


def decode_ops(text: str) -> list[str]:
    hits: list[tuple[int, str]] = []
    for m in PUSH_DECODE_RE.finditer(text):
        operand = re.sub(r"\s+", " ", m.group(2)).strip()
        hits.append((m.start(), f"PUSH{m.group(1)}[{operand}]"))
    for m in GENERIC_PUSH_DECODE_RE.finditer(text):
        if ".PUSH" in m.group(1):
            continue
        operand = re.sub(r"\s+", " ", m.group(2)).strip()
        hits.append((m.start(), f"PUSH{{{m.group(1)}}}[{operand}]"))
    for m in OP_DECODE_RE.finditer(text):
        op = m.group(1)
        if op == "JUMPI":
            op = "JUMPI"
        hits.append((m.start(), op))
    return [op for _, op in sorted(hits)]


def matching_bracket(text: str, start: int, left: str = "[", right: str = "]") -> int:
    depth = 0
    in_string = False
    escaped = False
    pairs = {"(": ")", "[": "]", "{": "}"}
    stack: list[str] = []
    for i in range(start, len(text)):
        c = text[i]
        if in_string:
            if escaped:
                escaped = False
            elif c == "\\":
                escaped = True
            elif c == '"':
                in_string = False
            continue
        if c == '"':
            in_string = True
        elif c in pairs:
            stack.append(pairs[c])
        elif c in ")]}":
            if stack and c == stack[-1]:
                stack.pop()
                if not stack:
                    return i
    return -1


def split_top_level(text: str) -> list[str]:
    pieces: list[str] = []
    start = 0
    stack: list[str] = []
    pairs = {"(": ")", "[": "]", "{": "}"}
    for i, c in enumerate(text):
        if c in pairs:
            stack.append(pairs[c])
        elif c in ")]}":
            if stack and c == stack[-1]:
                stack.pop()
        elif c == "," and not stack:
            pieces.append(text[start:i])
            start = i + 1
    pieces.append(text[start:])
    return pieces


def macro_events(body: str) -> list[tuple[int, list[str]]]:
    events: list[tuple[int, list[str]]] = []
    pos = 0
    while True:
        m = re.search(r"\bevm_run\b.*?\bwith\s*\[", body[pos:], re.S)
        if not m:
            break
        opening = pos + m.end() - 1
        closing = matching_bracket(body, opening)
        if closing < 0:
            break
        block_ops: list[str] = []
        for piece in split_top_level(body[opening + 1:closing]):
            step = piece.strip()
            sm = re.match(r"(?:raw\s+)?([A-Za-z][A-Za-z0-9_]*)\b(.*)", step, re.S)
            if not sm:
                continue
            name, args = sm.group(1), sm.group(2).strip()
            if name in PRIMITIVES:
                op = PRIMITIVES[name]
                if op.startswith("PUSH") and name != "push0":
                    operand = args.split()[0] if args else "…"
                    op += f"[{operand}]"
                block_ops.append(op)
        events.append((pos + m.start(), block_ops))
        pos = closing + 1
    return events


def macro_ops(body: str) -> list[str]:
    return [op for _, ops in macro_events(body) for op in ops]


def chain_events(body: str) -> list[tuple[int, list[str]]]:
    hits: list[tuple[int, str]] = []
    names = "|".join(sorted(map(re.escape, PRIMITIVES), key=len, reverse=True))
    pattern = re.compile(
        rf"(?P<prefix>\bRD\.|\|>\.|\b(?:rd[A-Za-z0-9_]*|r\d+|h)\.)(?P<name>{names})\b"
    )
    macro_ranges: list[tuple[int, int]] = []
    pos = 0
    while True:
        m = re.search(r"\bevm_run\b.*?\bwith\s*\[", body[pos:], re.S)
        if not m:
            break
        opening = pos + m.end() - 1
        closing = matching_bracket(body, opening)
        if closing < 0:
            break
        macro_ranges.append((pos + m.start(), closing + 1))
        pos = closing + 1
    for m in pattern.finditer(body):
        if any(a <= m.start() < b for a, b in macro_ranges):
            continue
        name = m.group("name")
        op = PRIMITIVES[name]
        if op.startswith("PUSH") and name != "push0":
            tail = body[m.end():]
            terms = re.findall(r"\s+(⟨[^\n]+?⟩|\([^\n]+?\)|[A-Za-z0-9_.]+)", tail[:300])
            operand_index = 1 if m.group("prefix").strip() == "RD." else 0
            operand = terms[operand_index] if len(terms) > operand_index else "…"
            operand = re.sub(r"\s+", " ", operand)
            op += f"[{operand}]"
        hits.append((m.start(), op))
    return [(pos, [op]) for pos, op in sorted(hits)]


def chain_ops(body: str) -> list[str]:
    return [op for _, ops in chain_events(body) for op in ops]


def normalize_op(op: str) -> str:
    if op.startswith("PUSH"):
        op = re.sub(r"\[[^]]*\]", "[*]", op)
    return op


def fingerprint(ops: list[str]) -> str:
    return " · ".join(normalize_op(op) for op in ops)


def theorem_refs(body: str, base_to_name: dict[str, str]) -> list[tuple[int, str]]:
    hits: list[tuple[int, str]] = []
    pattern = re.compile(
        r"(?<![A-Za-z0-9_])(?:Reasoning\.(?:Theory|Reach)\.)?(?:RD\.)?"
        r"([A-Za-z][A-Za-z0-9_]*)(?![A-Za-z0-9_])"
    )
    for match in pattern.finditer(body):
        name = base_to_name.get(match.group(1))
        if name:
            hits.append((match.start(), name))
    return sorted(hits)


def infer_sequences(decls: list[Decl]) -> None:
    defs = {d.name: d for d in decls if d.kind not in THEOREM_KINDS}
    theorems = [d for d in decls if d.kind in THEOREM_KINDS]

    # First pass: explicit decode contracts, then referenced well-formedness definitions.
    for d in theorems:
        ops = decode_ops(d.header)
        extraction = "decode premises"
        if len(ops) < 2:
            refs = re.findall(r"\b([A-Za-z][A-Za-z0-9_]*(?:Wf|WellFormed))\b", d.header)
            for ref in refs:
                target = defs.get(ref)
                if target:
                    candidate = decode_ops(target.text)
                    if len(candidate) > len(ops):
                        ops = candidate
                        extraction = f"{ref} decode contract"
        # Any explicit decode premise is authoritative, even for a one-opcode theorem.
        # Do not mistake semantic helper calls in that proof (for example `.balance`) for
        # additional EVM steps.
        if not ops:
            mops = macro_ops(d.body)
            cops = chain_ops(d.body)
            ops = mops if len(mops) >= len(cops) else cops
            extraction = "evm_run proof" if ops is mops else "RD proof chain"
        branch_hints = [
            "JUMPI[taken]" if item == "jumpiT" else "JUMPI[fallthrough]"
            for item in re.findall(r"\.(jumpiT|jumpiNT)\b", d.body)
        ]
        if branch_hints:
            hint_index = 0
            for i, op in enumerate(ops):
                if op == "JUMPI" and hint_index < len(branch_hints):
                    ops[i] = branch_hints[hint_index]
                    hint_index += 1
        d.ops = ops
        d.extraction = extraction

    # Second pass: expand summaries used by wrappers and interleave them with direct
    # evm_run/chain fragments, retaining the component names as provenance.
    by_name = {d.name: d for d in theorems if len(d.ops) >= 2}
    base_to_name: dict[str, str] = {}
    for name in by_name:
        base_to_name.setdefault(name.split(".")[-1], name)
    relevant = [d for d in theorems if d.rel.startswith(("Reasoning/", "Benchmarks/"))]
    for _ in range(3):
        for d in relevant:
            refs = theorem_refs(d.body, base_to_name)
            refs = [(pos, name) for pos, name in refs if name != d.name]
            d.components = list(dict.fromkeys(name for _, name in refs))
            if refs and d.extraction in {"evm_run proof", "RD proof chain", "expanded component summaries"}:
                events = macro_events(d.body) + chain_events(d.body)
                events += [(pos, by_name[name].ops) for pos, name in refs if name in by_name]
                expanded = [op for _, part in sorted(events, key=lambda item: item[0]) for op in part]
                if len(expanded) >= 2:
                    d.ops = expanded
                    d.extraction = "expanded component summaries"
        by_name = {d.name: d for d in theorems if len(d.ops) >= 2}

    # Components can determine branch direction even when the outer theorem's decode
    # contract only says JUMPI.
    for d in relevant:
        inherited = [op for name in d.components for op in by_name.get(name, d).ops
                     if op.startswith("JUMPI[")]
        if inherited:
            j = 0
            for i, op in enumerate(d.ops):
                if op == "JUMPI" and j < len(inherited):
                    d.ops[i] = inherited[j]
                    j += 1


def result_type(d: Decl) -> str:
    """Return the declaration result following the outermost type colon."""
    stack: list[str] = []
    pairs = {"(": ")", "[": "]", "{": "}"}
    colon = -1
    for i, char in enumerate(d.header):
        if char in pairs:
            stack.append(pairs[char])
        elif char in ")]}":
            if stack and char == stack[-1]:
                stack.pop()
        elif char == ":" and not stack:
            colon = i
    return d.header[colon + 1:] if colon >= 0 else ""


def has_rd_result(d: Decl) -> bool:
    return bool(re.match(r"\s*(?:∃[^,]+,\s*)?RD(?:ret|rev)?\b", result_type(d), re.S))


def contract_unit(path: Path) -> str:
    parts = path.relative_to(ROOT).parts
    if len(parts) >= 3 and parts[0] == "Benchmarks" and parts[1] == "Dss":
        return "/".join(parts[:3])
    if len(parts) >= 2:
        return "/".join(parts[:2])
    return parts[0]


def classify_effects(ops: list[str], header: str) -> str:
    tags: list[str] = []
    bases = [re.sub(r"\[.*", "", op) for op in ops]
    for needles, label in [
        ({"CALLDATALOAD", "CALLDATASIZE", "CALLDATACOPY"}, "calldata"),
        ({"MLOAD"}, "memory read"), ({"MSTORE", "MSTORE8", "MCOPY"}, "memory write"),
        ({"KECCAK256"}, "hashing"), ({"SLOAD"}, "storage read"),
        ({"SSTORE"}, "storage write"),
        ({"CALL", "CALLCODE", "DELEGATECALL", "STATICCALL"}, "external call"),
        ({"LOG0", "LOG1", "LOG2", "LOG3", "LOG4"}, "event log"),
        ({"RETURN", "STOP"}, "success halt"), ({"REVERT", "INVALID"}, "failure halt"),
        ({"JUMPI"}, "branch"), ({"JUMP"}, "control transfer"),
    ]:
        if any(base in needles for base in bases) and label not in tags:
            tags.append(label)
    if "addressModulus" in header or "solcAddrMask" in header:
        tags.append("address canonicality")
    return ", ".join(tags) if tags else "stack/control normalization"


def conclusion(d: Decl) -> str:
    text = result_type(d)
    text = re.sub(r"\s+", " ", text).strip()
    return text if len(text) <= 300 else text[:297] + "…"


def imports(path: Path, stripped: str) -> set[Path]:
    result: set[Path] = set()
    for module in re.findall(r"(?m)^\s*import\s+([A-Za-z0-9_.]+)", stripped):
        candidate = ROOT / (module.replace(".", "/") + ".lean")
        if candidate.exists():
            result.add(candidate)
    return result


def count_uses(all_decls: list[Decl], files: list[Path]) -> None:
    by_surface: dict[str, list[Decl]] = defaultdict(list)
    for d in all_decls:
        if len(d.ops) >= 2:
            by_surface[d.surface].append(d)

    clean_sources = {p: strip_comments(p.read_text(encoding="utf-8")) for p in files}
    import_graph = {p: imports(p, text) for p, text in clean_sources.items()}

    closure_cache: dict[Path, set[Path]] = {}

    def closure(path: Path, active: set[Path] | None = None) -> set[Path]:
        if path in closure_cache:
            return closure_cache[path]
        active = set() if active is None else active
        if path in active:
            return set()
        active.add(path)
        seen: set[Path] = set()
        for item in import_graph.get(path, ()):
            seen.add(item)
            seen.update(closure(item, active))
        active.remove(path)
        closure_cache[path] = seen
        return seen

    closures = {p: closure(p) for p in files}
    by_base: dict[str, list[Decl]] = defaultdict(list)
    for targets in by_surface.values():
        for target in targets:
            by_base[target.surface.split(".")[-1]].append(target)

    # Tokenize each source once. This keeps a full-repository audit linear in source size
    # rather than recompiling one regular expression per theorem per file.
    wanted = set(by_base)
    for path, text in clean_sources.items():
        counts = Counter(token for token in re.findall(r"\b[A-Za-z][A-Za-z0-9_]*\b", text)
                         if token in wanted)
        for base, count in counts.items():
            targets = by_base[base]
            decls_here = sum(1 for d in targets if d.path == path)
            count = max(0, count - decls_here)
            if not count:
                continue
            local = [d for d in targets if d.path == path]
            accessible = [d for d in targets if d.path in closures[path]]
            choices = local or accessible or (targets if len(targets) == 1 else [])
            if len(choices) == 1:
                choices[0].uses[path.parts[len(ROOT.parts)] if len(path.parts) > len(ROOT.parts) else "Other"] += count
            else:
                for d in targets:
                    d.ambiguous_uses += count


def markdown_link(d: Decl) -> str:
    rel_from_report = Path("..") / d.path.relative_to(ROOT)
    return f"[`{d.name}`]({rel_from_report.as_posix()}#L{d.line})"


def use_total(d: Decl) -> int:
    return sum(d.uses.values())


def use_breakdown(d: Decl) -> str:
    parts = [f"{key} {d.uses[key]}" for key in sorted(d.uses) if d.uses[key]]
    if d.ambiguous_uses:
        parts.append(f"ambiguous {d.ambiguous_uses}")
    return ", ".join(parts) if parts else "none"


def entry_lines(index: int, members: list[Decl], status: str) -> list[str]:
    representative = members[0]
    aggregate = sum(use_total(d) for d in members)
    ambiguous = max((d.ambiguous_uses for d in members), default=0)
    title = representative.name
    lines = [f"### {status[0]}{index:03d} — `{title}`", "",
             f"`{' → '.join(representative.ops)}`", "",
             f"- **Length:** {len(representative.ops)} opcodes", 
             f"- **Normalized fingerprint:** `{fingerprint(representative.ops)}`",
             f"- **Effect:** {classify_effects(representative.ops, representative.header)}",
             f"- **Aggregate direct uses:** {aggregate}" +
             (f" plus {ambiguous} unresolved duplicate-name references" if ambiguous else ""),
             f"- **Extraction:** {representative.extraction}"]
    if representative.components:
        lines.append("- **Composition:** " + ", ".join(f"`{x}`" for x in representative.components))
    lines += ["", "| Theorem | Direct uses | Directory breakdown | Result |", "|---|---:|---|---|"]
    for d in members:
        lines.append(
            f"| {markdown_link(d)} | {use_total(d)} | {use_breakdown(d)} | {conclusion(d).replace('|', '&#124;')} |"
        )
    lines.append("")
    return lines


def render(reasoning: list[Decl], candidates: list[Decl], rejected_count: int) -> str:
    reason_groups: dict[str, list[Decl]] = defaultdict(list)
    candidate_groups: dict[str, list[Decl]] = defaultdict(list)
    for d in reasoning:
        reason_groups[fingerprint(d.ops)].append(d)
    for d in candidates:
        candidate_groups[fingerprint(d.ops)].append(d)

    for group in list(reason_groups.values()) + list(candidate_groups.values()):
        group.sort(key=lambda d: (d.rel, d.line, d.name))

    reason_sorted = sorted(reason_groups.values(), key=lambda g: (-sum(use_total(d) for d in g), g[0].name))
    candidate_sorted = sorted(candidate_groups.values(), key=lambda g: (-sum(use_total(d) for d in g), g[0].name))
    reason_uses = sum(use_total(d) for d in reasoning)
    candidate_uses = sum(use_total(d) for d in candidates)
    explicit = sum(1 for d in candidates if d.marker)
    reasoning_names = {d.name for d in reasoning}
    duplicate = sum(1 for g in candidate_groups.values() if len({contract_unit(d.path) for d in g}) >= 2)

    # This is deliberately a structural, rather than semantic, novelty test.  Source
    # scanning cannot decide whether two differently stated postconditions are
    # logically equivalent.  At group level, use a disjoint priority order so the
    # headline counts add up: exact known path, direct composition, then no detected
    # multi-opcode reuse.
    novelty_groups: dict[str, list[list[Decl]]] = defaultdict(list)
    for fp, group in candidate_groups.items():
        if fp in reason_groups:
            novelty_groups["exact"].append(group)
        elif any(any(name in reasoning_names for name in d.components) for d in group):
            novelty_groups["composed"].append(group)
        else:
            novelty_groups["potential"].append(group)

    def novelty_stats(category: str) -> tuple[int, int, int]:
        groups = novelty_groups[category]
        decls = [d for group in groups for d in group]
        return len(groups), len(decls), sum(use_total(d) for d in decls)

    exact_paths, exact_theorems, exact_uses = novelty_stats("exact")
    composed_paths, composed_theorems, composed_uses = novelty_stats("composed")
    potential_paths, potential_theorems, potential_uses = novelty_stats("potential")
    reasoning_composites = sum(bool(d.components) for d in reasoning)
    bytecode_occurrences = dss_summary_pattern_occurrences()

    def ranking_lines(title: str, groups: list[list[Decl]], prefix: str) -> list[str]:
        ranked = [f"### {title}", "",
                  "| Rank | Representative theorem | Opcodes | Theorems | Aggregate direct uses |",
                  "|---:|---|---:|---:|---:|"]
        for index, group in enumerate(groups, 1):
            ranked.append(
                f"| {prefix}{index:03d} | {markdown_link(group[0])} | {len(group[0].ops)} | "
                f"{len(group)} | {sum(use_total(d) for d in group)} |"
            )
        ranked.append("")
        return ranked

    lines = [
        "# Bytecode Sequence Theorem Report", "",
        "<!-- Generated by scripts/audit_rd_sequences.py; do not edit by hand. -->", "",
        "This report inventories reusable theorems that execute **two or more EVM opcodes** and",
        "present an `RD`, `RDret`, or `RDrev` result. It also identifies benchmark-local",
        "sequences whose statements or repetition indicate that they can be factored into the",
        "reasoning library.", "",
        "## Executive summary", "",
        "| Category | Theorems | Distinct opcode paths | Direct uses |", "|---|---:|---:|---:|",
        f"| Factored in `Reasoning/` | {len(reasoning)} | {len(reason_groups)} | {reason_uses} |",
        f"| Generic but benchmark-local | {len(candidates)} | {len(candidate_groups)} | {candidate_uses} |",
        "", f"Of the benchmark-local candidates, {explicit} carry an explicit `LIBRARY CANDIDATE` or",
        f"`GENERALIZES` marker; {duplicate} opcode paths occur in at least two benchmark families.",
        f"Another {rejected_count} benchmark-local multi-opcode RD theorems were inspected but",
        "left out because their statements and use sites remain contract-specific.", "",
        "### Structural novelty assessment", "",
        "Whether a theorem's postcondition is logically new cannot be decided from source syntax.",
        "The following conservative proxy asks whether its opcode path is already factored or its",
        "proof directly invokes a known multi-opcode `Reasoning/` summary. Categories are disjoint", 
        "at the normalized-path level.", "",
        "| Benchmark-candidate category | Distinct paths | Theorems | Direct uses |", "|---|---:|---:|---:|",
        f"| Exact path already in `Reasoning/` | {exact_paths} | {exact_theorems} | {exact_uses} |",
        f"| Directly composes a `Reasoning/` sequence summary | {composed_paths} | {composed_theorems} | {composed_uses} |",
        f"| No reusable multi-opcode summary detected (potentially new) | {potential_paths} | {potential_theorems} | {potential_uses} |",
        "",
        f"Thus {exact_paths + composed_paths} of {len(candidate_groups)} candidate paths",
        f"({exact_theorems + composed_theorems} of {len(candidates)} theorems) primarily expose reuse or",
        f"refactoring opportunities, while {potential_paths} paths ({potential_theorems} theorems) are",
        "potential additions to the reusable pattern vocabulary. This does not claim semantic",
        "independence; that requires comparing the actual preconditions and postconditions.", "",
        f"Inside `Reasoning/` itself, {reasoning_composites} of {len(reasoning)} inventoried theorems",
        "explicitly compose other named summaries; the remainder present their path directly.", "",
        "### Registered summariser patterns in DSS bytecode", "",
        "These are actual within-basic-block bytecode matches, not Lean theorem references.",
        "Overlapping specializations use the generator's longest-first precedence.", "",
        "| Pattern | Bytecode occurrences | DSS artifacts |", "|---|---:|---:|",
        *[f"| `{name}` | {count} | {artifact_count} |"
          for name, count, artifact_count in bytecode_occurrences], "",
        "## Method", "",
        "- A sequence must establish an `RD`-family result and execute at least two opcodes.",
        "- Foundational one-opcode wrappers and non-executing conversions from `RD` to another logic are excluded.",
        "- `Reasoning/ReachGenerated*Test.lean` files are excluded as generator fixtures.",
        "- Opcode paths come from decode contracts, well-formedness predicates, `evm_run`, or RD proof chains.",
        "- Concrete operands and PCs are shown, but fingerprints wildcard operands while preserving PUSH widths.",
        "- Uses are direct, comment-free source references. Calls through another summary appear under composition, not as transitive uses.",
        "- Registered summary patterns are also counted directly in DSS bytecode, independently of source uses.",
        "- Duplicate local names are resolved through their source file and transitive imports; unresolved cases are labeled.",
        "", "Regenerate with `python3 scripts/audit_rd_sequences.py --write`; verify freshness with",
        "`python3 scripts/audit_rd_sequences.py --check`.", "",
        "## Ranking by direct use count", "",
        "Each ranking is over distinct normalized opcode paths. Uses of theorem aliases sharing",
        "a path are aggregated; unresolved duplicate-name references are not included in the",
        "numeric rank. Ties are ordered by representative theorem name. Rank identifiers match",
        "the detailed entries below.", "",
    ]
    lines.extend(ranking_lines("Factored `Reasoning/` paths", reason_sorted, "R"))
    lines.extend(ranking_lines("Generic benchmark-local paths", candidate_sorted, "C"))
    lines += ["## Factored reasoning sequences", "",
              "Entries remain in descending aggregate-use order, matching the ranking above.", ""]
    for i, group in enumerate(reason_sorted, 1):
        lines.extend(entry_lines(i, group, "Reasoning"))

    lines += ["## Generic benchmark-local candidates", "",
              "Candidates are included through an explicit marker, a bytecode-agnostic statement",
              "(`code` plus decode premises), or recurrence in multiple benchmark families.",
              "They remain in descending aggregate-use order, matching the ranking above.", ""]
    for i, group in enumerate(candidate_sorted, 1):
        units = sorted({contract_unit(d.path) for d in group})
        evidence: list[str] = []
        if any(d.marker for d in group):
            evidence.append("explicit marker")
        if any(re.search(r"\{code\s*:\s*ByteArray\}", d.header) and "decode code" in d.header for d in group):
            evidence.append("bytecode-agnostic statement")
        if len(units) >= 2:
            evidence.append("repeated across " + ", ".join(f"`{x}`" for x in units))
        lines.extend(entry_lines(i, group, "Candidate"))
        lines.insert(len(lines) - 1, "- **Candidate evidence:** " + "; ".join(evidence))
        existing = reason_groups.get(fingerprint(group[0].ops))
        component_existing = sorted({name for d in group for name in d.components
                                     if name in reasoning_names})
        if existing:
            lines.insert(len(lines) - 1, "- **Structural novelty:** exact normalized path already exists in `Reasoning/`.")
            lines.insert(len(lines) - 1, "- **Recommendation:** replace or derive from " +
                         ", ".join(f"`{d.name}`" for d in existing) + ".")
        elif component_existing:
            lines.insert(len(lines) - 1, "- **Structural novelty:** directly composes an existing `Reasoning/` sequence summary.")
            lines.insert(len(lines) - 1, "- **Recommendation:** retain only as a thin wrapper over " +
                         ", ".join(f"`{name}`" for name in component_existing) + ".")
        elif len(units) >= 2:
            lines.insert(len(lines) - 1, "- **Structural novelty:** no reusable multi-opcode `Reasoning/` summary detected.")
            lines.insert(len(lines) - 1, "- **Recommendation:** promote one parameterized version to `Reasoning/Solc.lean`.")
        else:
            lines.insert(len(lines) - 1, "- **Structural novelty:** no reusable multi-opcode `Reasoning/` summary detected.")
            lines.insert(len(lines) - 1, "- **Recommendation:** generalize and promote after validating a second compiler instance.")

    lines += ["## Notes and limitations", "",
              "- A theorem may describe a family of paths when its PUSH width is itself a parameter.",
              "- Opcode equality does not imply equal semantic postconditions; grouped aliases retain their individual result statements.",
              "- Source extraction is checked conservatively. New proof idioms must be added to the scanner before they enter the report.", ""]
    return "\n".join(lines)


def audit() -> tuple[str, list[Decl], list[Decl]]:
    files = source_files()
    all_decls = [d for path in files for d in declarations(path)]
    infer_sequences(all_decls)

    reasoning = [
        d for d in all_decls
        if d.kind in THEOREM_KINDS and d.rel.startswith("Reasoning/")
        and not GENERATED_FIXTURE_RE.search(d.rel) and has_rd_result(d) and len(d.ops) >= 2
    ]

    local_pool = [
        d for d in all_decls
        if d.kind in THEOREM_KINDS and d.rel.startswith("Benchmarks/")
        and has_rd_result(d) and len(d.ops) >= 2
    ]
    # Recurrence is evidence only when the path came from an explicit decode contract or
    # one unambiguous evm_run chain. Short fragments scraped from a larger proof chain are
    # not sufficient evidence that the theorem itself presents exactly that path.
    repeatable = [
        d for d in local_pool
        if d.extraction == "decode premises"
        or d.extraction.endswith(" decode contract")
        or (len(macro_events(d.body)) == 1)
    ]
    fp_units: dict[str, set[str]] = defaultdict(set)
    for d in repeatable:
        fp_units[fingerprint(d.ops)].add(contract_unit(d.path))
    candidates = []
    for d in local_pool:
        structural = bool(re.search(r"\{code\s*:\s*ByteArray\}", d.header) and "decode code" in d.header)
        repeated = d in repeatable and len(fp_units[fingerprint(d.ops)]) >= 2
        if d.marker or structural or repeated:
            candidates.append(d)
    count_uses(reasoning + candidates, files)
    return render(reasoning, candidates, len(local_pool) - len(candidates)), reasoning, candidates


def self_test() -> None:
    sample = '''theorem fake {code : ByteArray}\n    (h0 : decode code pc = some (.PUSH0, .none))\n+    /- nested /- RD.bad -/ comment -/\n+    (h1 : decode code (pc + 1) = some (.MSTORE, .none)) : RD x := by\n+      exact h.push0 h0 |>.mstore h1\n+'''
    clean = strip_comments(sample)
    assert "RD.bad" not in clean
    assert decode_ops(clean) == ["PUSH0", "MSTORE"]
    assert macro_ops("exact evm_run h with [push1 x, dup1, jumpiNT hz]") == [
        "PUSH1[x]", "DUP1", "JUMPI[fallthrough]"
    ]
    assert fingerprint(["PUSH2[target]", "JUMPI[taken]"]) == "PUSH2[*] · JUMPI[taken]"
    assert chain_ops("exact h.rawMstore 0 mem aw hd hc hm ha hov |>.rawKeccak256") == [
        "MSTORE", "KECCAK256"
    ]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--write", action="store_true", help="write the checked-in Markdown report")
    mode.add_argument("--check", action="store_true", help="fail if the checked-in report is stale")
    mode.add_argument("--self-test", action="store_true", help="run scanner unit tests")
    args = parser.parse_args(argv)
    self_test()
    if args.self_test:
        print("audit_rd_sequences: self-test passed")
        return 0
    report, reasoning, candidates = audit()
    if args.write:
        REPORT.write_text(report, encoding="utf-8")
        print(f"wrote {REPORT.relative_to(ROOT)} ({len(reasoning)} reasoning theorems, "
              f"{len(candidates)} benchmark candidates)")
        return 0
    if args.check:
        current = REPORT.read_text(encoding="utf-8") if REPORT.exists() else ""
        if current != report:
            print(f"stale report: run {Path(__file__).relative_to(ROOT)} --write", file=sys.stderr)
            return 1
        print("bytecode sequence report is current")
        return 0
    sys.stdout.write(report)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
