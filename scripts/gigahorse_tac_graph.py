#!/usr/bin/env python3
"""Render a Gigahorse TAC control-flow graph linked to EVM disassembly.

Examples:
    scripts/gigahorse_tac_graph.py Examples/ERC20/.temp/Bytecode
    scripts/gigahorse_tac_graph.py Examples/ERC20/.temp/Bytecode/out/contract.tac

The script writes a Graphviz DOT file and, if Graphviz `dot` is available,
renders an image such as SVG, PNG, or PDF.
"""

from __future__ import annotations

import argparse
import csv
import html
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path


HEX_RE = re.compile(r"0x[0-9a-fA-F]+")
TAC_ID_RE = re.compile(r"0x[0-9a-fA-F]+(?:[A-Za-z]0x[0-9a-fA-F]+)*")
FUNCTION_RE = re.compile(r"^function\s+(.*?)\s*\{$")
BLOCK_RE = re.compile(r"^\s*Begin block\s+(.+?)\s*$")
PREV_SUCC_RE = re.compile(r"^\s*prev=\[(.*?)\],\s*succ=\[(.*?)\]\s*$")
TAC_STMT_RE = re.compile(rf"^\s*({TAC_ID_RE.pattern}):\s*(.*?)\s*$")
DASM_RE = re.compile(r"^\s*(0x[0-9a-fA-F]+):\s*(.*?)\s*$")
PRIVATE_CALL_RE = re.compile(r"\bCALLPRIVATE\b.*?\((0x[0-9a-fA-F]+)\)")


@dataclass
class Statement:
    addr: str
    text: str


@dataclass
class Block:
    function_index: int
    function_name: str
    label: str
    succ: list[str] = field(default_factory=list)
    statements: list[Statement] = field(default_factory=list)


@dataclass
class Function:
    index: int
    name: str
    blocks: list[Block] = field(default_factory=list)


def normalize_hex(value: str) -> str:
    return hex(int(value, 16))


def normalize_tac_id(value: str) -> str:
    parts = re.split(r"([A-Za-z])(?=0x)", value.strip())
    normalized: list[str] = []
    for part in parts:
        if part.startswith("0x"):
            normalized.append(normalize_hex(part))
        else:
            normalized.append(part)
    return "".join(normalized)


def split_list(value: str) -> list[str]:
    value = value.strip()
    if not value:
        return []
    return [normalize_tac_id(part) for part in value.split(",") if part.strip()]


@dataclass
class InputPaths:
    root: Path
    tac: Path
    dasm: Path
    statement_map: Path


def resolve_input_paths(
    input_path: Path,
    dasm_override: Path | None,
    statement_map_override: Path | None,
) -> InputPaths:
    if input_path.is_dir():
        if input_path.name == "out":
            root = input_path.parent
            tac_path = input_path / "contract.tac"
        else:
            root = input_path
            tac_path = input_path / "out" / "contract.tac"
    else:
        tac_path = input_path
        root = input_path.parent.parent if input_path.parent.name == "out" else input_path.parent

    dasm_path = dasm_override or root / "contract.dasm"
    statement_map_path = (
        statement_map_override or tac_path.parent / "TAC_Statement_OriginalStatement.csv"
    )
    return InputPaths(root, tac_path, dasm_path, statement_map_path)


def parse_tac(path: Path) -> list[Function]:
    functions: list[Function] = []
    current_function: Function | None = None
    current_block: Block | None = None

    with path.open(encoding="utf-8") as handle:
        for line_no, raw_line in enumerate(handle, 1):
            line = raw_line.rstrip("\n")

            function_match = FUNCTION_RE.match(line)
            if function_match:
                current_function = Function(len(functions), function_match.group(1))
                functions.append(current_function)
                current_block = None
                continue

            block_match = BLOCK_RE.match(line)
            if block_match:
                if current_function is None:
                    raise ValueError(f"{path}:{line_no}: block before function")
                current_block = Block(
                    current_function.index,
                    current_function.name,
                    normalize_tac_id(block_match.group(1)),
                )
                current_function.blocks.append(current_block)
                continue

            prev_succ_match = PREV_SUCC_RE.match(line)
            if prev_succ_match and current_block is not None:
                current_block.succ = split_list(prev_succ_match.group(2))
                continue

            stmt_match = TAC_STMT_RE.match(line)
            if stmt_match and current_block is not None:
                addr = normalize_tac_id(stmt_match.group(1))
                current_block.statements.append(
                    Statement(addr, f"{addr}: {stmt_match.group(2).strip()}")
                )

    return functions


def parse_dasm(path: Path) -> dict[str, str]:
    instructions: dict[str, str] = {}
    with path.open(encoding="utf-8") as handle:
        for raw_line in handle:
            match = DASM_RE.match(raw_line.rstrip("\n"))
            if not match:
                continue
            addr = normalize_hex(match.group(1))
            instructions[addr] = f"{addr}: {match.group(2).strip()}"
    return instructions


def parse_statement_map(path: Path) -> dict[str, list[str]]:
    mapping: dict[str, list[str]] = {}
    if not path.exists():
        return mapping

    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.reader(handle, delimiter="\t")
        for row in reader:
            if len(row) < 2:
                continue
            try:
                tac_addr = normalize_tac_id(row[0].strip())
                evm_addr = normalize_hex(row[1].strip())
            except ValueError:
                continue
            mapping.setdefault(tac_addr, []).append(evm_addr)
    return mapping


def function_matches(name: str, pattern: str | None) -> bool:
    if pattern is None:
        return True
    try:
        return re.search(pattern, name) is not None
    except re.error:
        return pattern in name


def truncate_lines(lines: list[str], max_lines: int) -> list[str]:
    if max_lines <= 0 or len(lines) <= max_lines:
        return lines
    remaining = len(lines) - max_lines
    return lines[:max_lines] + [f"... {remaining} more"]


def html_line(line: str) -> str:
    return html.escape(line, quote=False)


def html_table(title: str, rows: list[str], fill: str, border: str) -> str:
    if not rows:
        rows = ["(no statements)"]

    parts = [
        "<<TABLE BORDER=\"1\" CELLBORDER=\"0\" CELLSPACING=\"0\" CELLPADDING=\"4\" "
        f"COLOR=\"{border}\" BGCOLOR=\"{fill}\">",
        f"<TR><TD BALIGN=\"LEFT\"><FONT POINT-SIZE=\"18\"><B>{html_line(title)}</B></FONT></TD></TR>",
    ]
    for row in rows:
        parts.append(
            "<TR><TD ALIGN=\"LEFT\"><FONT FACE=\"monospace\" POINT-SIZE=\"16\">"
            f"{html_line(row)}</FONT></TD></TR>"
        )
    parts.append("</TABLE>>")
    return "\n".join(parts)


def mapped_disassembly(
    block: Block,
    statement_map: dict[str, list[str]],
    disassembly: dict[str, str],
) -> list[str]:
    lines: list[str] = []
    seen: set[str] = set()
    for stmt in block.statements:
        evm_addrs = statement_map.get(stmt.addr, [])
        if not evm_addrs and stmt.addr in disassembly:
            evm_addrs = [stmt.addr]
        for evm_addr in evm_addrs:
            if evm_addr in seen:
                continue
            seen.add(evm_addr)
            lines.append(disassembly.get(evm_addr, f"{evm_addr}: <missing from disassembly>"))
    return lines


def sanitize_id(prefix: str, index: int) -> str:
    return f"{prefix}_{index}"


def private_call_targets(block: Block) -> list[str]:
    targets: list[str] = []
    seen: set[str] = set()
    for stmt in block.statements:
        match = PRIVATE_CALL_RE.search(stmt.text)
        if not match:
            continue
        target = normalize_tac_id(match.group(1))
        if target in seen:
            continue
        seen.add(target)
        targets.append(target)
    return targets


def emit_dot(
    functions: list[Function],
    statement_map: dict[str, list[str]],
    disassembly: dict[str, str],
    function_filter: str | None,
    max_blocks: int,
    max_lines_per_node: int,
    title: str,
) -> str:
    selected_functions = [
        function for function in functions if function_matches(function.name, function_filter)
    ]
    selected_blocks: list[Block] = []
    for function in selected_functions:
        selected_blocks.extend(function.blocks)
    if max_blocks > 0:
        selected_blocks = selected_blocks[:max_blocks]

    selected_by_function: dict[int, list[Block]] = {}
    for block in selected_blocks:
        selected_by_function.setdefault(block.function_index, []).append(block)

    block_ids: dict[tuple[int, str], str] = {}
    disasm_ids: dict[tuple[int, str], str] = {}
    blocks_by_label: dict[str, list[Block]] = {}
    for index, block in enumerate(selected_blocks):
        key = (block.function_index, block.label)
        block_ids[key] = sanitize_id("tac", index)
        disasm_ids[key] = sanitize_id("dasm", index)
        blocks_by_label.setdefault(block.label, []).append(block)

    lines = [
        "digraph GigahorseTAC {",
        "  graph [",
        "    rankdir=LR,",
        "    compound=true,",
        "    bgcolor=\"#ffffff\",",
        "    pad=0.05,",
        "    nodesep=0.15,",
        "    ranksep=0.08,",
        f"    label=\"{html.escape(title)}\",",
        "    labelloc=t,",
        "    fontsize=20,",
        "    fontname=\"Helvetica\"",
        "  ];",
        "  node [shape=plain, fontname=\"Helvetica\"];",
        "  edge [fontname=\"Helvetica\", fontsize=10, color=\"#56616f\", arrowsize=0.7];",
    ]

    for function in selected_functions:
        blocks = selected_by_function.get(function.index, [])
        if not blocks:
            continue
        cluster_id = f"cluster_function_{function.index}"
        lines.extend(
            [
                f"  subgraph {cluster_id} {{",
                f"    label=\"{html.escape(function.name)}\";",
                "    color=\"#c7d2fe\";",
                "    fontsize=50;",
                "    fontname=\"Helvetica-Bold\";",
                "    penwidth=1.4;",
                "    style=\"rounded\";",
            ]
        )
        for block in blocks:
            key = (block.function_index, block.label)
            tac_rows = truncate_lines(
                [statement.text for statement in block.statements], max_lines_per_node
            )
            dasm_rows = truncate_lines(
                mapped_disassembly(block, statement_map, disassembly), max_lines_per_node
            )
            if not dasm_rows:
                dasm_rows = ["(no original bytecode mapping)"]

            tac_title = f"TAC block {block.label}"
            dasm_title = f"Original bytecode for {block.label}"
            lines.append(
                f"    {block_ids[key]} [label={html_table(tac_title, tac_rows, '#eef6ff', '#7aa2c7')}];"
            )
            lines.append(
                f"    {disasm_ids[key]} [label={html_table(dasm_title, dasm_rows, '#fff8df', '#d3a631')}];"
            )
        lines.append("  }")

    for block in selected_blocks:
        source_key = (block.function_index, block.label)
        source_id = block_ids[source_key]
        dasm_id = disasm_ids[source_key]
        lines.append(
            f"  {source_id} -> {dasm_id} [style=dashed, color=\"#2f80c0\", "
            "arrowhead=vee];"
        )
        for succ in block.succ:
            target_id = block_ids.get((block.function_index, succ))
            if target_id is None:
                continue
            lines.append(f"  {source_id} -> {target_id};")
        for target_label in private_call_targets(block):
            for target_block in blocks_by_label.get(target_label, []):
                target_key = (target_block.function_index, target_block.label)
                if target_key == source_key:
                    continue
                target_id = block_ids[target_key]
                lines.append(
                    f"  {source_id} -> {target_id} [style=bold, color=\"#8a4baf\", "
                    "fontcolor=\"#8a4baf\"];"
                )

    omitted = sum(len(function.blocks) for function in selected_functions) - len(selected_blocks)
    if omitted > 0:
        lines.append(
            f"  omitted [shape=note, label=\"{omitted} blocks omitted by --max-blocks\", "
            "color=\"#9ca3af\", fontcolor=\"#4b5563\"];"
        )

    lines.append("}")
    lines.append("")
    return "\n".join(lines)


def write_outputs(dot: str, output: Path, dot_output: Path, image_format: str) -> None:
    dot_output.write_text(dot, encoding="utf-8")
    if image_format == "dot":
        return

    dot_bin = shutil.which("dot")
    if dot_bin is None:
        raise RuntimeError(
            f"Graphviz 'dot' was not found; wrote DOT to {dot_output}, "
            "but could not render the image"
        )

    subprocess.run(
        [dot_bin, f"-T{image_format}", "-o", str(output), str(dot_output)],
        check=True,
    )


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Create a Graphviz image for a Gigahorse TAC CFG, with each TAC block "
            "linked to the original bytecode disassembly instructions."
        )
    )
    parser.add_argument(
        "input",
        type=Path,
        help=(
            "Path to a Gigahorse bytecode folder, its out folder, or "
            "out/contract.tac"
        ),
    )
    parser.add_argument(
        "-d",
        "--dasm",
        type=Path,
        help="Path to contract.dasm; inferred from the input path by default",
    )
    parser.add_argument(
        "-m",
        "--statement-map",
        type=Path,
        help=(
            "Path to TAC_Statement_OriginalStatement.csv; inferred from the TAC "
            "path by default"
        ),
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        help="Rendered output image path; defaults to contract.tac.svg",
    )
    parser.add_argument(
        "--dot-output",
        type=Path,
        help="DOT output path; defaults to the rendered output path with .dot suffix",
    )
    parser.add_argument(
        "-T",
        "--format",
        choices=["svg", "png", "pdf", "dot"],
        help="Graphviz output format; inferred from --output suffix or defaults to svg",
    )
    parser.add_argument(
        "--function",
        help=(
            "Only include functions whose name matches this regex. If the value is "
            "not a valid regex, it is used as a substring."
        ),
    )
    parser.add_argument(
        "--max-blocks",
        type=int,
        default=0,
        help="Limit the number of rendered TAC blocks after filtering; 0 means no limit",
    )
    parser.add_argument(
        "--max-lines-per-node",
        type=int,
        default=0,
        help=(
            "Limit TAC/disassembly lines shown in each node; 0 means no limit "
            "(the default)"
        ),
    )
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    paths = resolve_input_paths(args.input, args.dasm, args.statement_map)
    tac_path = paths.tac
    dasm_path = paths.dasm
    statement_map_path = paths.statement_map

    if not tac_path.exists():
        print(f"error: TAC file does not exist: {tac_path}", file=sys.stderr)
        return 2
    if not dasm_path.exists():
        print(f"error: disassembly file does not exist: {dasm_path}", file=sys.stderr)
        return 2

    output = args.output
    image_format = args.format
    if output is None:
        image_format = image_format or "svg"
        output = Path(f"{tac_path}.{image_format}")
    elif image_format is None:
        suffix = output.suffix.lstrip(".").lower()
        image_format = suffix if suffix in {"svg", "png", "pdf", "dot"} else "svg"
    dot_output = args.dot_output or output.with_suffix(".dot")

    functions = parse_tac(tac_path)
    disassembly = parse_dasm(dasm_path)
    statement_map = parse_statement_map(statement_map_path)
    dot = emit_dot(
        functions=functions,
        statement_map=statement_map,
        disassembly=disassembly,
        function_filter=args.function,
        max_blocks=args.max_blocks,
        max_lines_per_node=args.max_lines_per_node,
        title=f"{tac_path.name} linked to {dasm_path.name}",
    )

    try:
        write_outputs(dot, output, dot_output, image_format)
    except (OSError, RuntimeError, subprocess.CalledProcessError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    if image_format == "dot":
        print(f"wrote DOT: {dot_output}")
    else:
        print(f"wrote DOT: {dot_output}")
        print(f"wrote image: {output}")
    if not statement_map_path.exists():
        print(
            f"warning: statement map not found at {statement_map_path}; "
            "used address equality fallback",
            file=sys.stderr,
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
