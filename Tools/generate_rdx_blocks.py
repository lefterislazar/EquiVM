#!/usr/bin/env python3
"""Generate Lean RDx block theorems from `symcheck summarize --json`.

The translator is deliberately EquiVM-specific.  SymCheck remains an untrusted,
general summary producer; Lean replays every emitted opcode through checked RDx
steppers and infers the exact post-cursor.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


TERMINATORS = {
    0x00: "STOP",
    0x56: "JUMP",
    0x57: "JUMPI",
    0xF3: "RETURN",
    0xFD: "REVERT",
    0xFE: "INVALID",
    0xFF: "SELFDESTRUCT",
}

TERMINATOR_STACK_INPUTS = {
    "STOP": 0,
    "JUMP": 1,
    "JUMPI": 2,
    "RETURN": 2,
    "REVERT": 2,
    "INVALID": 0,
    "SELFDESTRUCT": 1,
}

SIMPLE_STEPS = {
    "JUMPDEST": "jumpdest",
    "POP": "pop",
    "EQ": "eq",
    "LT": "lt",
    "GT": "gt",
    "SLT": "slt",
    "SGT": "sgt",
    "ADD": "add",
    "SUB": "sub",
    "AND": "and",
    "OR": "or",
    "XOR": "xor",
    "SHL": "shl",
    "SHR": "shr",
    "MUL": "mul",
    "DIV": "div",
    "MOD": "mod",
    "ADDMOD": "addmod",
    "MULMOD": "mulmod",
    "BYTE": "byte",
    "ISZERO": "iszero",
    "NOT": "not",
    "CALLVALUE": "callvalue",
    "CALLDATASIZE": "calldatasize",
    "CALLDATALOAD": "calldataload",
    "MSTORE": "mstoreCanonical",
    "MLOAD": "mloadCanonical",
    "MSTORE8": "mstore8Canonical",
    "CALLDATACOPY": "calldatacopyCanonical",
    "MCOPY": "mcopyCanonical",
}

for _n in list(range(1, 12)) + [13, 14, 15]:
    SIMPLE_STEPS[f"DUP{_n}"] = f"dup{_n}"
for _n in [12, 16]:
    SIMPLE_STEPS[f"DUP{_n}"] = f"dup{_n}Canonical"
for _n in range(1, 12):
    SIMPLE_STEPS[f"SWAP{_n}"] = f"swap{_n}"
for _n in range(12, 17):
    SIMPLE_STEPS[f"SWAP{_n}"] = f"swap{_n}Canonical"


@dataclass(frozen=True)
class Instruction:
    pc: int
    opcode: int
    size: int

    @property
    def next_pc(self) -> int:
        return self.pc + self.size


@dataclass(frozen=True)
class Block:
    start: int
    target: int
    terminator: str | None


def parse_hex(value: str) -> bytes:
    text = value.removeprefix("0x").replace("_", "")
    if len(text) % 2:
        text = "0" + text
    try:
        return bytes.fromhex(text)
    except ValueError as exc:
        raise SystemExit(f"invalid bytecode hex: {exc}") from exc


def disassemble(code: bytes) -> list[Instruction]:
    result: list[Instruction] = []
    pc = 0
    while pc < len(code):
        opcode = code[pc]
        size = 1 + (opcode - 0x5F if 0x60 <= opcode <= 0x7F else 0)
        result.append(Instruction(pc, opcode, size))
        pc += size
    return result


def discover_blocks(code: bytes, extra_entries: list[int]) -> list[Block]:
    instructions = disassemble(code)
    by_pc = {instr.pc: instr for instr in instructions}
    entries = {0} if code else set()
    entries.update(instr.pc for instr in instructions if instr.opcode == 0x5B)
    entries.update(
        instr.next_pc
        for instr in instructions
        if instr.opcode == 0x57 and instr.next_pc in by_pc
    )
    for pc in extra_entries:
        if pc not in by_pc:
            raise SystemExit(f"extra entry PC {pc} is not an instruction boundary")
        entries.add(pc)

    blocks: list[Block] = []
    for start in sorted(entries):
        target = len(code)
        terminator: str | None = None
        for instr in instructions:
            if instr.pc < start:
                continue
            if instr.pc > start and instr.pc in entries:
                target = instr.pc
                break
            if instr.opcode in TERMINATORS:
                target = instr.pc
                terminator = TERMINATORS[instr.opcode]
                break
        blocks.append(Block(start, target, terminator))
    return blocks


def parse_json_output(stdout: str) -> dict[str, Any]:
    for line in reversed(stdout.splitlines()):
        line = line.strip()
        if line.startswith("{"):
            try:
                value = json.loads(line)
            except json.JSONDecodeError:
                continue
            if isinstance(value, dict):
                return value
    raise RuntimeError("SymCheck did not emit a JSON object")


def run_summary(exe: str, code_hex: str, start: int, target: int, fuel: int) -> dict[str, Any]:
    command = [
        exe,
        "summarize",
        "--code", code_hex,
        "--pc", str(start),
        "--target-pc", str(target),
        "--fuel", str(fuel),
        "--memory", "sym:memory",
        "--active-words", "var:active_words",
        "--calldata", "sym:calldata",
        "--returndata", "sym:returndata",
        "--callvalue", "var:callvalue",
        "--block-number", "var:block_number",
        "--timestamp", "var:timestamp",
        "--gas", "var:gas",
        "--json",
        "--trace-opcodes",
    ]
    process = subprocess.run(command, text=True, capture_output=True, check=False)
    if process.returncode != 0:
        raise RuntimeError(
            f"SymCheck failed for block {start}: {process.stderr.strip() or process.stdout.strip()}"
        )
    summary = parse_json_output(process.stdout)
    required = {
        "mode", "solverFree", "steps", "stop", "pc", "pcTrace",
        "pcTraceOpcodes", "stack", "stackTail", "initialStackDepth",
        "memory", "activeWords", "returndata", "gasCost",
    }
    missing = sorted(required.difference(summary))
    if missing:
        raise RuntimeError(f"SymCheck summary is missing fields: {', '.join(missing)}")
    if summary["mode"] != "straight-line" or summary["solverFree"] is not True:
        raise RuntimeError("SymCheck returned a non-straight-line or solver-backed summary")
    return summary


def push_step(code: bytes, pc: int, opcode_name: str) -> str | None:
    if opcode_name == "PUSH0":
        return "push0"
    match = re.fullmatch(r"PUSH(\d+)", opcode_name)
    if not match:
        return None
    width = int(match.group(1))
    if pc + 1 + width > len(code):
        return None
    payload = code[pc + 1 : pc + 1 + width]
    value = int.from_bytes(payload, "big")
    return (
        f"pushCanonical {width} .PUSH{width} ⟨0x{value:x}⟩ (by decide)"
    )


def render_step(code: bytes, entry: dict[str, Any]) -> str | None:
    pc = int(entry["pc"])
    opcode_name = str(entry["opcode"]).upper()
    pushed = push_step(code, pc, opcode_name)
    if pushed is not None:
        return pushed
    return SIMPLE_STEPS.get(opcode_name)


def lean_byte_array(code: bytes) -> str:
    data = ", ".join(f"0x{byte:02x}" for byte in code)
    return f"⟨#[{data}]⟩"


def binder_lines(materialized: int, max_depth: int, code_name: str, start: int) -> list[str]:
    stack_binders = ""
    if materialized:
        names = " ".join(f"stack_{idx}" for idx in range(materialized))
        stack_binders = f"    {{{names} : UInt256}}\n"
    stack = "tail"
    for idx in reversed(range(materialized)):
        stack = f"stack_{idx} :: {stack}"
    return [
        "    {ee : ExecutionEnv} {g : Sat256} {s0 : State}",
        "    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}",
        "    {acc : Batteries.RBSet AccountAddress compare × AccountMap}",
        "    {k C : Nat} {tail : List UInt256}",
        *(stack_binders.rstrip().splitlines() if stack_binders else []),
        f"    (hdepth : tail.length + {materialized} ≤ {max_depth})",
        f"    (h : RDx {code_name} ee g s0 ⟨{start}⟩ ({stack}) mem aw rdata acc k C)",
    ]


def render_theorem(
    name: str,
    code_name: str,
    start: int,
    endpoint: int,
    materialized: int,
    max_depth: int,
    steps: list[str],
) -> str:
    binders = "\n".join(binder_lines(materialized, max_depth, code_name, start))
    step_text = ",\n      ".join(steps)
    if steps:
        proof = f"(evm_run h with [\n      {step_text}\n    ])"
    else:
        proof = "h"
    return (
        f"evm_theorem {name}\n{binders} :=\n"
        f"  ({proof}).withPC (pc' := ⟨{endpoint}⟩) (by native_decide)\n"
    )


def terminal_step(terminator: str | None) -> str | None:
    return {
        "STOP": "stop",
        "RETURN": "retCanonical",
        "REVERT": "revCanonical",
        "INVALID": "raw invalid (by native_decide)",
    }.get(terminator)


def render_terminal_theorem(
    name: str,
    code_name: str,
    start: int,
    materialized: int,
    max_depth: int,
    steps: list[str],
    terminator: str,
) -> str:
    binders = "\n".join(binder_lines(materialized, max_depth, code_name, start))
    all_steps = steps + [terminal_step(terminator)]
    step_text = ",\n      ".join(step for step in all_steps if step is not None)
    return (
        f"evm_theorem {name}\n{binders} :=\n"
        f"  evm_run h with [\n      {step_text}\n    ]\n"
    )


def render_control_edge_theorems(
    body_name: str,
    code_name: str,
    start: int,
    materialized: int,
    max_depth: int,
    terminator: str | None,
    post_stack_words: int,
) -> list[tuple[str, str]]:
    """Close a body theorem over a dynamic branch.

    The body theorem deliberately leaves its post-state type inferred by Lean.  Underscore-typed
    lambda binders let the checked RDx edge theorem infer the precise decode, condition, and
    destination hypotheses from that post-state, without translating SymCheck expressions into
    Lean syntax.
    """
    binders = "\n".join(binder_lines(materialized, max_depth, code_name, start))
    consumed = TERMINATOR_STACK_INPUTS.get(terminator or "", 0)
    if post_stack_words > consumed:
        stack_bound = "by simp only [List.length_cons]; omega"
    else:
        stack_bound = "by omega"
    if terminator == "JUMP":
        name = body_name.removesuffix("_body") + "_jump"
        theorem = (
            f"evm_theorem {name}\n{binders} :=\n"
            "  fun (hdec : _) (hjd : _) =>\n"
            f"    ({body_name} hdepth h).jump hdec hjd ({stack_bound})\n"
        )
        return [(name, theorem)]
    if terminator == "JUMPI":
        base = body_name.removesuffix("_body")
        taken_name = base + "_taken"
        not_taken_name = base + "_notTaken"
        taken = (
            f"evm_theorem {taken_name}\n{binders} :=\n"
            "  fun (hdec : _) (hcondition : _) (hjd : _) =>\n"
            f"    ({body_name} hdepth h).jumpiT hdec hcondition hjd ({stack_bound})\n"
        )
        not_taken = (
            f"evm_theorem {not_taken_name}\n{binders} :=\n"
            "  fun (hdec : _) (hcondition : _) =>\n"
            f"    ({body_name} hdepth h).jumpiNT hdec hcondition ({stack_bound})\n"
        )
        return [(taken_name, taken), (not_taken_name, not_taken)]
    return []


def materialized_for_edge(summary: dict[str, Any], terminator: str | None) -> int:
    """Include tail words consumed by a terminator that the boundary summary does not execute."""
    materialized = int(summary["stackTail"]["materialized"])
    required = TERMINATOR_STACK_INPUTS.get(terminator or "", 0)
    visible = len(summary.get("stack", []))
    return materialized + max(0, required - visible)


def markdown_section(record: dict[str, Any]) -> str:
    summary = record["summary"]
    trace = ", ".join(
        f"{entry['pc']}:{entry['opcode']}" for entry in summary.get("pcTraceOpcodes", [])
    )
    fields = [
        f"## Block {record['start']} → {record['endpoint']}",
        "",
        f"- Status: `{record['status']}`",
        f"- Requested boundary: `{record['target']}`",
        f"- Stop: `{summary.get('stop')}`",
        f"- Steps: `{summary.get('steps')}`",
        f"- Gas cost: `{summary.get('gasCost')}`",
        f"- Trace: `{trace}`",
        f"- Stack: `{summary.get('stack')}`",
        f"- Memory: `{summary.get('memory')}`",
        f"- Active words: `{summary.get('activeWords')}`",
        f"- Returndata: `{summary.get('returndata')}`",
    ]
    if record.get("reason"):
        fields.append(f"- Incomplete reason: `{record['reason']}`")
    fields.extend(["", "<details><summary>Raw SymCheck JSON</summary>", "", "```json",
                   json.dumps(summary, indent=2, sort_keys=True), "```", "", "</details>", ""])
    return "\n".join(fields)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--symcheck", required=True, help="path to the built symcheck executable")
    parser.add_argument("--code", required=True, help="legacy EVM bytecode as hex")
    parser.add_argument("--lean-code", required=True, help="qualified Lean ByteArray declaration")
    parser.add_argument("--lean-import", action="append", default=[], help="additional Lean import")
    parser.add_argument("--namespace", required=True, help="namespace for generated declarations")
    parser.add_argument("--output", type=Path, required=True, help="generated Lean file")
    parser.add_argument("--manifest", type=Path, required=True, help="machine-readable coverage JSON")
    parser.add_argument("--summaries", type=Path, required=True, help="human-readable summary Markdown")
    parser.add_argument("--extra-entry-pc", type=int, action="append", default=[])
    args = parser.parse_args()

    code = parse_hex(args.code)
    code_hex = code.hex()
    blocks = discover_blocks(code, args.extra_entry_pc)
    fuel = max(2, len(disassemble(code)) + 2)
    records: list[dict[str, Any]] = []
    declarations: list[str] = []
    incomplete = False

    for block in blocks:
        summary = run_summary(args.symcheck, code_hex, block.start, block.target, fuel)
        executed = list(summary["pcTraceOpcodes"][: int(summary["steps"])])
        rendered: list[str] = []
        unsupported: dict[str, Any] | None = None
        for entry in executed:
            step = render_step(code, entry)
            if step is None:
                unsupported = entry
                break
            rendered.append(step)

        if unsupported is not None:
            endpoint = int(unsupported["pc"])
            summary = run_summary(args.symcheck, code_hex, block.start, endpoint, fuel)
            executed = list(summary["pcTraceOpcodes"][: int(summary["steps"])])
            rendered = [render_step(code, entry) for entry in executed]
            if any(step is None for step in rendered):
                raise RuntimeError("prefix summary still contains an unsupported opcode")
            rendered = [step for step in rendered if step is not None]
            status = "incomplete"
            reason = f"unsupported RDx step at PC {endpoint}: {unsupported['opcode']}"
            theorem_name = f"block_{block.start}_prefix_{endpoint}"
            incomplete = True
        elif int(summary["pc"]) != block.target or summary["stop"] != f"target-pc {block.target}":
            endpoint = int(summary["pc"])
            status = "incomplete"
            reason = str(summary["stop"])
            theorem_name = f"block_{block.start}_prefix_{endpoint}"
            incomplete = True
        else:
            endpoint = block.target
            status = "complete"
            reason = None
            theorem_name = f"block_{block.start}_body"

        depths = summary["initialStackDepth"]
        edge_terminator = block.terminator if status == "complete" else None
        materialized = materialized_for_edge(summary, edge_terminator)
        max_depth = int(depths["maximum"])
        declarations.append(
            render_theorem(
                theorem_name, args.lean_code, block.start, endpoint,
                materialized, max_depth, rendered,
            )
        )

        edge_names: list[str] = []
        edge_step = terminal_step(block.terminator)
        if status == "complete" and edge_step is not None:
            edge_name = f"block_{block.start}_halt"
            edge_names.append(edge_name)
            declarations.append(
                render_terminal_theorem(
                    edge_name, args.lean_code, block.start,
                    materialized, max_depth, rendered, block.terminator or "",
                )
            )
        elif status == "complete":
            branch_edges = render_control_edge_theorems(
                theorem_name, args.lean_code, block.start,
                materialized, max_depth, block.terminator,
                len(summary.get("stack", [])),
            )
            edge_names.extend(name for name, _ in branch_edges)
            declarations.extend(theorem for _, theorem in branch_edges)

        if status == "complete" and block.terminator is not None and not edge_names:
            status = "incomplete"
            reason = f"unsupported RDx terminal edge: {block.terminator}"
            incomplete = True

        records.append({
            "start": block.start,
            "target": block.target,
            "endpoint": endpoint,
            "terminator": block.terminator,
            "status": status,
            "reason": reason,
            "bodyTheorem": theorem_name,
            "edgeTheorems": edge_names,
            "theoremInitialStackMaterialized": materialized,
            "theoremInitialStackMaximum": max_depth,
            "summary": summary,
        })

    imports = ["Reasoning.SymCheck", *args.lean_import]
    lean_text = "-- Generated by Tools/generate_rdx_blocks.py; do not edit manually.\n"
    lean_text += "\n".join(f"import {module}" for module in dict.fromkeys(imports))
    lean_text += (
        "\n\nopen Solm ABI Ethereum Ethereum.EVM\n"
        "open Reasoning.Reach\n\n"
        "set_option maxRecDepth 100000\n"
        "set_option linter.unusedVariables false\n\n"
        f"namespace {args.namespace}\n\n"
        f"private theorem symcheckCodeMatches :\n"
        f"    {args.lean_code} = {lean_byte_array(code)} := by native_decide\n\n"
        + "\n".join(declarations)
        + f"\nend {args.namespace}\n"
    )
    manifest = {
        "formatVersion": 1,
        "generator": "Tools/generate_rdx_blocks.py",
        "code": code_hex,
        "leanCode": args.lean_code,
        "namespace": args.namespace,
        "complete": not incomplete,
        "blocks": records,
    }
    markdown = (
        "<!-- Generated by Tools/generate_rdx_blocks.py; do not edit manually. -->\n\n"
        f"# SymCheck summaries for `{args.lean_code}`\n\n"
        "This file preserves the human-readable and raw SymCheck view used to generate the "
        "adjacent Lean block catalog. Lean replay is authoritative for theorem conclusions.\n\n"
        + "\n".join(markdown_section(record) for record in records)
    )

    for path in (args.output, args.manifest, args.summaries):
        path.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(lean_text, encoding="utf-8")
    args.manifest.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    args.summaries.write_text(markdown, encoding="utf-8")

    if incomplete:
        print("generated catalog with incomplete block coverage", file=sys.stderr)
        return 2
    print(f"generated {len(records)} block theorem catalog entries")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except RuntimeError as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc
