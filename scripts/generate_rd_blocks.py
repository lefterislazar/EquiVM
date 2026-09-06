#!/usr/bin/env python3
"""Generate elaborating Lean RD summaries for EVM basic blocks.

Each output is ordinary Lean source: every summary starts from an ``RD`` cursor
and stacks the framework's opcode lemmas.  ``--shard-size`` spreads summaries
across independently importable files. Deterministic blocks expose exact final
step/gas counters; blocks containing warm/cold operations existentially package
the counters and keep stepping through the remainder of the block.  Semantic side
conditions required by an opcode are lifted to hypotheses of the whole block
summary, so they do not interrupt symbolic execution.  Unsupported instructions
become explicit boundaries, with independently quantified summaries generated for
every maximal supported segment on either side.

Example:
  scripts/generate_rd_blocks.py contract.hex --name runtime \
    --code-term My.bytecode --bytecode-import My.Bytecode --output RuntimeBlocks.lean
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Iterable

from bytecode_io import parse_bytecode_text, read_bytecode


TERMINATORS = {0x00, 0x56, 0x57, 0xF3, 0xFD, 0xFE, 0xFF}
MAX_SUMMARY_INSTRUCTIONS = 64


@dataclass(frozen=True)
class Instruction:
    pc: int
    opcode: int
    name: str
    width: int = 0
    argument: int | None = None
    complete: bool = True

    @property
    def size(self) -> int:
        return self.width + 1


class SequenceEffect(Enum):
    REVERT = "revert"
    SELECTOR_MODERN = "selector_modern"
    SELECTOR_LEGACY = "selector_legacy"
    FREE_MEMORY_POINTER = "free_memory_pointer"
    ADDRESS_MASK = "address_mask"
    FREE_MEMORY_POINTER_LOAD = "free_memory_pointer_load"
    ERROR_SELECTOR_STORE = "error_selector_store"


@dataclass(frozen=True)
class SequencePattern:
    """An exact, within-basic-block opcode sequence with a summary theorem."""

    name: str
    instructions: tuple[tuple[int, int | None], ...]
    theorem: str
    effect: SequenceEffect
    peak_growth: int
    gas_cost: int

    @property
    def terminal(self) -> bool:
        return self.effect is SequenceEffect.REVERT


# Keep this explicitly longest-first.  That makes the copy-and-revert idioms win
# over their revert suffixes and gives additions to the registry a visible order.
SEQUENCE_PATTERNS = (
    SequencePattern(
        "error_revert_finalizer",
        ((0x60, 68), (0x82, None), (0x01, None), (0x52, None),
         (0x90, None), (0x51, None), (0x90, None), (0x81, None),
         (0x90, None), (0x03, None), (0x60, 100), (0x01, None),
         (0x90, None), (0xFD, None)),
        "RD.solcSummaryErrorRevertFinalizer", SequenceEffect.REVERT, 2, 0,
    ),
    SequencePattern(
        "return_data_copy_revert",
        ((0x3D, None), (0x5F, None), (0x5F, None), (0x3E, None),
         (0x3D, None), (0x5F, None), (0xFD, None)),
        "RD.solcSummaryReturnDataCopyRevert", SequenceEffect.REVERT, 3, 0,
    ),
    SequencePattern(
        "legacy_return_data_copy_revert",
        ((0x3D, None), (0x60, 0), (0x80, None), (0x3E, None),
         (0x3D, None), (0x60, 0), (0xFD, None)),
        "RD.solcSummaryLegacyReturnDataCopyRevert", SequenceEffect.REVERT, 3, 0,
    ),
    SequencePattern(
        "address_mask",
        ((0x60, 1), (0x60, 1), (0x60, 160), (0x1B, None), (0x03, None)),
        "RD.solcSummaryAddressMask", SequenceEffect.ADDRESS_MASK, 3, 15,
    ),
    SequencePattern(
        "error_selector_store",
        ((0x62, 4594637), (0x60, 229), (0x1B, None), (0x81, None), (0x52, None)),
        "RD.solcSummaryErrorSelectorStore", SequenceEffect.ERROR_SELECTOR_STORE, 2, 15,
    ),
    SequencePattern(
        "selector_load",
        ((0x5F, None), (0x35, None), (0x60, 224), (0x1C, None)),
        "RD.solcSummarySelectorLoad", SequenceEffect.SELECTOR_MODERN, 2, 11,
    ),
    SequencePattern(
        "legacy_selector_load",
        ((0x60, 0), (0x35, None), (0x60, 224), (0x1C, None)),
        "RD.solcSummaryLegacySelectorLoad", SequenceEffect.SELECTOR_LEGACY, 2, 12,
    ),
    SequencePattern(
        "revert0",
        ((0x5F, None), (0x5F, None), (0xFD, None)),
        "RD.solcSummaryRevert0", SequenceEffect.REVERT, 2, 0,
    ),
    SequencePattern(
        "legacy_revert0",
        ((0x60, 0), (0x80, None), (0xFD, None)),
        "RD.solcSummaryLegacyRevert0", SequenceEffect.REVERT, 2, 0,
    ),
    SequencePattern(
        "free_memory_pointer",
        ((0x60, 128), (0x60, 64), (0x52, None)),
        "RD.solcSummaryFreeMemoryPointer", SequenceEffect.FREE_MEMORY_POINTER, 2, 9,
    ),
    SequencePattern(
        "free_memory_pointer_load",
        ((0x60, 64), (0x80, None), (0x51, None)),
        "RD.solcSummaryFreeMemoryPointerLoad", SequenceEffect.FREE_MEMORY_POINTER_LOAD, 2, 9,
    ),
)

ADDRESS_MASK_INSTRUCTIONS = ((0x60, 1), (0x60, 1), (0x60, 160),
                             (0x1B, None), (0x03, None))
ERROR_SELECTOR_BUILD_INSTRUCTIONS = ((0x62, 4594637), (0x60, 229), (0x1B, None))


def matches_instructions(run: list[Instruction], start: int,
                         expected: tuple[tuple[int, int | None], ...]) -> bool:
    end = start + len(expected)
    return end <= len(run) and all(
        ins.opcode == opcode and (argument is None or ins.argument == argument)
        for ins, (opcode, argument) in zip(run[start:end], expected)
    )


def match_sequence(run: list[Instruction], start: int) -> SequencePattern | None:
    """Return the first (therefore longest) exact pattern at ``start``."""
    for pattern in SEQUENCE_PATTERNS:
        if matches_instructions(run, start, pattern.instructions):
            return pattern
    return None


NAMES = {
    0x00: "stop", 0x01: "add", 0x02: "mul", 0x03: "sub", 0x04: "div", 0x06: "mod",
    0x0A: "exp", 0x10: "lt", 0x11: "gt", 0x12: "slt", 0x13: "sgt",
    0x14: "eq", 0x15: "iszero", 0x16: "and", 0x17: "or", 0x18: "xor",
    0x19: "not", 0x1B: "shl", 0x1C: "shr", 0x20: "keccak256",
    0x30: "address", 0x33: "caller", 0x34: "callvalue", 0x35: "calldataload",
    0x36: "calldatasize", 0x37: "calldatacopy", 0x38: "codesize",
    0x39: "codecopy", 0x3B: "extcodesize", 0x3D: "returndatasize",
    0x3E: "returndatacopy", 0x42: "timestamp", 0x46: "chainid", 0x49: "blobhash",
    0x50: "pop", 0x51: "mload", 0x52: "mstore", 0x54: "sload",
    0x55: "sstore", 0x56: "jump", 0x57: "jumpi", 0x5A: "gas",
    0x5B: "jumpdest", 0x5F: "push0", 0xA1: "log1", 0xA2: "log2", 0xA3: "log3",
    0xA4: "log4", 0xF1: "call", 0xF3: "return", 0xFA: "staticcall",
    0xFD: "revert", 0xFE: "invalid", 0xFF: "selfdestruct",
}


def opcode_name(op: int) -> str:
    if 0x60 <= op <= 0x7F:
        return f"push{op - 0x5F}"
    if 0x80 <= op <= 0x8F:
        return f"dup{op - 0x7F}"
    if 0x90 <= op <= 0x9F:
        return f"swap{op - 0x8F}"
    return NAMES.get(op, f"unsupported_{op:02x}")


def disassemble(code: bytes) -> list[Instruction]:
    out: list[Instruction] = []
    pc = 0
    while pc < len(code):
        op = code[pc]
        width = op - 0x5F if 0x60 <= op <= 0x7F else 0
        data = code[pc + 1:pc + 1 + width]
        complete = len(data) == width
        if not complete:
            data = data + bytes(width - len(data))
        out.append(Instruction(pc, op, opcode_name(op), width,
                               int.from_bytes(data, "big") if width else None, complete))
        pc += 1 + width
    return out


def blocks(instructions: list[Instruction]) -> list[list[Instruction]]:
    if not instructions:
        return []
    starts = {instructions[0].pc}
    for i, ins in enumerate(instructions):
        if ins.opcode == 0x5B:
            starts.add(ins.pc)
        if ins.opcode in TERMINATORS and i + 1 < len(instructions):
            starts.add(instructions[i + 1].pc)
    result: list[list[Instruction]] = []
    current: list[Instruction] = []
    for ins in instructions:
        if current and ins.pc in starts:
            result.append(current)
            current = []
        current.append(ins)
        if ins.opcode in TERMINATORS:
            result.append(current)
            current = []
    if current:
        result.append(current)
    return result


def strip_solidity_metadata(code: bytes) -> bytes:
    """Remove a standard length-suffixed solc CBOR metadata map for block discovery.

    The full byte array is still emitted/referenced in theorem statements and decode proofs.
    """
    if len(code) < 3:
        return code
    metadata_length = int.from_bytes(code[-2:], "big")
    start = len(code) - metadata_length - 2
    if start < 0 or start >= len(code) - 2:
        return code
    # CBOR major type 5 (map), including the indefinite-length map marker.
    if code[start] & 0xE0 != 0xA0:
        return code
    return code[:start]


def lean_ident(value: str) -> str:
    ident = re.sub(r"[^A-Za-z0-9_]", "_", value)
    if not ident or ident[0].isdigit():
        ident = "rd_" + ident
    return ident


def u256_nat(value: int) -> str:
    return f"(UInt256.ofNat {value})"


WORD32 = "(⟨32⟩ : UInt256)"
WORD0 = "(⟨0⟩ : UInt256)"


def is_static_word(term: str) -> bool:
    return re.fullmatch(r"\(UInt256\.ofNat [0-9]+\)", term) is not None


def stack_term(values: list[str]) -> str:
    return "R" if not values else "(" + " :: ".join(values + ["R"]) + ")"


# (minimum stack depth before the opcode, pop count, push count)
def stack_shape(ins: Instruction) -> tuple[int, int, int]:
    op = ins.opcode
    if op in {0x00, 0x5B, 0xFE}:
        return (0, 0, 0)
    if op == 0x5F or 0x60 <= op <= 0x7F or op in {
        0x30, 0x33, 0x34, 0x36, 0x38, 0x3D, 0x42, 0x46, 0x5A,
    }:
        return (0, 0, 1)
    if 0x80 <= op <= 0x8F:
        depth = op - 0x7F
        return (depth, 0, 1)
    if 0x90 <= op <= 0x9F:
        depth = op - 0x8F + 1
        return (depth, 0, 0)
    if op in {0x15, 0x19, 0x35, 0x3B, 0x51, 0x54}:
        return (1, 1, 1)
    if op in {0x50, 0x56}:
        return (1, 1, 0)
    if op in {0x01, 0x02, 0x03, 0x04, 0x06, 0x0A, 0x10, 0x11, 0x12, 0x13,
              0x14, 0x16, 0x17, 0x18, 0x1B, 0x1C, 0x20}:
        return (2, 2, 1)
    if op in {0x52, 0x55, 0x57, 0xF3, 0xFD}:
        return (2, 2, 0)
    if op in {0x37, 0x39, 0x3E}:
        return (3, 3, 0)
    if op == 0xA1:
        return (3, 3, 0)
    if op == 0xA2:
        return (4, 4, 0)
    if op == 0xA3:
        return (5, 5, 0)
    if op == 0xA4:
        return (6, 6, 0)
    raise ValueError(f"no RD stepper for opcode 0x{op:02x} ({ins.name}) at pc {ins.pc}")


def required_input_depth(block: list[Instruction]) -> int:
    height = 0
    required = 0
    for ins in block:
        need, pops, pushes = stack_shape(ins)
        required = max(required, need - height)
        height += pushes - pops
    return required


def instruction_is_supported(ins: Instruction) -> bool:
    """Whether ``simulate`` has an RD stepper for this instruction."""
    if not ins.complete:
        return False
    try:
        stack_shape(ins)
        return True
    except ValueError:
        return False


def supported_segments(block: list[Instruction]) -> list[list[Instruction] | Instruction]:
    """Split a basic block into supported runs and unsupported singleton boundaries."""
    result: list[list[Instruction] | Instruction] = []
    current: list[Instruction] = []
    for ins in block:
        if instruction_is_supported(ins):
            current.append(ins)
        else:
            if current:
                result.append(current)
                current = []
            result.append(ins)
    if current:
        result.append(current)
    return result


def bounded_supported_segments(
    block: list[Instruction], max_instructions: int = MAX_SUMMARY_INSTRUCTIONS,
    use_sequence_patterns: bool = True,
) -> list[list[Instruction] | Instruction]:
    """Split supported runs without cutting through a recognized sequence."""
    if max_instructions <= 0:
        raise ValueError("max summary instruction count must be positive")
    result: list[list[Instruction] | Instruction] = []
    for piece in supported_segments(block):
        if isinstance(piece, Instruction):
            result.append(piece)
        else:
            start = 0
            while start < len(piece):
                end = min(start + max_instructions, len(piece))
                if use_sequence_patterns and end < len(piece):
                    crossing = [
                        index for index in range(start, end)
                        if (pattern := match_sequence(piece, index)) is not None
                        and index + len(pattern.instructions) > end
                    ]
                    if crossing:
                        end = crossing[0]
                # A pattern is always shorter than the default bound.  For a
                # deliberately tiny test bound, keep it intact and allow this
                # one segment to exceed the requested instruction count.
                if end == start and use_sequence_patterns:
                    pattern = match_sequence(piece, start)
                    if pattern is not None:
                        end = start + len(pattern.instructions)
                if end == start:
                    end = min(start + max_instructions, len(piece))
                result.append(piece[start:end])
                start = end
    return result


BINOPS = {
    0x01: lambda a, b: f"({a} + {b})",
    0x02: lambda a, b: f"(UInt256.mul {a} {b})",
    0x03: lambda a, b: f"(UInt256.sub {a} {b})",
    0x04: lambda a, b: f"(UInt256.div {a} {b})",
    0x06: lambda a, b: f"(UInt256.mod {a} {b})",
    0x0A: lambda a, b: f"(UInt256.exp {a} {b})",
    0x10: lambda a, b: f"(UInt256.lt {a} {b})",
    0x11: lambda a, b: f"(UInt256.gt {a} {b})",
    0x12: lambda a, b: f"(UInt256.slt {a} {b})",
    0x13: lambda a, b: f"(UInt256.sgt {a} {b})",
    0x14: lambda a, b: f"(UInt256.eq {a} {b})",
    0x16: lambda a, b: f"(UInt256.land {a} {b})",
    0x17: lambda a, b: f"(UInt256.lor {a} {b})",
    0x18: lambda a, b: f"(UInt256.xor {a} {b})",
    0x1B: lambda a, b: f"(UInt256.shiftLeft {b} {a})",
    0x1C: lambda a, b: f"(UInt256.shiftRight {b} {a})",
}


STATIC_COST = {
    0x00: 0, 0x01: 3, 0x02: 5, 0x03: 3, 0x04: 5, 0x06: 5, 0x10: 3, 0x11: 3,
    0x12: 3, 0x13: 3, 0x14: 3, 0x15: 3, 0x16: 3, 0x17: 3, 0x18: 3,
    0x19: 3, 0x1B: 3, 0x1C: 3, 0x30: 2, 0x33: 2, 0x34: 2, 0x35: 3,
    0x36: 2, 0x38: 2, 0x3D: 2, 0x42: 2, 0x46: 2, 0x50: 2,
    0x56: 8, 0x57: 10, 0x5A: 2, 0x5B: 1, 0x5F: 2,
}


def block_cost(costs: Iterable[str | int]) -> str:
    numeric = 0
    symbolic: list[str] = []
    for cost in costs:
        if isinstance(cost, int):
            numeric += cost
        else:
            symbolic.append(cost)
    terms = ([str(numeric)] if numeric else []) + symbolic
    return "0" if not terms else " + ".join(f"({term})" for term in terms)


@dataclass
class Summary:
    stack_in: list[str]
    stack_out: list[str]
    mem: str
    aw: str
    world_map: str
    pc: str
    costs: list[str | int]
    proof: list[str]
    existential_counters: bool
    terminal: str | None
    extra_hypotheses: list[tuple[str, str]]
    branch: str | None
    max_stack_prefix: int
    existential_words: list[str]
    last_cursor: str


def simulate(block: list[Instruction], branch: str | None,
             use_sequence_patterns: bool = True) -> Summary:
    depth = required_input_depth(block)
    initial = [f"x{i}" for i in range(depth)]
    stack = initial.copy()
    mem = "mem"
    aw = "aw"
    world_map = "σ"
    pc = u256_nat(block[0].pc)
    costs: list[str | int] = []
    proof: list[str] = []
    existential = False
    terminal: str | None = None
    extra_hypotheses: list[tuple[str, str]] = []
    rno = 0
    max_stack_prefix = len(stack)
    existential_words: list[str] = []

    def require(name: str, proposition: str) -> str:
        """Add an opcode side condition to the enclosing block theorem.

        A repeated named condition (currently ``hperm``) is shared by every
        instruction that needs it.  Per-instruction conditions use fresh names.
        Returning the name keeps the generated step invocation tied to the
        hypothesis introduced in the theorem statement.
        """
        existing = next((term for hyp, term in extra_hypotheses if hyp == name), None)
        if existing is not None:
            if existing != proposition:
                raise ValueError(f"conflicting block hypothesis {name}")
            return name
        extra_hypotheses.append((name, proposition))
        return name

    def next_r() -> tuple[str, str]:
        nonlocal rno
        before = f"r{rno}"
        rno += 1
        return before, f"r{rno}"

    def ends_with(expected: tuple[tuple[int, int | None], ...], index: int) -> bool:
        start = index - len(expected) + 1
        return start >= 0 and matches_instructions(block, start, expected)

    def apply_pattern_effect(pattern: SequencePattern) -> None:
        nonlocal mem, aw
        effect = pattern.effect
        if effect is SequenceEffect.FREE_MEMORY_POINTER:
            address = u256_nat(64)
            value = u256_nat(128)
            costs.append(f"memExpansionCost {aw} {address} {WORD32}")
            mem = f"({value}.toByteArray.write 0 {mem} {address}.toNat 32)"
            aw = f"(M {aw} {address} {WORD32})"
        elif effect is SequenceEffect.ADDRESS_MASK:
            stack.insert(0, "solcAddrMask")
        elif effect is SequenceEffect.FREE_MEMORY_POINTER_LOAD:
            address = u256_nat(64)
            old_aw = aw
            costs.append(f"memExpansionCost {old_aw} {address} {WORD32}")
            stack.insert(0, address)
            stack.insert(0, f"(memLoad {address} {old_aw} {mem})")
            aw = f"(M {old_aw} {address} {WORD32})"
        elif effect is SequenceEffect.ERROR_SELECTOR_STORE:
            base = stack[0]
            old_aw = aw
            costs.append(f"memExpansionCost {old_aw} {base} {WORD32}")
            mem = f"(solcErrorStringSelector.toByteArray.write 0 {mem} {base}.toNat 32)"
            aw = f"(M {old_aw} {base} {WORD32})"
        elif effect in {SequenceEffect.SELECTOR_MODERN, SequenceEffect.SELECTOR_LEGACY}:
            zero = WORD0 if effect is SequenceEffect.SELECTOR_MODERN else u256_nat(0)
            selector = (
                f"(UInt256.shiftRight (uInt256OfByteArray "
                f"(ee.calldata.readBytes {zero}.toNat 32)) {u256_nat(224)})"
            )
            stack.insert(0, selector)
        else:
            raise AssertionError(f"no nonterminal effect handler for {effect.value}")
        costs.append(pattern.gas_cost)

    index = 0
    while index < len(block):
        ins = block[index]
        pattern = match_sequence(block, index) if use_sequence_patterns else None
        if pattern is not None:
            stack_before = len(stack)
            before, after = next_r()
            count = len(pattern.instructions)
            witnesses = ", ".join(
                [before] + ["by native_decide"] * count + ["by evm_ov"]
            )
            if pattern.terminal:
                proof.append(f"  exact {pattern.theorem} (by exact ⟨{witnesses}⟩)")
                terminal = "RDrev __CODE__ g s0"
                max_stack_prefix = max(max_stack_prefix, stack_before + pattern.peak_growth)
                break

            apply_pattern_effect(pattern)
            proof.append(f"  have {after} := {pattern.theorem} (by exact ⟨{witnesses}⟩)")
            max_stack_prefix = max(max_stack_prefix, stack_before + pattern.peak_growth)
            last = block[index + count - 1]
            pc = u256_nat(last.pc + last.size)
            index += count
            continue

        op = ins.opcode
        before, after = next_r()
        decode = "(by native_decide)"
        ov = "(by evm_ov)"
        step_pc = ins.size

        if op == 0x5F:
            stack.insert(0, WORD0)
            proof.append(f"  have {after} := {before}.push0 {decode} {ov}")
        elif 0x60 <= op <= 0x7F:
            assert ins.argument is not None
            value = u256_nat(ins.argument)
            stack.insert(0, value)
            if ins.width in {1, 2, 4, 20}:
                proof.append(f"  have {after} := {before}.push{ins.width} {value} {decode} {ov}")
            else:
                proof.append(
                    f"  have {after} := {before}.pushConst {value} "
                    f"(width := {ins.width}) (op := .PUSH{ins.width}) (by decide) {decode} {ov}"
                )
        elif 0x80 <= op <= 0x8F:
            n = op - 0x7F
            stack.insert(0, stack[n - 1])
            call = f"RD.dup{n} {before}" if n in {12, 16} else f"{before}.dup{n}"
            proof.append(f"  have {after} := {call} {decode} {ov}")
        elif 0x90 <= op <= 0x9F:
            n = op - 0x8F
            stack[0], stack[n] = stack[n], stack[0]
            call = (
                f"RD.swap{n} {before}" if n in {9, 12, 13, 14, 15, 16}
                else f"{before}.swap{n}"
            )
            proof.append(f"  have {after} := {call} {decode} {ov}")
        elif op in BINOPS:
            a, b = stack.pop(0), stack.pop(0)
            stack.insert(0, BINOPS[op](a, b))
            normalization: str | None = None
            if op == 0x03 and ends_with(ADDRESS_MASK_INSTRUCTIONS, index):
                stack[0] = "solcAddrMask"
                normalization = "solcAddrMask"
            elif op == 0x1B and ends_with(ERROR_SELECTOR_BUILD_INSTRUCTIONS, index):
                stack[0] = "solcErrorStringSelector"
                normalization = "solcErrorStringSelector"
            if normalization is None:
                proof.append(f"  have {after} := {before}.{ins.name} {decode} {ov}")
            else:
                raw_after = f"{after}Raw"
                proof.append(f"  have {raw_after} := {before}.{ins.name} {decode} {ov}")
                proof.append(
                    f"  have {after} := by simpa [{normalization}] using {raw_after}"
                )
        elif op == 0x15:
            a = stack.pop(0)
            stack.insert(0, f"(UInt256.isZero {a})")
            proof.append(f"  have {after} := {before}.iszero {decode} {ov}")
        elif op == 0x19:
            a = stack.pop(0)
            stack.insert(0, f"(UInt256.lnot {a})")
            proof.append(f"  have {after} := {before}.not {decode} {ov}")
        elif op == 0x50:
            stack.pop(0)
            proof.append(f"  have {after} := {before}.pop {decode} {ov}")
        elif op in {0x30, 0x33, 0x34, 0x36, 0x38, 0x3D, 0x42, 0x46}:
            pushed = {
                0x30: "(UInt256.ofNat ee.codeOwner.val)",
                0x33: "(UInt256.ofNat ee.source.val)",
                0x34: "ee.weiValue",
                0x36: "(UInt256.ofNat ee.calldata.size)",
                0x38: "(UInt256.ofNat __CODE__.size)",
                0x3D: "(UInt256.ofNat rdata.size)",
                0x42: "(UInt256.ofNat ee.header.timestamp)",
                0x46: "(UInt256.ofNat Ethereum.chainId)",
            }[op]
            stack.insert(0, pushed)
            proof.append(f"  have {after} := {before}.{ins.name} {decode} {ov}")
        elif op == 0x35:
            a = stack.pop(0)
            stack.insert(0, f"(uInt256OfByteArray (ee.calldata.readBytes {a}.toNat 32))")
            proof.append(f"  have {after} := {before}.calldataload {decode} {ov}")
        elif op == 0x51:
            a = stack.pop(0)
            stack.insert(0, f"(memLoad {a} {aw} {mem})")
            costs.append(f"memExpansionCost {aw} {a} {WORD32}")
            aw = f"(M {aw} {a} {WORD32})"
            proof.append(f"  have {after} := RD.mload {before} {decode} {ov}")
        elif op == 0x52:
            a, b = stack.pop(0), stack.pop(0)
            costs.append(f"memExpansionCost {aw} {a} {WORD32}")
            mem = f"({b}.toByteArray.write 0 {mem} {a}.toNat 32)"
            aw = f"(M {aw} {a} {WORD32})"
            proof.append(f"  have {after} := RD.mstore {before} {decode} {ov}")
        elif op == 0x20:
            a, b = stack.pop(0), stack.pop(0)
            stack.insert(0, f"(keccakWord {a} {b} {mem})")
            costs.append(f"memExpansionCost {aw} {a} {b}")
            costs.append(
                f"GasConstants.Gkeccak256 + GasConstants.Gkeccak256word * (({b}.toNat + 31) / 32)"
            )
            aw = f"(M {aw} {a} {b})"
            proof.append(f"  have {after} := RD.keccak256 {before} {decode} {ov}")
        elif op in {0x37, 0x39}:
            a, b, c = stack.pop(0), stack.pop(0), stack.pop(0)
            source = "ee.calldata" if op == 0x37 else "__CODE__"
            mem = f"({source}.write {b}.toNat {mem} {a}.toNat {c}.toNat)"
            costs.append(f"memExpansionCost {aw} {a} {c}")
            costs.append(f"GasConstants.Gverylow + GasConstants.Gcopy * (({c}.toNat + 31) / 32)")
            aw = f"(M {aw} {a} {c})"
            proof.append(f"  have {after} := RD.{ins.name} {before} {decode} {ov}")
        elif op == 0x3E:
            a, b, c = stack.pop(0), stack.pop(0), stack.pop(0)
            mem = f"(rdata.write {b}.toNat {mem} {a}.toNat {c}.toNat)"
            costs.append(f"memExpansionCost {aw} {a} {c}")
            costs.append(f"GasConstants.Gverylow + GasConstants.Gcopy * (({c}.toNat + 31) / 32)")
            aw = f"(M {aw} {a} {c})"
            zero_terms = {WORD0, u256_nat(0)}
            if b in zero_terms and c == "(UInt256.ofNat rdata.size)":
                guard_name = "(solcSummaryReturnDataCopyGuard rdata)"
            else:
                guard_name = require(
                    f"hguard{sum(name.startswith('hguard') for name, _ in extra_hypotheses)}",
                    f"{b}.toNat + {c}.toNat ≤ rdata.size",
                )
            proof.append(
                f"  have {after} := RD.returndatacopy {before} {decode} {guard_name} {ov}"
            )
        elif op == 0x54:
            slot = stack.pop(0)
            stack.insert(0, f"(storageRead ee.codeOwner {world_map} {slot})")
            proof.append(f"  obtain ⟨_, _, {after}⟩ := RD.sload {before} {decode} {ov}")
            existential = True
        elif op == 0x55:
            slot, value = stack.pop(0), stack.pop(0)
            perm = require("hperm", "ee.perm = true")
            proof.append(f"  obtain ⟨_, _, {after}⟩ := RD.sstore {before} {perm} {decode} {ov}")
            world_map = f"(storageWrite ee.codeOwner {world_map} {slot} {value})"
            existential = True
        elif op == 0x3B:
            target = stack.pop(0)
            stack.insert(0, f"(extCodeSizeWord {world_map} {target})")
            proof.append(f"  obtain ⟨_, _, {after}⟩ := {before}.extcodesize {decode} {ov}")
            existential = True
        elif op == 0x5A:
            if existential:
                gas_word = f"gasWord{len(existential_words)}"
                existential_words.append(gas_word)
                stack.insert(0, gas_word)
                # Earlier warm/cold operations hide the current counter values
                # behind existential eliminations.  RD.gas still determines the
                # pushed word from that hidden C; leave the theorem's gas-word
                # witness for Lean to infer from the resulting cursor.
                proof.append(f"  have {after} := RD.gas {before} {decode} {ov}")
            else:
                cumulative = block_cost(costs)
                stack.insert(0, f"((g.subNat (C + ({cumulative}) + 2)).toUInt256)")
                proof.append(
                    f"  have {after} := RD.gas "
                    f"(RD.normalizeCounters (k' := k + {rno - 1}) "
                    f"(C' := C + ({cumulative})) {before} (by omega) (by omega)) "
                    f"{decode} {ov}"
                )
        elif op == 0x5B:
            proof.append(f"  have {after} := {before}.jumpdest {decode} {ov}")
        elif op == 0x56:
            dest = stack.pop(0)
            valid = require("hvalid", f"(D_J __CODE__ 0).contains {dest} = true")
            proof.append(f"  have {after} := {before}.jump {decode} {valid} {ov}")
            pc = dest
        elif op == 0x57:
            dest, cond = stack.pop(0), stack.pop(0)
            if branch == "taken":
                cond_hyp = require("hcond", f"{cond} ≠ {u256_nat(0)}")
                valid = require("hvalid", f"(D_J __CODE__ 0).contains {dest} = true")
                proof.append(
                    f"  have {after} := {before}.jumpiT {decode} {cond_hyp} {valid} {ov}"
                )
                pc = dest
            elif branch == "fallthrough":
                cond_hyp = require("hcond", f"{cond} = {u256_nat(0)}")
                proof.append(f"  have {after} := {before}.jumpiNT {decode} {cond_hyp} {ov}")
            else:
                raise AssertionError("JUMPI requires a branch")
        elif op == 0x00:
            proof.append(f"  exact {before}.stop {decode} {ov}")
            terminal = "RDret __CODE__ g s0 (cA, " + world_map + ") ByteArray.empty"
            break
        elif op == 0xFE:
            proof.append(f"  exact RD.invalid {before} {decode}")
            terminal = "RDinvalid __CODE__ g s0"
            break
        elif op in {0xF3, 0xFD}:
            off, length = stack.pop(0), stack.pop(0)
            if op == 0xF3:
                proof.append(f"  exact RD.ret {before} {decode} {ov}")
                terminal = (
                    f"RDret __CODE__ g s0 (cA, {world_map}) "
                    f"({mem}.readWithPadding {off}.toNat {length}.toNat)"
                )
            else:
                proof.append(f"  exact RD.rev {before} {decode} {ov}")
                terminal = "RDrev __CODE__ g s0"
            break
        elif op in {0xA1, 0xA2, 0xA3, 0xA4}:
            count = {0xA1: 3, 0xA2: 4, 0xA3: 5, 0xA4: 6}[op]
            vals = [stack.pop(0) for _ in range(count)]
            off, length = vals[0], vals[1]
            perm = require("hperm", "ee.perm = true")
            costs.append(f"memExpansionCost {aw} {off} {length}")
            topics = count - 2
            costs.append(
                f"GasConstants.Glog + GasConstants.Glogdata * {length}.toNat + "
                f"{topics} * GasConstants.Glogtopic"
            )
            aw = f"(M {aw} {off} {length})"
            proof.append(f"  have {after} := RD.{ins.name} {before} {decode} {perm} {ov}")
        else:
            raise ValueError(f"no generator rule for {ins.name} at pc {ins.pc}")

        if op not in {0x0A, 0x20, 0x37, 0x39, 0x3B, 0x3E, 0x51, 0x52, 0x54,
                      0x55, 0xA1, 0xA2, 0xA3, 0xA4, 0xF3, 0xFD}:
            costs.append(3 if 0x60 <= op <= 0x9F else STATIC_COST.get(op, 0))
        elif op == 0x0A:
            # The exponent is the second popped operand; the generated RD rule carries this term.
            costs.append("expGasCost " + b)
        elif op in {0x51, 0x52}:
            costs.append(3)

        if op not in {0x56} and not (op == 0x57 and branch == "taken"):
            # Every instruction in a discovered block has a concrete byte offset.  Keep
            # fallthrough cursors canonical instead of accumulating a large UInt256 sum.
            pc = u256_nat(ins.pc + step_pc)

        max_stack_prefix = max(max_stack_prefix, len(stack))
        index += 1

    return Summary(initial, stack, mem, aw, world_map, pc, costs, proof, existential,
                   terminal, extra_hypotheses, branch, max_stack_prefix, existential_words,
                   f"r{rno}")


def render_summary(prefix: str, code_term: str, block: list[Instruction], summary: Summary) -> str:
    suffix = ""
    if summary.branch == "taken":
        suffix = "_taken"
    elif summary.branch == "fallthrough":
        suffix = "_fallthrough"
    name = f"{prefix}_block_{block[0].pc}{suffix}"
    xs = " ".join(summary.stack_in)
    xbinder = f" {{{xs} : UInt256}}" if xs else ""
    params = (
        f"{{ee : ExecutionEnv}} {{g : Sat256}} {{s0 : State}} {{mem : ByteArray}} "
        f"{{aw : UInt256}} {{rdata : ByteArray}} "
        f"{{cA : Batteries.RBSet AccountAddress compare}} {{σ : AccountMap}} "
        f"{{k C : ℕ}}{xbinder} {{R : List UInt256}}"
    )
    assumptions: list[str] = []
    if any(ins.opcode != 0xFE for ins in block):
        assumptions.append(f"(hstack : R.length + {summary.max_stack_prefix} ≤ 1024)")
    assumptions.extend(
        f"({name} : {term.replace('__CODE__', code_term)})"
        for name, term in summary.extra_hypotheses
    )

    input_rd = (
        f"RD {code_term} ee g s0 {u256_nat(block[0].pc)} {stack_term(summary.stack_in)} "
        f"mem aw rdata (cA, σ) k C"
    )
    assumptions.append(f"(h : {input_rd})")

    if summary.terminal:
        result = summary.terminal
    else:
        result_rd = (
            f"RD {code_term} ee g s0 {summary.pc} {stack_term(summary.stack_out)} "
            f"{summary.mem} {summary.aw} rdata (cA, {summary.world_map})"
        )
        if summary.existential_counters:
            word_binders = "" if not summary.existential_words else (
                "(" + " ".join(summary.existential_words) + " : UInt256) "
            )
            result = f"∃ {word_binders}(k' C' : ℕ), {result_rd} k' C'"
        else:
            result = (
                f"{result_rd} (k + {len(block)}) "
                f"(C + ({block_cost(summary.costs)}))"
            )
    result = result.replace("__CODE__", code_term)

    lines = [f"/-- Automatically generated RD summary for bytecode block at pc {block[0].pc}. -/",
             f"theorem {name} {params}"]
    lines.extend(f"    {a}" for a in assumptions)
    lines.append(f"    : {result} := by")
    lines.append("  let r0 := h")
    lines.extend(summary.proof)
    if not summary.terminal:
        last = summary.last_cursor
        if is_static_word(summary.pc):
            lines.append(
                f"  have rFinal := RD.normalizePC (pc' := {summary.pc}) "
                f"{last} (by native_decide)"
            )
            last = "rFinal"
        if summary.existential_counters:
            witnesses = ["_"] * len(summary.existential_words) + ["_", "_", last]
            lines.append(f"  exact ⟨{', '.join(witnesses)}⟩")
        else:
            lines.append(f"  exact RD.normalizeCounters {last} (by omega) (by omega)")
    return "\n".join(lines)


def unsupported_boundary_comment(ins: Instruction, code_size: int) -> str:
    successor = ins.pc + ins.size
    resume = (
        f" Summaries resume at pc {successor} from a fresh symbolic RD state."
        if successor < code_size and ins.opcode not in TERMINATORS else ""
    )
    return (
        f"/- Unsupported instruction boundary at pc {ins.pc}: {ins.name} "
        f"(0x{ins.opcode:02x}). No RD transition is asserted.{resume} -/"
    )


def generate_units(code: bytes, prefix: str, code_term: str,
                   fail_on_unsupported: bool = False, keep_metadata: bool = False,
                   max_summary_instructions: int = MAX_SUMMARY_INSTRUCTIONS,
                   use_sequence_patterns: bool = True) -> list[str]:
    """Generate theorem/comment units without a Lean module wrapper."""
    prefix = lean_ident(prefix)
    analyzed_code = code if keep_metadata else strip_solidity_metadata(code)
    discovered_blocks = blocks(disassemble(analyzed_code))
    unsupported = [
        ins for block in discovered_blocks for ins in block if not instruction_is_supported(ins)
    ]
    if fail_on_unsupported and unsupported:
        listing = ", ".join(
            f"pc {ins.pc}: {ins.name} (0x{ins.opcode:02x})" for ins in unsupported
        )
        raise ValueError(f"unsupported instructions: {listing}")

    units: list[str] = []
    for block in discovered_blocks:
        for piece in bounded_supported_segments(
            block, max_summary_instructions, use_sequence_patterns
        ):
            if isinstance(piece, Instruction):
                units.append(unsupported_boundary_comment(piece, len(analyzed_code)))
                continue
            branches: list[str | None] = (
                ["taken", "fallthrough"] if piece[-1].opcode == 0x57 else [None]
            )
            for branch in branches:
                summary = simulate(piece, branch, use_sequence_patterns)
                units.append(render_summary(prefix, code_term, piece, summary))
    return units


def render_module(prefix: str, imports: list[str], units: list[str]) -> str:
    """Wrap generated units as an independently elaboratable Lean module."""
    prefix = lean_ident(prefix)
    output = ["import Reasoning.SummaryPatterns"]
    output.extend(f"import {module}" for module in imports)
    output += ["", "open Solm ABI Ethereum Ethereum.EVM",
               "open Reasoning.Theory Reasoning.Reach", "",
               f"namespace {prefix}Blocks", ""]
    for unit in units:
        output += [unit, ""]
    output += [f"end {prefix}Blocks", ""]
    return "\n".join(output)


def generate(code: bytes, prefix: str, code_term: str, imports: list[str],
             fail_on_unsupported: bool = False, keep_metadata: bool = False,
             max_summary_instructions: int = MAX_SUMMARY_INSTRUCTIONS,
             use_sequence_patterns: bool = True) -> str:
    """Generate a single Lean module. Use ``write_outputs`` for file sharding."""
    units = generate_units(code, prefix, code_term, fail_on_unsupported, keep_metadata,
                           max_summary_instructions, use_sequence_patterns)
    return render_module(prefix, imports, units)


def shard_units(units: list[str], shard_size: int) -> list[list[str]]:
    """Group units with at most ``shard_size`` summary theorems per group."""
    if shard_size <= 0:
        raise ValueError("shard size must be positive")
    shards: list[list[str]] = []
    current: list[str] = []
    summaries = 0
    for unit in units:
        is_summary = unit.startswith("/-- Automatically generated RD summary")
        if is_summary and summaries == shard_size:
            shards.append(current)
            current = []
            summaries = 0
        current.append(unit)
        summaries += int(is_summary)
    if current or not shards:
        shards.append(current)
    return shards


def write_outputs(output: Path, prefix: str, imports: list[str], units: list[str],
                  shard_size: int | None) -> list[Path]:
    if shard_size is None:
        output.write_text(render_module(prefix, imports, units), encoding="utf-8")
        return [output]

    shards = shard_units(units, shard_size)
    width = max(3, len(str(len(shards))))
    suffix = output.suffix or ".lean"
    paths: list[Path] = []
    for index, shard in enumerate(shards, 1):
        path = output.with_name(f"{output.stem}_{index:0{width}d}{suffix}")
        path.write_text(render_module(prefix, imports, shard), encoding="utf-8")
        paths.append(path)
    return paths


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("bytecode", nargs="?", type=Path,
                        help="raw binary, hex text, or solc JSON; use - for stdin")
    parser.add_argument("--hex", dest="hex_bytecode", help="bytecode as a hexadecimal string")
    parser.add_argument("--name", required=True, help="Lean-safe prefix for generated declarations")
    parser.add_argument("--code-term", required=True,
                        help="ByteArray term provided by the imported bytecode module")
    parser.add_argument("--bytecode-import", required=True,
                        help="Lean module containing --code-term")
    parser.add_argument("--import", dest="imports", action="append", default=[],
                        help="additional Lean module import")
    parser.add_argument("--output", "-o", type=Path, required=True,
                        help="output .lean file; its stem is used for sharded filenames")
    parser.add_argument("--shard-size", type=int,
                        help="maximum summary theorems per output file")
    parser.add_argument("--fail-on-unsupported", action="store_true",
                        help="reject bytecode containing an instruction without a generator rule")
    parser.add_argument("--allow-unsupported", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--keep-metadata", action="store_true",
                        help="treat length-suffixed solc CBOR metadata bytes as executable code")
    parser.add_argument("--max-summary-instructions", type=int,
                        default=MAX_SUMMARY_INSTRUCTIONS,
                        help="split long supported runs after this many instructions (default: 64)")
    parser.add_argument("--no-sequence-patterns", action="store_true",
                        help="emit one primitive RD step per opcode")
    args = parser.parse_args(argv)
    if (args.bytecode is None) == (args.hex_bytecode is None):
        parser.error("provide exactly one of BYTECODE or --hex")
    try:
        code = (parse_bytecode_text(args.hex_bytecode) if args.hex_bytecode is not None
                else read_bytecode(args.bytecode, args.code_term))
        units = generate_units(code, args.name, args.code_term, args.fail_on_unsupported,
                               args.keep_metadata, args.max_summary_instructions,
                               not args.no_sequence_patterns)
        paths = write_outputs(args.output, args.name,
                              [args.bytecode_import, *args.imports], units,
                              args.shard_size)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    if args.shard_size is not None:
        for path in paths:
            print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
