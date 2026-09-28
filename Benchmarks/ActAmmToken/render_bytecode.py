#!/usr/bin/env python3
"""Render Act's exact AMM Token hex artifacts as an EquiVM Lean module."""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


def read_hex(path: Path) -> bytes:
    text = path.read_text().strip()
    if text.startswith("0x"):
        text = text[2:]
    return bytes.fromhex(text)


def jumpdests(code: bytes) -> list[int]:
    result: list[int] = []
    pc = 0
    while pc < len(code):
        op = code[pc]
        if op == 0x5B:
            result.append(pc)
        pc += 2 + op - 0x60 if 0x60 <= op <= 0x7F else 1
    return result


def chunks(name: str, code: bytes, size: int = 128) -> tuple[list[str], str]:
    definitions: list[str] = []
    names: list[str] = []
    for index, start in enumerate(range(0, len(code), size)):
        chunk_name = f"{name}Chunk{index}"
        names.append(chunk_name)
        values = code[start : start + size]
        lines = []
        for offset in range(0, len(values), 24):
            lines.append("    " + ", ".join(str(x) for x in values[offset : offset + 24]))
        definitions.append(
            f"private def {chunk_name} : ByteArray :=\n"
            "  ⟨#[\n" + ",\n".join(lines) + "\n  ]⟩\n"
        )
    return definitions, " ++\n  ".join(names)


def vector(values: list[int]) -> str:
    if not values:
        return "#[]"
    lines = []
    for offset in range(0, len(values), 10):
        lines.append("      " + ", ".join(f"⟨{x}⟩" for x in values[offset : offset + 10]))
    return "#[\n" + ",\n".join(lines) + "\n      ]"


def main() -> None:
    runtime_path, creation_path, output_path = map(Path, sys.argv[1:4])
    runtime = read_hex(runtime_path)
    creation = read_hex(creation_path)
    runtime_defs, runtime_joined = chunks("tokenRuntime", runtime)
    creation_defs, creation_joined = chunks("tokenCreation", creation)

    text = f'''import Benchmarks.ActAmmToken.Spec
import Ethereum.Semantics
import Reasoning.JumpDest

open Solm Ethereum Ethereum.EVM

namespace Benchmarks.ActAmmToken

/-! # Act AMM Token bytecode

These are the exact `Token` bytes selected by Act when invoked with
`tests/hevm/pass/multisource/amm/amm.json`: solc 0.8.28 standard JSON,
source unit `hevm.sol`, optimizer off, and `viaIR = false`.

Runtime: {len(runtime)} bytes, SHA-256 `{hashlib.sha256(runtime).hexdigest()}`.
Creation: {len(creation)} bytes, SHA-256 `{hashlib.sha256(creation).hexdigest()}`.
-/

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

{chr(10).join(runtime_defs)}
/-- Exact deployed runtime bytecode used by Act for its AMM `Token`. -/
def tokenBytecode : ByteArray :=
  {runtime_joined}

@[valid_jumps] theorem validJumps :
    D_J tokenBytecode 0 = {vector(jumpdests(runtime))} := by
  native_decide

{chr(10).join(creation_defs)}
/-- Exact creation bytecode, without appended constructor arguments. -/
def tokenCreationBytecode : ByteArray :=
  {creation_joined}

@[valid_jumps] theorem creationValidJumps :
    D_J tokenCreationBytecode 0 = {vector(jumpdests(creation))} := by
  native_decide

end Benchmarks.ActAmmToken
'''
    output_path.write_text(text)


if __name__ == "__main__":
    main()
