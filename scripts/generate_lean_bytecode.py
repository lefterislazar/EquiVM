#!/usr/bin/env python3
"""Generate a chunked Lean ByteArray definition from EVM bytecode."""

from __future__ import annotations

import argparse
import re
from pathlib import Path

from bytecode_io import parse_bytecode_text, read_bytecode


def checked_ident(value: str) -> str:
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", value):
        raise ValueError("--name must be a Lean identifier")
    return value


def array_literal(code: bytes) -> str:
    rows = [
        "    " + ", ".join(f"0x{byte:02x}" for byte in code[start:start + 12])
        for start in range(0, len(code), 12)
    ]
    body = ",\n".join(rows)
    return f"⟨#[\n{body}\n  ]⟩"


def render(code: bytes, name: str, namespace: str | None, chunk_size: int) -> str:
    name = checked_ident(name)
    chunks = [code[start:start + chunk_size] for start in range(0, len(code), chunk_size)]
    if not chunks:
        chunks = [b""]
    lines = ["import Ethereum.Semantics", ""]
    if namespace:
        lines += [f"namespace {namespace}", ""]
    for index, chunk in enumerate(chunks):
        lines += [f"private def {name}Chunk{index} : ByteArray :=",
                  "  " + array_literal(chunk), ""]
    lines.append(f"def {name} : ByteArray :=")
    for index in range(len(chunks)):
        append = " ++" if index + 1 < len(chunks) else ""
        lines.append(f"  {name}Chunk{index}{append}")
    if namespace:
        lines += ["", f"end {namespace}"]
    lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("bytecode", nargs="?", type=Path,
                        help="raw binary, hex text, or solc JSON; use - for stdin")
    parser.add_argument("--hex", dest="hex_bytecode", help="bytecode as hexadecimal")
    parser.add_argument("--name", required=True, help="public ByteArray definition name")
    parser.add_argument("--namespace", help="optional Lean namespace")
    parser.add_argument("--chunk-size", type=int, default=128,
                        help="bytes per private definition (default: 128)")
    parser.add_argument("--output", "-o", type=Path, required=True)
    args = parser.parse_args(argv)
    if (args.bytecode is None) == (args.hex_bytecode is None):
        parser.error("provide exactly one of BYTECODE or --hex")
    if args.chunk_size <= 0:
        parser.error("--chunk-size must be positive")
    try:
        code = (parse_bytecode_text(args.hex_bytecode) if args.hex_bytecode is not None
                else read_bytecode(args.bytecode))
        result = render(code, args.name, args.namespace, args.chunk_size)
    except (OSError, ValueError) as error:
        parser.error(str(error))
    args.output.write_text(result, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
