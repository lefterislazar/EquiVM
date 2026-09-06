#!/usr/bin/env python3
"""Generate and elaborate RD summaries for repository bytecode definitions."""

from __future__ import annotations

import argparse
import concurrent.futures
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

import generate_rd_blocks as rd


ROOT = Path(__file__).resolve().parent.parent
DECLARATION = re.compile(
    r"^(private\s+)?def\s+([A-Za-z_][A-Za-z0-9_]*)\s*:\s*ByteArray\s*:=",
    re.MULTILINE,
)


@dataclass(frozen=True)
class Case:
    source: Path
    module: str
    term: str
    code: bytes

    @property
    def label(self) -> str:
        return f"{self.module}.{self.term}"


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def discover(roots: list[Path]) -> list[Case]:
    cases: list[Case] = []
    for root in roots:
        for source in sorted(root.rglob("Bytecode.lean")):
            text = source.read_text(encoding="utf-8")
            declarations = list(DECLARATION.finditer(text))
            namespace_match = re.search(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.]*)", text,
                                        re.MULTILINE)
            namespace = namespace_match.group(1) if namespace_match else ""
            values: dict[str, bytes] = {}
            public: list[str] = []
            pending: list[tuple[str, str]] = []
            for index, match in enumerate(declarations):
                body_end = declarations[index + 1].start() if index + 1 < len(declarations) else len(text)
                name = match.group(2)
                body = text[match.end():body_end]
                literal = re.match(r"\s*(⟨#\[.*?\]\s*⟩)", body, re.DOTALL)
                if literal:
                    values[name] = rd.parse_bytecode_text(literal.group(1))
                else:
                    pending.append((name, body))
                if match.group(1) is None and re.search(r"(?:bytecode|initcode)", name, re.I):
                    public.append(name)

            # Benchmark bytecode is split into private chunks and reassembled
            # with ``++``.  Resolve those simple named concatenations locally.
            while pending:
                deferred: list[tuple[str, str]] = []
                made_progress = False
                for name, body in pending:
                    expression = body.split("\n\n", 1)[0]
                    expression = re.sub(r"--[^\n]*", "", expression)
                    expression = re.sub(r"/-(?:.|\n)*?-\/", "", expression)
                    identifiers = re.findall(r"[A-Za-z_][A-Za-z0-9_]*", expression)
                    refs = identifiers
                    refs = [ref for ref in refs if ref in values]
                    unknown = [
                        ref for ref in identifiers
                        if ("Chunk" in ref or re.search(r"(?:bytecode|initcode)", ref, re.I))
                        and ref not in values
                    ]
                    if refs and not unknown:
                        values[name] = b"".join(values[ref] for ref in refs)
                        made_progress = True
                    else:
                        deferred.append((name, body))
                if not made_progress:
                    break
                pending = deferred

            for term in public:
                if term in values:
                    qualified = f"{namespace}.{term}" if namespace else term
                    cases.append(Case(source, module_name(source), qualified, values[term]))
    return cases


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("roots", nargs="*", default=["Examples", "Benchmarks"],
                        help="repository subtrees to scan (default: Examples Benchmarks)")
    parser.add_argument("--match", help="only run cases whose qualified name matches this regex")
    parser.add_argument("--limit", type=int, help="run at most this many cases")
    parser.add_argument("--timeout", type=int, default=300,
                        help="Lean timeout per generated file in seconds (default: 300)")
    parser.add_argument("--jobs", type=int, default=4,
                        help="number of generated files to elaborate concurrently (default: 4)")
    parser.add_argument("--shard-size", type=int, default=100,
                        help="maximum generated summaries per Lean file (default: 100)")
    parser.add_argument("--skip-build-imports", action="store_true",
                        help="do not first build the Bytecode modules imported by generated files")
    args = parser.parse_args(argv)

    roots = [(ROOT / root).resolve() for root in args.roots]
    cases = discover(roots)
    if args.match:
        wanted = re.compile(args.match)
        cases = [case for case in cases if wanted.search(case.label)]
    if args.limit is not None:
        cases = cases[:args.limit]
    if not cases:
        parser.error("no direct ByteArray definitions found")

    if not args.skip_build_imports:
        modules = sorted({case.module for case in cases})
        print(f"building {len(modules)} imported Bytecode modules", flush=True)
        built = subprocess.run(["lake", "build", *modules], cwd=ROOT, check=False)
        if built.returncode != 0:
            print("failed to build one or more imported Bytecode modules", file=sys.stderr)
            return built.returncode

    failures: list[tuple[Case, str]] = []
    theorem_count = 0
    with tempfile.TemporaryDirectory(prefix="rd-block-corpus-") as temp:
        temp_dir = Path(temp)

        def check(index: int, case: Case) -> tuple[Case, int, str | None]:
            prefix = rd.lean_ident(f"corpus_{case.module}_{case.term}")
            header = (
                "import Reasoning.SummaryPatterns\n"
                f"import {case.module}\n\n"
                "open Solm ABI Ethereum Ethereum.EVM\n"
                "open Reasoning.Theory Reasoning.Reach\n\n"
                f"namespace {prefix}Blocks\n\n"
            )
            footer = f"\nend {prefix}Blocks\n"
            analyzed = rd.strip_solidity_metadata(case.code)
            discovered = rd.blocks(rd.disassemble(analyzed))
            summaries = 0
            shard_index = 0
            units: list[str] = []

            def elaborate_shard(parts: list[str]) -> str | None:
                nonlocal shard_index
                shard_index += 1
                shard = header + "\n\n".join(parts) + footer
                output = temp_dir / f"{index:03}_{prefix}_{shard_index:03}.lean"
                output.write_text(shard, encoding="utf-8")
                try:
                    result = subprocess.run(
                        ["lake", "env", "lean", str(output)], cwd=ROOT,
                        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                        timeout=args.timeout, check=False,
                    )
                except subprocess.TimeoutExpired:
                    return f"shard {shard_index} timed out after {args.timeout}s"
                if result.returncode != 0:
                    detail = result.stdout[-12000:] or f"Lean exited with {result.returncode}"
                    return f"shard {shard_index}:\n{detail}"
                print(f"  shard {shard_index} ok: {case.label} ({len(parts)} summaries)",
                      flush=True)
                return None

            for block in discovered:
                for piece in rd.bounded_supported_segments(block):
                    if isinstance(piece, rd.Instruction):
                        continue
                    branches: list[str | None] = (
                        ["taken", "fallthrough"] if piece[-1].opcode == 0x57 else [None]
                    )
                    for branch in branches:
                        summary = rd.simulate(piece, branch)
                        units.append(rd.render_summary(prefix, case.term, piece, summary))
                        summaries += 1
                        if len(units) == args.shard_size:
                            error = elaborate_shard(units)
                            if error:
                                return case, summaries, error
                            units = []
            if units or summaries == 0:
                error = elaborate_shard(units)
                if error:
                    return case, summaries, error
            return case, summaries, None

        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures = {
                executor.submit(check, index, case): index
                for index, case in enumerate(cases, 1)
            }
            completed = 0
            for future in concurrent.futures.as_completed(futures):
                case, summaries, error = future.result()
                completed += 1
                theorem_count += summaries
                status = "FAIL" if error else "ok"
                print(f"[{completed}/{len(cases)}] {status}: {case.label} "
                      f"({len(case.code)} bytes, {summaries} summaries)", flush=True)
                if error:
                    failures.append((case, error))

    print(f"generated {theorem_count} summaries from {len(cases)} byte arrays")
    if failures:
        print(f"{len(failures)} case(s) failed:", file=sys.stderr)
        for case, detail in failures:
            print(f"\n=== {case.label} ===\n{detail}", file=sys.stderr)
        return 1
    print("all generated summaries elaborated successfully")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
