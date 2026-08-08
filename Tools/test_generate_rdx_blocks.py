#!/usr/bin/env python3

import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest


MODULE_PATH = Path(__file__).with_name("generate_rdx_blocks.py")
FIXTURE_DIR = MODULE_PATH.parent / "SymCheck" / "Fixtures"
SPEC = importlib.util.spec_from_file_location("generate_rdx_blocks", MODULE_PATH)
assert SPEC is not None and SPEC.loader is not None
GEN = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GEN
SPEC.loader.exec_module(GEN)


class GeneratorTests(unittest.TestCase):
    def test_disassembly_skips_push_payload_jumpdest(self) -> None:
        instructions = GEN.disassemble(bytes.fromhex("605b5b00"))
        self.assertEqual([(i.pc, i.opcode) for i in instructions], [(0, 0x60), (2, 0x5B), (3, 0)])

    def test_truncated_push_is_not_rendered(self) -> None:
        code = bytes.fromhex("62ff")
        self.assertIsNone(GEN.render_step(code, {"pc": 0, "opcode": "PUSH3"}))

    def test_discovers_jump_target_and_fallthrough_entries(self) -> None:
        blocks = GEN.discover_blocks(bytes.fromhex("600657005b005b00"), [])
        self.assertEqual(
            [(b.start, b.target, b.terminator) for b in blocks],
            [(0, 2, "JUMPI"), (3, 3, "STOP"), (4, 5, "STOP"), (6, 7, "STOP")],
        )

    def test_every_jumpdest_is_a_trace_root_without_being_a_boundary(self) -> None:
        code = bytes.fromhex("6001600657005b600b56005b00")
        roots = GEN.discover_trace_roots(code, [])
        self.assertEqual([root.start for root in roots], [0, 5, 6, 11])
        rendered, unsupported = GEN.render_trace_steps(
            code,
            [
                {"pc": 0, "opcode": "PUSH1"},
                {"pc": 2, "opcode": "PUSH1"},
                {"pc": 4, "opcode": "JUMPI"},
                {"pc": 6, "opcode": "JUMPDEST"},
                {"pc": 7, "opcode": "PUSH1"},
                {"pc": 9, "opcode": "JUMP"},
                {"pc": 11, "opcode": "JUMPDEST"},
            ],
            12,
        )
        self.assertIsNone(unsupported)
        self.assertIn("jumpiT (by native_decide) (by native_decide)", rendered)
        self.assertIn("jump (by native_decide)", rendered)
        self.assertEqual(rendered.count("jumpdest"), 2)
        self.assertEqual(
            GEN.render_trace_step(code, {"pc": 4, "opcode": "JUMPI"}, 5),
            "jumpiNT (by evm_branch_zero)",
        )

    def test_trace_loop_stops_at_first_pc_revisit(self) -> None:
        summary = {
            "pcTraceOpcodes": [
                {"pc": 13, "opcode": "JUMPDEST"},
                {"pc": 14, "opcode": "PUSH1"},
                {"pc": 16, "opcode": "JUMP"},
                {"pc": 13, "opcode": "JUMPDEST"},
            ]
        }
        self.assertEqual(GEN.first_revisit_step(summary), 3)

    def test_symbolic_jumpi_smt_stop_is_a_complete_trace_boundary(self) -> None:
        self.assertTrue(
            GEN.is_symbolic_control_boundary(
                "JUMPI", 'needs SMT at current opcode (condition (Var "x"))'
            )
        )
        self.assertTrue(
            GEN.is_symbolic_control_boundary(
                "JUMP", 'needs a concrete value at current opcode (expression (Var "target"))'
            )
        )
        self.assertFalse(GEN.is_symbolic_control_boundary("ADD", "needs SMT"))

    def test_push_renderer_uses_explicit_width(self) -> None:
        step = GEN.render_step(bytes.fromhex("62010203"), {"pc": 0, "opcode": "PUSH3"})
        self.assertEqual(step, "pushCanonical 3 .PUSH3 ⟨0x10203⟩ (by decide)")

    def test_deep_stack_opcode_renderers(self) -> None:
        self.assertEqual(GEN.render_step(b"\x8b", {"pc": 0, "opcode": "DUP12"}), "dup12Canonical")
        self.assertEqual(GEN.render_step(b"\x8f", {"pc": 0, "opcode": "DUP16"}), "dup16Canonical")
        self.assertEqual(GEN.render_step(b"\x9f", {"pc": 0, "opcode": "SWAP16"}), "swap16Canonical")

    def test_symbolic_jumpi_edges_are_inferred_from_body(self) -> None:
        edges = GEN.render_control_edge_theorems(
            "block_0_body", "code", 0, 2, 1022, "JUMPI", 3
        )
        self.assertEqual([name for name, _ in edges], ["block_0_taken", "block_0_notTaken"])
        self.assertIn("(block_0_body hdepth h).jumpiT", edges[0][1])
        self.assertIn("fun (hdec : _) (hcondition : _) (hjd : _)", edges[0][1])
        self.assertIn("simp only [List.length_cons]; omega", edges[0][1])
        self.assertIn("(block_0_body hdepth h).jumpiNT", edges[1][1])

        shallow_edges = GEN.render_control_edge_theorems(
            "block_0_body", "code", 0, 2, 1024, "JUMPI", 2
        )
        self.assertIn("(by omega)", shallow_edges[0][1])
        self.assertNotIn("List.length_cons", shallow_edges[0][1])

    def test_terminator_inputs_extend_materialized_tail(self) -> None:
        summary = {"stack": [], "stackTail": {"materialized": 0}}
        self.assertEqual(GEN.materialized_for_edge(summary, "JUMPI"), 2)
        summary = {"stack": ["target"], "stackTail": {"materialized": 3}}
        self.assertEqual(GEN.materialized_for_edge(summary, "JUMPI"), 4)
        self.assertEqual(GEN.materialized_for_edge(summary, "SELFDESTRUCT"), 3)

    def test_markdown_preserves_raw_summary(self) -> None:
        summary = {
            "stop": "target-pc 1", "steps": 1, "gasCost": "3", "pcTraceOpcodes": [],
            "stack": ['(Var "x")'], "memory": "sym:memory", "activeWords": "active_words",
            "returndata": "sym:returndata",
        }
        rendered = GEN.markdown_section({
            "start": 0, "endpoint": 1, "target": 1, "status": "complete",
            "summary": summary,
        })
        self.assertIn("Raw SymCheck JSON", rendered)
        self.assertIn(json.dumps(summary, indent=2, sort_keys=True), rendered)

    def test_large_catalog_is_split_at_block_boundaries(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            output = root / "Generated.lean"
            groups = [
                f"theorem block_{index}_body : True := by trivial\n"
                f"theorem block_{index}_edge : True := by trivial"
                for index in range(5)
            ]
            records = [{"start": index} for index in range(5)]
            paths = GEN.write_lean_catalog(
                output,
                "Generated",
                2,
                ["Reasoning.SymCheck"],
                "Generated.Test",
                "code",
                b"\x00",
                groups,
                records,
            )

            self.assertEqual(
                [path.relative_to(root).as_posix() for path in paths],
                [
                    "Generated.lean",
                    "Generated/Part000.lean",
                    "Generated/Part001.lean",
                    "Generated/Part002.lean",
                ],
            )
            aggregator = output.read_text(encoding="utf-8")
            self.assertIn("import Generated.Part000", aggregator)
            self.assertIn("private theorem symcheckCodeMatches", aggregator)
            for index, part_path in enumerate(paths[1:]):
                part = part_path.read_text(encoding="utf-8")
                self.assertNotIn("symcheckCodeMatches", part)
                first = index * 2
                for block in range(first, min(first + 2, 5)):
                    self.assertIn(f"theorem block_{block}_body", part)
                    self.assertIn(f"theorem block_{block}_edge", part)
                    self.assertEqual(records[block]["leanFile"], str(part_path))

    def test_small_catalog_remains_one_file(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "Small.lean"
            records = [{"start": 0}]
            paths = GEN.write_lean_catalog(
                output, None, 100, ["Reasoning.SymCheck"], "Small", "code", b"",
                ["theorem block_0 : True := by trivial"], records,
            )
            self.assertEqual(paths, [output])
            self.assertIn("symcheckCodeMatches", output.read_text(encoding="utf-8"))
            self.assertEqual(records[0]["leanFile"], str(output))

    def test_committed_catalogs_preserve_every_raw_summary(self) -> None:
        for stem in ("ctor_store_runtime", "dynamic_branch"):
            manifest = json.loads((FIXTURE_DIR / f"{stem}.json").read_text(encoding="utf-8"))
            markdown = (FIXTURE_DIR / f"{stem}.md").read_text(encoding="utf-8")
            self.assertTrue(manifest["complete"])
            self.assertEqual(manifest["generator"], "Tools/generate_rdx_blocks.py")
            for block in manifest["blocks"]:
                raw = json.dumps(block["summary"], indent=2, sort_keys=True)
                self.assertIn(raw, markdown)

    def test_committed_branch_catalog_exercises_edges_and_deep_stack(self) -> None:
        lean = (FIXTURE_DIR / "SymCheckGeneratedBranchSmoke.lean").read_text(encoding="utf-8")
        self.assertIn("set_option maxRecDepth 100000", lean)
        self.assertIn("evm_theorem block_0_taken", lean)
        self.assertIn("evm_theorem block_0_notTaken", lean)
        self.assertIn("evm_theorem block_6_jump", lean)
        self.assertIn("dup12Canonical", lean)
        self.assertIn("swap16Canonical", lean)

    def test_committed_maximal_trace_crosses_roots_and_cuts_loops(self) -> None:
        manifest = json.loads(
            (FIXTURE_DIR / "deterministic_trace.json").read_text(encoding="utf-8")
        )
        markdown = (FIXTURE_DIR / "deterministic_trace.md").read_text(encoding="utf-8")
        lean = (
            FIXTURE_DIR / "SymCheckGeneratedDeterministicTraceSmoke.lean"
        ).read_text(encoding="utf-8")
        self.assertTrue(manifest["complete"])
        self.assertEqual(manifest["catalogKind"], "traces")
        self.assertEqual(manifest["traceRoots"], [0, 5, 6, 11, 13])
        root_zero = next(trace for trace in manifest["traces"] if trace["start"] == 0)
        self.assertEqual(root_zero["endpoint"], 12)
        self.assertEqual(root_zero["endKind"], "halt")
        loop = next(trace for trace in manifest["traces"] if trace["start"] == 13)
        self.assertEqual((loop["endpoint"], loop["endKind"]), (13, "loop-revisit"))
        self.assertIn("jumpiT (by native_decide) (by native_decide)", lean)
        self.assertGreaterEqual(lean.count("jumpdest"), 3)
        for trace in manifest["traces"]:
            raw = json.dumps(trace["summary"], indent=2, sort_keys=True)
            self.assertIn(raw, markdown)


if __name__ == "__main__":
    unittest.main()
