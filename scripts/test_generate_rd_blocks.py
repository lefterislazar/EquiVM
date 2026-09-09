#!/usr/bin/env python3
"""Focused regressions for Solidity sequence matching in generate_rd_blocks."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import generate_rd_blocks as rd


CASES = {
    "return_data_copy_revert": "3d5f5f3e3d5ffd",
    "legacy_return_data_copy_revert": "3d6000803e3d6000fd",
    "selector_load": "5f3560e01c",
    "legacy_selector_load": "60003560e01c",
    "revert0": "5f5ffd",
    "legacy_revert0": "600080fd",
}

NEXT_CASES = {
    "address_mask": "6001600160a01b03",
    "free_memory_pointer_load": "60408051",
    "error_selector_store": "62461bcd60e51b8152",
    "error_revert_finalizer": "604482015290519081900360640190fd",
}

MIGRATED_CASES = {
    "low_mask": "60016001609f1b03",
    "uint_max": "600019",
    "left_aligned_selector": "63ffffffff1660e01b",
    "bool_normalize": "1515",
    "selector_condition": "80631234567814611234",
    "selector_split_condition": "8063123456781162123456",
    "call_success_condition": "158015611234",
    "callvalue_condition": "348015",
    "calldata_size_condition": "60043610611234",
    "returndata_size_condition": "3d6020811015611234",
    "static_args_condition": "5b61123460048036036064811015615678",
    "checked_add_condition": "5b80820182811015615678",
    "checked_sub_condition": "5b80820382811115615678",
    "mapping_hash_key_first": "6000908152600160205260409020",
    "mapping_hash_slot_first": "6001602052600090815260409020",
}


def instructions(hex_code: str) -> list[rd.Instruction]:
    return rd.disassemble(bytes.fromhex(hex_code))


def theorem_headers(units: list[str]) -> list[str]:
    return [unit.split(":= by", 1)[0] for unit in units if ":= by" in unit]


def generated_line(rendered: str, prefix: str) -> str:
    return next(line for line in rendered.splitlines() if line.startswith(prefix))


class SequencePatternTests(unittest.TestCase):
    def test_gas_and_call_family_are_execution_split_boundaries(self) -> None:
        block = instructions("60005a6001f16002f26003f46004fa6005")
        pieces = rd.supported_segments(block)
        self.assertEqual(
            [[0x60], 0x5A, [0x60], 0xF1, [0x60], 0xF2,
             [0x60], 0xF4, [0x60], 0xFA, [0x60]],
            [piece.opcode if isinstance(piece, rd.Instruction)
             else [ins.opcode for ins in piece] for piece in pieces],
        )

    def test_gas_split_is_not_unsupported(self) -> None:
        units = rd.generate_units(bytes.fromhex("305a600100"), "gas", "code",
                                  fail_on_unsupported=True, keep_metadata=True)
        output = "\n".join(units)
        self.assertIn("Execution split boundary at pc 1: gas", output)
        self.assertIn("theorem gas_block_0", output)
        self.assertIn("theorem gas_block_2", output)
        self.assertNotIn("RD.gas", output)
        self.assertEqual(2, len(theorem_headers(units)))

    def test_call_family_instructions_are_outside_adjacent_summaries(self) -> None:
        code = bytes.fromhex("6000f16001f26002f46003fa600400")
        units = rd.generate_units(code, "calls", "code", keep_metadata=True)
        output = "\n".join(units)
        self.assertEqual(
            [0, 3, 6, 9, 12],
            [int(header.split("theorem calls_block_", 1)[1].split()[0])
             for header in theorem_headers(units)],
        )
        for pc, name in ((2, "call"), (5, "callcode"),
                         (8, "delegatecall"), (11, "staticcall")):
            self.assertIn(f"boundary at pc {pc}: {name}", output)

    def test_creation_mode_quantifies_tail_and_lifts_prefix_facts(self) -> None:
        # Free-memory-pointer pattern; PUSH1 8; JUMP; JUMPDEST; CODESIZE.
        # The prefix is deliberately shorter than 33 bytes to exercise both
        # sequence witnesses and exact-width decode lifting.
        units = rd.generate_units(
            bytes.fromhex("60806040526008565b38"), "creation", "creationBytecode",
            keep_metadata=True, creation_code=True,
        )
        rendered = "\n".join(units)
        self.assertIn("{tail : ByteArray}", rendered)
        self.assertIn("RD (creationBytecode ++ tail)", rendered)
        self.assertIn("(UInt256.ofNat (creationBytecode ++ tail).size)", rendered)
        self.assertIn("d tail _ _ _", rendered)
        self.assertIn("RD.solcSummaryFreeMemoryPointer", rendered)
        self.assertIn("(D_J creationBytecode 0).contains", rendered)
        self.assertIn("j tail", rendered)

        module = rd.render_module(
            "creation", ["CreationBytecode"], units, True, "creationBytecode"
        )
        self.assertIn(
            "private abbrev d := Reasoning.Theory.decode_append_left_of_decode creationBytecode",
            module,
        )
        self.assertIn(
            "private abbrev j := Reasoning.Theory.D_J_contains_append_left creationBytecode",
            module,
        )
        self.assertEqual(1, module.count("decode_append_left_of_decode"))
        self.assertEqual(1, module.count("D_J_contains_append_left"))

    def test_runtime_mode_remains_closed_over_code_term(self) -> None:
        units = rd.generate_units(
            bytes.fromhex("600100"), "runtime", "runtimeBytecode",
            keep_metadata=True,
        )
        rendered = "\n".join(units)
        self.assertNotIn("{tail : ByteArray}", rendered)
        self.assertNotIn("decode_append_left_of_decode", rendered)
        self.assertIn("RD runtimeBytecode", rendered)

    def test_packed_summary_hides_final_counters_and_active_words(self) -> None:
        units = rd.generate_units(
            bytes.fromhex("6001"), "runtime", "runtimeBytecode",
            keep_metadata=True,
        )
        rendered = "\n".join(units)
        self.assertIn("def runtime_block_0_stack {R : List UInt256}", rendered)
        self.assertIn("theorem runtime_block_0_packed", rendered)
        self.assertIn("∃ (aw' : UInt256) (k' C' : ℕ), RD runtimeBytecode", rendered)
        self.assertNotIn("def runtime_block_0_memory", rendered)
        self.assertIn("(runtime_block_0_stack (R := R)) mem aw' rdata", rendered)
        self.assertIn("RD.pack (runtime_block_0 hstack h)", rendered)

    def test_final_value_definitions_scan_needed_parameters(self) -> None:
        units = rd.generate_units(
            bytes.fromhex("35"), "runtime", "runtimeBytecode",
            keep_metadata=True,
        )
        rendered = "\n".join(units)
        self.assertEqual(
            "def runtime_block_0_stack {ee : ExecutionEnv} {x0 : UInt256} "
            "{R : List UInt256} : List UInt256 :=",
            generated_line(rendered, "def runtime_block_0_stack"),
        )
        self.assertNotIn("def runtime_block_0_memory", rendered)
        self.assertIn(
            "(runtime_block_0_stack (ee := ee) (x0 := x0) (R := R)) mem",
            rendered,
        )

    def test_trivial_final_values_do_not_emit_definitions(self) -> None:
        units = rd.generate_units(
            bytes.fromhex("5b"), "runtime", "runtimeBytecode",
            keep_metadata=True,
        )
        rendered = "\n".join(units)
        self.assertNotIn("def runtime_block_0_stack", rendered)
        self.assertNotIn("def runtime_block_0_memory", rendered)
        self.assertIn("RD runtimeBytecode ee g s0 (UInt256.ofNat 1) R mem aw", rendered)

    def test_final_memory_definition_scans_stack_input_parameters(self) -> None:
        units = rd.generate_units(
            bytes.fromhex("52"), "runtime", "runtimeBytecode",
            keep_metadata=True,
        )
        rendered = "\n".join(units)
        self.assertEqual(
            "def runtime_block_0_memory {mem : ByteArray} {x0 : UInt256} "
            "{x1 : UInt256} : ByteArray :=",
            generated_line(rendered, "def runtime_block_0_memory"),
        )
        self.assertIn(
            "(runtime_block_0_memory (mem := mem) (x0 := x0) (x1 := x1))",
            rendered,
        )

    def test_final_stack_definition_scans_existential_word_parameters(self) -> None:
        summary = rd.Summary(
            ["x0"], ["gasWord0", "x0"], "mem", "aw", "σ", "0", [], [],
            True, None, [], None, 1, ["gasWord0"], "r0",
        )
        rendered = "\n".join(
            rd.render_final_value_defs(
                "runtime_block_0", summary, "runtimeBytecode", False,
            ).lines
        )
        self.assertEqual(
            "def runtime_block_0_stack {x0 : UInt256} "
            "{R : List UInt256} {gasWord0 : UInt256} : List UInt256 :=",
            generated_line(rendered, "def runtime_block_0_stack"),
        )
        self.assertIn(
            "gasWord0 :: x0 :: R",
            rendered,
        )

    def test_packed_summary_repackages_existential_counter_blocks(self) -> None:
        units = rd.generate_units(
            bytes.fromhex("600054"), "runtime", "runtimeBytecode",
            keep_metadata=True,
        )
        rendered = "\n".join(units)
        self.assertIn("theorem runtime_block_0_packed", rendered)
        self.assertIn("obtain ⟨k0, C0, h0⟩ := runtime_block_0 hstack h", rendered)
        self.assertIn("obtain ⟨k', C', h'⟩ := RD.pack h0", rendered)

    def test_creation_packed_summary_lifts_code_terms_inside_symbolic_results(self) -> None:
        units = rd.generate_units(
            bytes.fromhex("38"), "creation", "creationBytecode",
            keep_metadata=True, creation_code=True,
        )
        rendered = "\n".join(units)
        self.assertEqual(
            "def creation_block_0_stack {tail : ByteArray} {R : List UInt256} "
            ": List UInt256 :=",
            generated_line(rendered, "def creation_block_0_stack"),
        )
        self.assertIn("(UInt256.ofNat (creationBytecode ++ tail).size)", rendered)
        self.assertNotIn("__CODE__", rendered)

        namespaced_units = rd.generate_units(
            bytes.fromhex("38"), "creation", "Creation.C.bytecode",
            keep_metadata=True, creation_code=True,
        )
        self.assertEqual(
            "def creation_block_0_stack {tail : ByteArray} {R : List UInt256} "
            ": List UInt256 :=",
            generated_line("\n".join(namespaced_units), "def creation_block_0_stack"),
        )

    def test_write_outputs_emits_compact_theorem_index(self) -> None:
        records = rd.generate_unit_records(
            bytes.fromhex("526001"), "runtime", "runtimeBytecode",
            keep_metadata=True,
        )
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "RuntimeBlocks.lean"
            rd.write_outputs(output, "runtime", ["RuntimeBytecode"], records, None)
            index = output.with_suffix(".index").read_text(encoding="utf-8").splitlines()
            rendered = output.read_text(encoding="utf-8").splitlines()

        self.assertEqual(2, len(index))
        self.assertEqual(["runtime_block_0", "runtime_block_0_packed"],
                         [line.split("\t")[0] for line in index])
        for line in index:
            theorem, location, pcs = line.split("\t")
            file_name, span = location.split(":")
            start, end = (int(part) for part in span.split("-"))
            self.assertEqual("RuntimeBlocks.lean", file_name)
            self.assertEqual("0 1", pcs)
            ranged = rendered[start - 1:end]
            self.assertTrue(any(line.startswith(f"theorem {theorem} ") for line in ranged))
            self.assertTrue(ranged[0].startswith("/-- Final stack"))
            self.assertTrue(any(line.startswith("/-- Final memory") for line in ranged))
            self.assertGreaterEqual(end, start)

    def test_sharded_outputs_emit_one_index_with_actual_shard_names(self) -> None:
        records = rd.generate_unit_records(
            bytes.fromhex("5b5b"), "runtime", "runtimeBytecode",
            keep_metadata=True,
        )
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "RuntimeBlocks.lean"
            rd.write_outputs(output, "runtime", ["RuntimeBytecode"], records, 1)
            index = output.with_suffix(".index").read_text(encoding="utf-8")

        self.assertIn("runtime_block_0\tRuntimeBlocks_001.lean:", index)
        self.assertIn("\t0", index)
        self.assertIn("runtime_block_1\tRuntimeBlocks_002.lean:", index)
        self.assertIn("\t1", index)

    def test_write_outputs_honors_explicit_index_path(self) -> None:
        records = rd.generate_unit_records(
            bytes.fromhex("5b"), "runtime", "runtimeBytecode",
            keep_metadata=True,
        )
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "RuntimeBlocks.lean"
            index_output = Path(temp) / "RuntimeBlocks.tsv"
            rd.write_outputs(output, "runtime", ["RuntimeBytecode"], records, None,
                             index_output=index_output)
            self.assertTrue(index_output.exists())
            self.assertFalse(output.with_suffix(".index").exists())

    def test_write_outputs_emits_empty_index_for_no_theorems(self) -> None:
        records = rd.generate_unit_records(
            bytes.fromhex("f1"), "runtime", "runtimeBytecode",
            keep_metadata=True,
        )
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp) / "RuntimeBlocks.lean"
            rd.write_outputs(output, "runtime", ["RuntimeBytecode"], records, None)
            index_output = output.with_suffix(".index")
            self.assertTrue(index_output.exists())
            self.assertEqual("", index_output.read_text(encoding="utf-8"))

    def test_terminal_blocks_do_not_emit_packed_summaries(self) -> None:
        units = rd.generate_units(
            bytes.fromhex("600100"), "runtime", "runtimeBytecode",
            keep_metadata=True,
        )
        self.assertNotIn("_packed", "\n".join(units))

    def test_dynamic_gas_constants_emit_as_numerals(self) -> None:
        for code in ("60006000602039", "6000602020", "600060206001a1"):
            with self.subTest(code):
                summary = rd.simulate(instructions(code), None)
                costs = "\n".join(str(cost) for cost in summary.costs)
                self.assertNotIn("GasConstants.", costs)
        self.assertIn("3 + 3 *", "\n".join(str(cost) for cost in
                                            rd.simulate(instructions("60006000602039"), None).costs))
        self.assertIn("30 + 6 *", "\n".join(str(cost) for cost in
                                             rd.simulate(instructions("6000602020"), None).costs))
        self.assertIn("375 + 8 *", "\n".join(str(cost) for cost in
                                              rd.simulate(instructions("600060206001a1"), None).costs))

    def test_all_six_patterns_match(self) -> None:
        for expected, code in CASES.items():
            with self.subTest(expected):
                match = rd.match_sequence(instructions(code), 0)
                self.assertIsNotNone(match)
                self.assertEqual(expected, match.name)

    def test_free_memory_pointer_extension_matches(self) -> None:
        match = rd.match_sequence(instructions("6080604052"), 0)
        self.assertIsNotNone(match)
        self.assertEqual("free_memory_pointer", match.name)
        self.assertIsNone(rd.match_sequence(instructions("6081604052"), 0))

    def test_next_four_patterns_match_exactly(self) -> None:
        for expected, code in NEXT_CASES.items():
            with self.subTest(expected):
                match = rd.match_sequence(instructions(code), 0)
                self.assertIsNotNone(match)
                self.assertEqual(expected, match.name)

        for code in (
            "60016002609f1b03", "60418051", "62461bcd60e41b8152",
            "604482015290519081900360630190fd",
        ):
            with self.subTest(near_miss=code):
                self.assertIsNone(rd.match_sequence(instructions(code), 0))

    def test_migrated_patterns_capture_values_and_widths(self) -> None:
        for expected, code in MIGRATED_CASES.items():
            with self.subTest(expected):
                match = rd.match_sequence(instructions(code), 0)
                self.assertIsNotNone(match)
                self.assertEqual(expected, match.name)

        # The final target PUSH is width-generic for these condition producers.
        for width_code in ("806312345678146012", "8063123456781462123456"):
            self.assertEqual("selector_condition",
                             rd.match_sequence(instructions(width_code), 0).name)

    def test_migrated_patterns_are_fully_disabled_in_primitive_mode(self) -> None:
        for name, code in MIGRATED_CASES.items():
            with self.subTest(name):
                block = instructions(code)
                enabled = rd.simulate(block, None, True)
                disabled = rd.simulate(block, None, False)
                self.assertIn("solcSummary", "\n".join(enabled.proof))
                self.assertNotIn("solcSummary", "\n".join(disabled.proof))
                self.assertEqual(len(block), len(disabled.proof))

    def test_migrated_patterns_stay_inside_segments_and_shards(self) -> None:
        for name, code in MIGRATED_CASES.items():
            with self.subTest(name):
                pattern = instructions(code)
                run = instructions("30" * 63 + code)
                pieces = rd.bounded_supported_segments(run, 64)
                self.assertEqual([63, len(pattern)], [len(piece) for piece in pieces])

    def test_nested_mapping_pair_composes_inside_one_block(self) -> None:
        code = "5b60016020908152600092835260408084209091529082529020548156"
        block = instructions(code)
        self.assertEqual("nested_mapping_inner_hash", rd.match_sequence(block, 0).name)
        inner_len = 14
        self.assertEqual("nested_mapping_outer_hash",
                         rd.match_sequence(block, inner_len).name)
        enabled = rd.simulate(block, None, True)
        disabled = rd.simulate(block, None, False)
        for field in ("stack_in", "aw", "pc", "extra_hypotheses",
                      "max_stack_prefix", "existential_counters"):
            self.assertEqual(getattr(disabled, field), getattr(enabled, field), field)
        self.assertIn("solcSummaryNestedMappingInnerHash", "\n".join(enabled.proof))
        self.assertIn("solcSummaryNestedMappingOuterHash", "\n".join(enabled.proof))
        self.assertNotIn("solcSummaryNestedMapping", "\n".join(disabled.proof))
        self.assertIn("RD.keccak256", "\n".join(disabled.proof))

    def test_next_four_patterns_are_fully_disabled_in_primitive_mode(self) -> None:
        for name, code in NEXT_CASES.items():
            with self.subTest(name):
                block = instructions(code)
                enabled = rd.simulate(block, None, True)
                disabled = rd.simulate(block, None, False)
                self.assertIn("solcSummary", "\n".join(enabled.proof))
                self.assertNotIn("solcSummary", "\n".join(disabled.proof))
                self.assertEqual(len(block), len(disabled.proof))

    def test_push_constants_are_exact(self) -> None:
        for code in ("60013560e01c", "60003560df1c", "3d6001803e3d6000fd"):
            with self.subTest(code):
                self.assertIsNone(rd.match_sequence(instructions(code), 0))

    def test_mandatory_full_copy_summary_takes_precedence(self) -> None:
        match = rd.match_sequence(instructions(CASES["return_data_copy_revert"]), 0)
        self.assertEqual("return_data_copy_revert", match.name)
        summary = rd.simulate(instructions(CASES["return_data_copy_revert"]), None)
        self.assertEqual(4, len(summary.proof))
        self.assertIn("returndatacopyFull", summary.proof[0])

    def test_split_does_not_cut_pattern(self) -> None:
        run = instructions("30" * 63 + CASES["return_data_copy_revert"])
        pieces = rd.bounded_supported_segments(run, 64)
        self.assertEqual([63, 7], [len(piece) for piece in pieces])

        for name, code in NEXT_CASES.items():
            with self.subTest(name):
                pattern = instructions(code)
                run = instructions("30" * 63 + code)
                pieces = rd.bounded_supported_segments(run, 64)
                self.assertEqual([63, len(pattern)], [len(piece) for piece in pieces])

    def test_opt_out_uses_primitive_steppers(self) -> None:
        block = instructions(CASES["selector_load"])
        enabled = rd.simulate(block, None, True)
        disabled = rd.simulate(block, None, False)
        self.assertIn("solcSummarySelectorLoad", "\n".join(enabled.proof))
        self.assertNotIn("solcSummarySelectorLoad", "\n".join(disabled.proof))
        self.assertEqual(4, len(disabled.proof))

    def test_opt_out_keeps_mapping_hashes_primitive(self) -> None:
        for name in ("mapping_hash_key_first", "mapping_hash_slot_first"):
            with self.subTest(name):
                block = instructions(MIGRATED_CASES[name])
                enabled = rd.simulate(block, None, True)
                disabled = rd.simulate(block, None, False)
                self.assertIn("solcSummaryMapping", "\n".join(enabled.proof))
                self.assertNotIn("solcSummaryMapping", "\n".join(disabled.proof))
                self.assertIn("RD.keccak256", "\n".join(disabled.proof))

    def test_opt_out_avoids_all_registered_sequence_theorems(self) -> None:
        # Add STOP after selector loads so those blocks have terminal statements;
        # revert patterns already terminate themselves.
        code = bytes.fromhex("608060405200" + "5f3560e01c0060003560e01c00" +
                             CASES["return_data_copy_revert"] +
                             CASES["legacy_return_data_copy_revert"] +
                             CASES["revert0"] + CASES["legacy_revert0"] +
                             NEXT_CASES["address_mask"] + "00" +
                             NEXT_CASES["free_memory_pointer_load"] + "00" +
                             NEXT_CASES["error_selector_store"] + "00" +
                             NEXT_CASES["error_revert_finalizer"])
        enabled = rd.generate_units(code, "same", "code", keep_metadata=True,
                                    use_sequence_patterns=True)
        disabled = rd.generate_units(code, "same", "code", keep_metadata=True,
                                     use_sequence_patterns=False)
        self.assertIn("RD.solcSummary", "\n".join(enabled))
        self.assertNotIn("RD.solcSummary", "\n".join(disabled))


if __name__ == "__main__":
    unittest.main()
