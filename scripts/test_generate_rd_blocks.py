#!/usr/bin/env python3
"""Focused regressions for Solidity sequence matching in generate_rd_blocks."""

from __future__ import annotations

import unittest

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


def instructions(hex_code: str) -> list[rd.Instruction]:
    return rd.disassemble(bytes.fromhex(hex_code))


def theorem_headers(units: list[str]) -> list[str]:
    return [unit.split(":= by", 1)[0] for unit in units if ":= by" in unit]


class SequencePatternTests(unittest.TestCase):
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
            "60016001609f1b03", "60418051", "62461bcd60e41b8152",
            "604482015290519081900360630190fd",
        ):
            with self.subTest(near_miss=code):
                self.assertIsNone(rd.match_sequence(instructions(code), 0))

    def test_next_four_symbolic_effects_match_primitive_mode(self) -> None:
        for name, code in NEXT_CASES.items():
            with self.subTest(name):
                block = instructions(code)
                enabled = rd.simulate(block, None, True)
                disabled = rd.simulate(block, None, False)
                fields = ("stack_in", "world_map", "existential_counters", "terminal",
                          "extra_hypotheses", "max_stack_prefix", "existential_words")
                if enabled.terminal is None:
                    fields += ("stack_out", "mem", "aw", "pc")
                for field in fields:
                    self.assertEqual(getattr(disabled, field), getattr(enabled, field), field)
                if enabled.terminal is None:
                    self.assertEqual(rd.block_cost(disabled.costs), rd.block_cost(enabled.costs))

        mask_raw = rd.simulate(instructions(NEXT_CASES["address_mask"]), None, False)
        error_raw = rd.simulate(instructions(NEXT_CASES["error_selector_store"]), None, False)
        self.assertEqual(["solcAddrMask"], mask_raw.stack_out)
        self.assertIn("solcErrorStringSelector", error_raw.mem)
        self.assertIn("r5Raw", "\n".join(mask_raw.proof))
        self.assertIn("r3Raw", "\n".join(error_raw.proof))

    def test_push_constants_are_exact(self) -> None:
        for code in ("60013560e01c", "60003560df1c", "3d6001803e3d6000fd"):
            with self.subTest(code):
                self.assertIsNone(rd.match_sequence(instructions(code), 0))

    def test_longest_match_wins(self) -> None:
        match = rd.match_sequence(instructions(CASES["return_data_copy_revert"]), 0)
        self.assertEqual("return_data_copy_revert", match.name)
        summary = rd.simulate(instructions(CASES["return_data_copy_revert"]), None)
        self.assertEqual(1, len(summary.proof))
        self.assertIn("solcSummaryReturnDataCopyRevert", summary.proof[0])

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

    def test_pattern_mode_preserves_theorem_statements(self) -> None:
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
        self.assertEqual(theorem_headers(disabled), theorem_headers(enabled))


if __name__ == "__main__":
    unittest.main()
