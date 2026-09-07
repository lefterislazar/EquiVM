#!/usr/bin/env python3
"""Reproduce bytecode and RD summaries with solc 0.8.34, legacy/Shanghai, no optimizer."""
import argparse
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import generate_rd_blocks as rd
from generate_lean_bytecode import render


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="verify checked-in artifacts without writing")
    args = parser.parse_args()
    version = subprocess.check_output(["solc", "--version"], text=True)
    if "Version: 0.8.34+commit.80d5c536" not in version:
        raise SystemExit("This fixture requires solc 0.8.34+commit.80d5c536")
    request = {
        "language": "Solidity",
        "sources": {"NestedCaller.sol": {"content": (HERE / "NestedCaller.sol").read_text()}},
        "settings": {
            "optimizer": {"enabled": False}, "viaIR": False, "evmVersion": "shanghai",
            "metadata": {"appendCBOR": False, "bytecodeHash": "none"},
            "outputSelection": {"*": {"*": ["evm.deployedBytecode.object", "evm.methodIdentifiers"]}},
        },
    }
    proc = subprocess.run(["solc", "--standard-json"], input=json.dumps(request),
                          text=True, capture_output=True, check=True)
    result = json.loads(proc.stdout)
    errors = [e["formattedMessage"] for e in result.get("errors", []) if e["severity"] == "error"]
    if errors:
        raise SystemExit("\n".join(errors))
    artifact = result["contracts"]["NestedCaller.sol"]["NestedCaller"]["evm"]
    code = bytes.fromhex(artifact["deployedBytecode"]["object"])
    assert artifact["methodIdentifiers"] == {"run(address,uint256)": "381fd190"}
    assert result["contracts"]["NestedCaller.sol"]["IProbe"]["evm"]["methodIdentifiers"] == {
        "probe(uint256)": "db082440"}
    instructions = rd.disassemble(code)
    jumps = [i.pc for i in instructions if i.opcode == 0x5b]
    # Keep this an integration test of the intended compiler shape. In particular,
    # sample must remain an internal jump/return around a real external CALL.
    assert len(code) == 656
    assert [i.pc for i in instructions if i.opcode == 0x5a] == [194, 284]
    assert [i.pc for i in instructions if i.opcode in rd.CALL_FAMILY_OPCODES] == [285]
    assert all(i.opcode not in {0x54, 0x55, 0xf0, 0xf5} for i in instructions)
    assert code[131:135] == bytes.fromhex("6100bf56")  # JUMP to sample at 191
    assert code[340] == 0x5b and code[345] == 0x56  # helper's dynamic return
    lean = render(code, "nestedCallerBytecode", "NestedCaller", 4096)
    lean = lean.replace("import Ethereum.Semantics", "import Ethereum.Semantics\nimport Reasoning.JumpDest")
    lean += "\nnamespace NestedCaller\n\n@[valid_jumps] theorem nestedCallerValidJumps :\n"
    lean += "    Ethereum.EVM.D_J nestedCallerBytecode 0 = #[" + ", ".join(f"⟨{p}⟩" for p in jumps) + "] := by\n  native_decide\n\nend NestedCaller\n"
    blocks = rd.generate(code, "nestedCaller", "NestedCaller.nestedCallerBytecode",
                         ["Examples.NestedCaller.Bytecode"])
    artifacts = {"Bytecode.lean": lean, "Blocks.lean": blocks}
    if args.check:
        stale = [name for name, text in artifacts.items()
                 if not (HERE / name).exists() or (HERE / name).read_text() != text]
        if stale:
            raise SystemExit("Stale generated artifacts: " + ", ".join(stale))
    else:
        for name, text in artifacts.items():
            (HERE / name).write_text(text)
    action = "Verified" if args.check else "Generated"
    print(f"{action} {len(code)} runtime bytes and {len(jumps)} jump destinations")


if __name__ == "__main__":
    main()
