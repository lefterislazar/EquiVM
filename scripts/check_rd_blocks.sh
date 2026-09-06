#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
test_dir=$(mktemp -d)
trap 'rm -rf -- "$test_dir"' EXIT

cd "$repo_root"

python3 scripts/generate_rd_blocks.py Examples/Truth/Bytecode.lean \
  --name truthAuto --code-term truthBytecode \
  --bytecode-import Examples.Truth.Bytecode \
  --fail-on-unsupported --output "$test_dir/TruthBlocksAuto.lean"
lake env lean "$test_dir/TruthBlocksAuto.lean"

python3 scripts/generate_rd_blocks.py Examples/ERC20/Bytecode.lean \
  --name erc20Auto --code-term erc20Bytecode \
  --bytecode-import Examples.ERC20.Bytecode \
  --fail-on-unsupported --output "$test_dir/ERC20BlocksAuto.lean"
lake env lean "$test_dir/ERC20BlocksAuto.lean"

python3 scripts/generate_lean_bytecode.py --hex 6001f16002fa600349600460050100 \
  --name unsupportedSplitBytecode --output "$test_dir/UnsupportedSplitBytecode.lean"
lake env lean -R "$test_dir" -o "$test_dir/UnsupportedSplitBytecode.olean" \
  "$test_dir/UnsupportedSplitBytecode.lean"

python3 scripts/generate_rd_blocks.py "$test_dir/UnsupportedSplitBytecode.lean" \
  --name unsupportedSplit --code-term unsupportedSplitBytecode \
  --bytecode-import UnsupportedSplitBytecode \
  --shard-size 1 --output "$test_dir/UnsupportedSplit.lean"
test "$(find "$test_dir" -maxdepth 1 -name 'UnsupportedSplit_*.lean' | wc -l)" -gt 1
for shard in "$test_dir"/UnsupportedSplit_*.lean; do
  LEAN_PATH="$test_dir${LEAN_PATH:+:$LEAN_PATH}" lake env lean "$shard"
done

# RETURNDATACOPY, SSTORE, and LOG1 all need side conditions.  They must be
# lifted to one block theorem without stopping simulation at any instruction.
python3 scripts/generate_lean_bytecode.py \
  --hex 6000600060003e6001600055600360006000a16002600301 \
  --name extraRequirementsBytecode --output "$test_dir/ExtraRequirementsBytecode.lean"
lake env lean -R "$test_dir" -o "$test_dir/ExtraRequirementsBytecode.olean" \
  "$test_dir/ExtraRequirementsBytecode.lean"

python3 scripts/generate_rd_blocks.py "$test_dir/ExtraRequirementsBytecode.lean" \
  --name extraRequirements --code-term extraRequirementsBytecode \
  --bytecode-import ExtraRequirementsBytecode \
  --shard-size 1 --output "$test_dir/ExtraRequirements.lean"
rg -Fq '(hguard0 :' "$test_dir/ExtraRequirements_001.lean"
test "$(rg -Fh '(hperm :' "$test_dir"/ExtraRequirements_*.lean | wc -l)" -eq 1
rg -q 'have r14 := r13.add' "$test_dir"/ExtraRequirements_*.lean
for shard in "$test_dir"/ExtraRequirements_*.lean; do
  LEAN_PATH="$test_dir${LEAN_PATH:+:$LEAN_PATH}" lake env lean "$shard"
done

if python3 scripts/generate_rd_blocks.py --hex 6001f1 --name unsupportedStrict \
    --code-term unsupportedSplitBytecode --bytecode-import UnsupportedSplitBytecode \
    --output "$test_dir/Strict.lean" --fail-on-unsupported >/dev/null 2>&1; then
  echo "expected --fail-on-unsupported to reject CALL" >&2
  exit 1
fi
