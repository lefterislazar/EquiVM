#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd -- "$(dirname -- "$0")/.." && pwd)
test_dir=$(mktemp -d)
trap 'rm -rf -- "$test_dir"' EXIT

cd "$repo_root"

python3 scripts/test_generate_rd_blocks.py

# Exercise the original six summariser companions in one elaborating fixture.
# The copy-and-revert patterns appear before their revert suffixes, checking
# longest-match use. The free-memory-pointer extension is covered below by both
# real solc examples and the full corpus check.
python3 scripts/generate_lean_bytecode.py \
  --hex 5f3560e01c0060003560e01c005f5ffd600080fd3d5f5f3e3d5ffd3d6000803e3d6000fd \
  --name summaryPatternsBytecode --output "$test_dir/SummaryPatternsBytecode.lean"
lake env lean -R "$test_dir" -o "$test_dir/SummaryPatternsBytecode.olean" \
  "$test_dir/SummaryPatternsBytecode.lean"
python3 scripts/generate_rd_blocks.py "$test_dir/SummaryPatternsBytecode.lean" \
  --name summaryPatterns --code-term summaryPatternsBytecode \
  --bytecode-import SummaryPatternsBytecode --output "$test_dir/SummaryPatterns.lean"
test "$(rg -c 'RD\.solcSummary' "$test_dir/SummaryPatterns.lean")" -eq 6
LEAN_PATH="$test_dir${LEAN_PATH:+:$LEAN_PATH}" lake env lean "$test_dir/SummaryPatterns.lean"

python3 scripts/generate_lean_bytecode.py \
  --hex 6001600160a01b0300604080510062461bcd60e51b815200604482015290519081900360640190fd \
  --name nextSummaryPatternsBytecode --output "$test_dir/NextSummaryPatternsBytecode.lean"
lake env lean -R "$test_dir" -o "$test_dir/NextSummaryPatternsBytecode.olean" \
  "$test_dir/NextSummaryPatternsBytecode.lean"
python3 scripts/generate_rd_blocks.py "$test_dir/NextSummaryPatternsBytecode.lean" \
  --name nextSummaryPatterns --code-term nextSummaryPatternsBytecode \
  --bytecode-import NextSummaryPatternsBytecode --output "$test_dir/NextSummaryPatterns.lean"
test "$(rg -c 'RD\.solcSummary' "$test_dir/NextSummaryPatterns.lean")" -eq 4
LEAN_PATH="$test_dir${LEAN_PATH:+:$LEAN_PATH}" lake env lean "$test_dir/NextSummaryPatterns.lean"

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
