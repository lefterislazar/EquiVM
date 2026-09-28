#!/usr/bin/env bash
set -euo pipefail

ACT_REPO=${ACT_REPO:-/home/lazar/act}
SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
MODE=${1:-write}

if [[ "$MODE" != write && "$MODE" != check ]]; then
  echo "usage: bash Benchmarks/ActAmm4/generate.sh [write|check]" >&2
  exit 2
fi

if [[ -z ${IN_NIX_SHELL:-} ]]; then
  exec nix develop "$ACT_REPO" --command bash "$0" "$MODE"
fi

ACT_FIXTURE_DIR="$ACT_REPO/sand/amm4"
if [[ ! -f "$ACT_FIXTURE_DIR/amm.act" || ! -f "$ACT_FIXTURE_DIR/amm.sol" ]]; then
  echo "missing Act sand/amm4 fixture" >&2
  exit 1
fi
if ! cmp -s "$ACT_FIXTURE_DIR/amm.sol" "$SCRIPT_DIR/amm.sol"; then
  echo "local amm.sol is not byte-for-byte identical to Act's sand/amm4 source" >&2
  exit 1
fi

version=$(solc --version | awk '/Version:/ { print $2 }')
if [[ "$version" != 0.8.28+commit.7893614a.Linux.g++ ]]; then
  echo "expected Act's solc 0.8.28, got: $version" >&2
  exit 1
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Exact Standard JSON shape made by hevm for Act's `--sol` path:
# `solc Solidity source False`, source unit `hevm.sol`, optimizer absent,
# and viaIR disabled.
jq -n --rawfile source "$SCRIPT_DIR/amm.sol" '
  {
    language: "Solidity",
    sources: {"hevm.sol": {content: $source}},
    settings: {
      viaIR: false,
      outputSelection: {
        "*": {
          "*": [
            "metadata",
            "evm.bytecode",
            "evm.deployedBytecode",
            "abi",
            "storageLayout",
            "evm.bytecode.sourceMap",
            "evm.bytecode.linkReferences",
            "evm.bytecode.generatedSources",
            "evm.deployedBytecode.sourceMap",
            "evm.deployedBytecode.linkReferences",
            "evm.deployedBytecode.generatedSources",
            "evm.deployedBytecode.immutableReferences"
          ],
          "": ["ast"]
        }
      }
    }
  }
' > "$work/act-standard-input.json"

solc --standard-json < "$work/act-standard-input.json" > "$work/act-standard-output.json"
if jq -e '.errors // [] | any(.severity == "error")' "$work/act-standard-output.json" >/dev/null; then
  jq -r '.errors[] | select(.severity == "error") | .formattedMessage' "$work/act-standard-output.json" >&2
  exit 1
fi

jq -r '.contracts["hevm.sol"].Amm.evm.bytecode.object' "$work/act-standard-output.json" > "$work/creation.hex"
jq -r '.contracts["hevm.sol"].Amm.evm.deployedBytecode.object' "$work/act-standard-output.json" > "$work/runtime.hex"
jq '.contracts["hevm.sol"].Amm.abi' "$work/act-standard-output.json" > "$work/Amm.abi.json"
jq '.contracts["hevm.sol"].Amm.storageLayout' "$work/act-standard-output.json" > "$work/Amm.storage.json"
jq '.sources["hevm.sol"].ast' "$work/act-standard-output.json" > "$work/amm.sol.ast.json"
cp "$work/act-standard-input.json" "$work/compiler-input.json"

python3 "$SCRIPT_DIR/render_bytecode.py" \
  "$work/runtime.hex" "$work/creation.hex" "$work/Bytecode.lean"

(
  cd "$work"
  sha256sum compiler-input.json creation.hex runtime.hex Amm.abi.json Amm.storage.json amm.sol.ast.json
  sha256sum "$SCRIPT_DIR/amm.sol" | sed 's# .*/#  #'
) > "$work/sources.sha256"

artifacts=(compiler-input.json creation.hex runtime.hex Amm.abi.json Amm.storage.json amm.sol.ast.json Bytecode.lean sources.sha256)
if [[ "$MODE" == check ]]; then
  failed=0
  for artifact in "${artifacts[@]}"; do
    if ! cmp -s "$work/$artifact" "$SCRIPT_DIR/$artifact"; then
      echo "mismatch: $artifact" >&2
      failed=1
    fi
  done
  exit "$failed"
fi

for artifact in "${artifacts[@]}"; do
  cp "$work/$artifact" "$SCRIPT_DIR/$artifact"
done
