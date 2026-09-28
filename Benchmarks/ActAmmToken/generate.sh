#!/usr/bin/env bash
set -euo pipefail

ACT_REPO=${ACT_REPO:-/home/lazar/act}
SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
MODE=${1:-write}

if [[ "$MODE" != write && "$MODE" != check ]]; then
  echo "usage: bash Benchmarks/ActAmmToken/generate.sh [write|check]" >&2
  exit 2
fi

if [[ -z ${IN_NIX_SHELL:-} ]]; then
  exec nix develop "$ACT_REPO" --command bash "$0" "$MODE"
fi

ACT_AMM_DIR="$ACT_REPO/tests/hevm/pass/multisource/amm"
ACT_TOKEN_SOURCE="$ACT_REPO/tests/hevm/pass/multisource/erc20/erc20.sol"
if ! jq -e '
    .sources["../erc20/erc20.sol"] == {"language": "Solidity"} and
    .contracts.Token == {"source": "../erc20/erc20.sol"}
  ' "$ACT_AMM_DIR/amm.json" >/dev/null; then
  echo "Act AMM JSON no longer selects Token from ../erc20/erc20.sol as expected" >&2
  exit 1
fi
if ! cmp -s "$ACT_TOKEN_SOURCE" "$SCRIPT_DIR/erc20.sol"; then
  echo "local erc20.sol is not byte-for-byte identical to Act's AMM Token source" >&2
  exit 1
fi

version=$(solc --version | awk '/Version:/ { print $2 }')
if [[ "$version" != 0.8.28+commit.7893614a.Linux.g++ ]]; then
  echo "expected Act's solc 0.8.28, got: $version" >&2
  exit 1
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# Exact input shape from hevm's `solc Solidity src False`, which Act applies
# independently to each Solidity source selected by the multisource JSON.
jq -n --rawfile source "$SCRIPT_DIR/erc20.sol" '
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

jq -r '.contracts["hevm.sol"].Token.evm.bytecode.object' "$work/act-standard-output.json" > "$work/creation.hex"
jq -r '.contracts["hevm.sol"].Token.evm.deployedBytecode.object' "$work/act-standard-output.json" > "$work/runtime.hex"
jq '.contracts["hevm.sol"].Token.abi' "$work/act-standard-output.json" > "$work/Token.abi.json"
jq '.contracts["hevm.sol"].Token.storageLayout' "$work/act-standard-output.json" > "$work/Token.storage.json"
jq '.sources["hevm.sol"].ast' "$work/act-standard-output.json" > "$work/erc20.sol.ast.json"
cp "$work/act-standard-input.json" "$work/compiler-input.json"

python3 "$SCRIPT_DIR/render_bytecode.py" \
  "$work/runtime.hex" "$work/creation.hex" "$work/Bytecode.lean"

(
  cd "$work"
  sha256sum compiler-input.json creation.hex runtime.hex Token.abi.json Token.storage.json erc20.sol.ast.json
  sha256sum "$SCRIPT_DIR/erc20.sol" | sed 's# .*/#  #'
) > "$work/sources.sha256"

artifacts=(compiler-input.json creation.hex runtime.hex Token.abi.json Token.storage.json erc20.sol.ast.json Bytecode.lean sources.sha256)
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
