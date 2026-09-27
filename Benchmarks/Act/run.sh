#!/usr/bin/env bash
set -u

ACT_REPO=${ACT_REPO:-/home/lazar/act}
MODE=${1:-check}
SOLVER=${SOLVER:-cvc5}
SMT_TIMEOUT=${SMT_TIMEOUT:-100000000}
NUM_SOLVERS=${NUM_SOLVERS:-1}

if [[ "$MODE" != check && "$MODE" != bench ]]; then
  echo "usage: bash Benchmarks/Act/run.sh [check|bench]" >&2
  exit 2
fi

if [[ -z ${IN_NIX_SHELL:-} ]]; then
  exec nix develop "$ACT_REPO" --command bash "$0" "$MODE"
fi

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
RESULT_DIR=$(mktemp -d)
trap 'rm -rf "$RESULT_DIR"' EXIT

cd "$ACT_REPO" || exit 1
cabal build exe:act >/dev/null || exit 1
ACT_BIN=$(cabal list-bin exe:act) || exit 1

if [[ "$MODE" == bench ]]; then
  RUNS=${REPEATS:-3}
else
  RUNS=1
fi

mapfile -t MOCKED < <(find "$SCRIPT_DIR" -type f -path '*/mocked/*.act' | sort)
mapfile -t STANDALONE < <(find "$SCRIPT_DIR" -type f -path '*/standalone/*.act' | sort)
SPECS=("${MOCKED[@]}" "${STANDALONE[@]}")

printf 'target\tvariant\trun\tstatus\telapsed_ms\n'
FAILED=0
for spec in "${SPECS[@]}"; do
  sol=${spec%.act}.sol
  variant=$(basename "$(dirname "$spec")")
  target=$(basename "$(dirname "$(dirname "$spec")")")
  for ((run = 1; run <= RUNS; run++)); do
    log="$RESULT_DIR/${target}-${variant}-${run}.log"
    start=$(date +%s%N)
    "$ACT_BIN" equiv \
      --spec "$spec" \
      --sol "$sol" \
      --solver "$SOLVER" \
      --numsolvers "$NUM_SOLVERS" \
      --smttimeout "$SMT_TIMEOUT" >"$log" 2>&1
    status=$?
    end=$(date +%s%N)
    elapsed=$(((end - start) / 1000000))
    if [[ $status -eq 0 ]]; then
      result=pass
    else
      result=fail
      FAILED=1
      sed -n '1,240p' "$log" >&2
    fi
    printf '%s\t%s\t%s\t%s\t%s\n' "$target" "$variant" "$run" "$result" "$elapsed"
  done
done

exit "$FAILED"
