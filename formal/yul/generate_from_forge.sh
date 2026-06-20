#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 3 || $# -gt 4 ]]; then
  echo "usage: $0 <kind> <forge-target> <output.lean> [solc-version]" >&2
  exit 2
fi

kind="$1"
target="$2"
output="$3"
solc_version="${4:-}"

if [[ -n "$solc_version" ]]; then
  FOUNDRY_SOLC_VERSION="$solc_version" forge inspect "$target" ir
else
  forge inspect "$target" ir
fi | lake -d formal/yul exe yul_importer --kind "$kind" --output "$output"
