#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 3 || $# -gt 4 ]]; then
  echo "usage: $0 <kind> <forge-target> <output-stem.lean> [solc-version]" >&2
  exit 2
fi

kind="$1"
target="$2"
output="$3"
solc_version="${4:-}"

# Expected 4-byte selectors per model kind, kept in sync with `selectorCases`
# in formal/yul/YulImporter.lean. We assert the wrapper's compiled ABI exposes
# exactly these selectors so a wrapper signature change fails here instead of
# anchoring the proof to the wrong function.
case "$kind" in
  sqrt)    expected="5b29048a 65c9cba1" ;;
  sqrt512) expected="3f51628a 996e33a4" ;;
  cbrt)    expected="29f2f4f1 56df2b56" ;;
  cbrt512) expected="7c0352fc a83a5c08" ;;
  ln)      expected="31d42abd ef102248" ;;
  exp)     expected="4187462b" ;;
  *) echo "unknown kind: $kind" >&2; exit 2 ;;
esac

# Every compile this script triggers must request the Yul IR artifact. `forge
# inspect ... ir` trusts whatever artifact the compile cache serves for the
# target; once any compile in the same cache has produced an IR-less artifact
# for the target (e.g. the methodIdentifiers inspection, or a prior run of
# this script against another wrapper sharing sources), the ir inspection
# fails with "IR output missing from artifact" instead of recompiling.
# Requesting `ir` on every invocation keeps the cache's artifact settings
# uniform, so that failure mode cannot arise.
inspect () {
  local -a fenv=(FOUNDRY_EXTRA_OUTPUT='["ir"]')
  if [[ -n "$solc_version" ]]; then
    fenv+=(FOUNDRY_SOLC_VERSION="$solc_version")
  fi
  env "${fenv[@]}" forge inspect "$target" "$@"
}

actual="$(inspect methodIdentifiers | grep -oiE '\b[0-9a-f]{8}\b' | tr 'A-F' 'a-f' | sort -u | tr '\n' ' ' | sed 's/ $//' || true)"
want="$(echo "$expected" | tr ' ' '\n' | sort -u | tr '\n' ' ' | sed 's/ $//')"
if [[ "$actual" != "$want" ]]; then
  echo "selector mismatch for kind '$kind' target '$target':" >&2
  echo "  expected: $want" >&2
  echo "  actual:   $actual" >&2
  exit 1
fi

inspect ir | lake -d formal/yul exe yul_importer --kind "$kind" --output "$output"
