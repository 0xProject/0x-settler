#!/usr/bin/env bash
set -euo pipefail

: "${GITHUB_OUTPUT:?}"
: "${EVENT_NAME:?}"
: "${HEAD_SHA:?}"

changed_paths="$(mktemp)"
trap 'rm "$changed_paths"' EXIT
route_all=false

case "$EVENT_NAME" in
  pull_request)
    : "${BASE_SHA:?}"
    git diff --name-only --no-renames "$BASE_SHA...$HEAD_SHA" > "$changed_paths"
    ;;
  push)
    zero_sha='0000000000000000000000000000000000000000'
    if [[ -z "${BEFORE_SHA:-}" || "$BEFORE_SHA" == "$zero_sha" ]]; then
      route_all=true
    else
      git diff --name-only --no-renames "$BEFORE_SHA" "$HEAD_SHA" > "$changed_paths"
    fi
    ;;
  *)
    echo "unsupported formal routing event: $EVENT_NAME" >&2
    exit 2
    ;;
esac

common=false
cbrt=false
cbrt512=false
sqrt=false
sqrt512=false
ln=false
exp=false

select_all() {
  common=true
  cbrt=true
  cbrt512=true
  sqrt=true
  sqrt512=true
  ln=true
  exp=true
}

if [[ "$route_all" == true ]]; then
  select_all
fi

while IFS= read -r path; do
  case "$path" in
    .github/workflows/formal.yml | \
    .github/actions/route-formal/* | \
    .github/actions/setup-formal/* | \
    .github/actions/cache-formal-package/* | \
    .github/actions/check-generated-sources/* | \
    .github/actions/fetch-lean-cache/* | \
    formal/yul/* | \
    foundry.toml | remappings.txt | .gitmodules | lib/EVMYulLean)
      select_all
      ;;
    .github/actions/build-cbrt-proof/* | formal/cbrt/* | formal/python/cbrt/*)
      cbrt=true
      cbrt512=true
      ;;
    .github/actions/build-cbrt512-proof/* | src/wrappers/Cbrt512Wrapper.sol)
      cbrt512=true
      ;;
    .github/actions/build-sqrt-proof/* | formal/sqrt/* | formal/python/sqrt/*)
      sqrt=true
      sqrt512=true
      ;;
    .github/actions/build-sqrt512-proof/* | src/wrappers/Sqrt512Wrapper.sol)
      sqrt512=true
      ;;
    .github/actions/build-common-proof/* | .github/actions/build-ln-proof/* | \
    formal/common/* | formal/ln/* | \
    src/vendor/Ln.sol | src/wrappers/LnWrapper.sol)
      common=true
      ln=true
      exp=true
      ;;
    .github/actions/build-exp-proof/* | formal/exp/* | src/vendor/Exp.sol | \
    src/wrappers/ExpWrapper.sol)
      exp=true
      ;;
    src/wrappers/CbrtWrapper.sol)
      cbrt=true
      cbrt512=true
      ;;
    src/wrappers/SqrtWrapper.sol)
      sqrt=true
      sqrt512=true
      ;;
    src/vendor/Cbrt.sol)
      cbrt=true
      cbrt512=true
      sqrt512=true
      ;;
    src/vendor/Sqrt.sol)
      cbrt512=true
      sqrt=true
      sqrt512=true
      ;;
    src/vendor/Clz.sol)
      cbrt512=true
      sqrt512=true
      exp=true
      ;;
    src/utils/FastLogic.sol)
      cbrt512=true
      sqrt512=true
      exp=true
      ;;
    src/utils/Panic.sol)
      cbrt512=true
      sqrt512=true
      ln=true
      exp=true
      ;;
    src/utils/512Math.sol | src/utils/Ternary.sol | src/utils/UnsafeMath.sol | lib/forge-std)
      cbrt512=true
      sqrt512=true
      ;;
  esac
done < "$changed_paths"

if [[ "$cbrt512" == true ]]; then
  cbrt=true
fi
if [[ "$sqrt512" == true ]]; then
  sqrt=true
fi
if [[ "$exp" == true ]]; then
  common=true
  ln=true
fi
if [[ "$ln" == true ]]; then
  common=true
fi

any=false
if [[ "$common" == true || "$cbrt" == true || "$cbrt512" == true || \
      "$sqrt" == true || "$sqrt512" == true || "$ln" == true || "$exp" == true ]]; then
  any=true
fi

{
  printf 'any=%s\n' "$any"
  printf 'common=%s\n' "$common"
  printf 'cbrt=%s\n' "$cbrt"
  printf 'cbrt512=%s\n' "$cbrt512"
  printf 'sqrt=%s\n' "$sqrt"
  printf 'sqrt512=%s\n' "$sqrt512"
  printf 'ln=%s\n' "$ln"
  printf 'exp=%s\n' "$exp"
} >> "$GITHUB_OUTPUT"
