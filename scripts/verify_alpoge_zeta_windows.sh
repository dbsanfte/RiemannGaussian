#!/bin/sh
# Recheck the small modulus-one adapter and the native window estimates on the repository pin.
set -eu
repo=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
port=$(CDPATH= cd -- "${1:?Pass the path to the checked window-port worktree}" && pwd)
lake_bin=${LAKE:-lake}
cd "$repo"
"$lake_bin" build +RiemannGaussian.PrimeMassFromZeroBound:olean +RiemannGaussian.AlpogeZetaShortIntervals:olean --wfail
"$lake_bin" env sh -eu -c '
  repo=$1
  port=$2
  out="$repo/.lake/dyadic-prime/optional"
  external="$port/RiemannGaussian/External"
  mkdir -p "$out"
  export LEAN_PATH="$out:$port/vendor/alpoge-window/.lake/build/lib/lean:$LEAN_PATH"
  lean --trust=0 -DwarningAsError=true --root="$external" -o "$out/AlpogePrimeWindows.olean" "$external/AlpogePrimeWindows.lean"
  lean --trust=0 -DwarningAsError=true --root="$repo/scripts" -o "$out/CheckAlpogeZetaWindows.olean" "$repo/scripts/CheckAlpogeZetaWindows.lean"
  lean --trust=0 -DwarningAsError=true --root="$repo/scripts" -o "$out/CheckAlpogeExponentialScales.olean" "$repo/scripts/CheckAlpogeExponentialScales.lean"
  leanchecker -v AlpogePrimeWindows CheckAlpogeZetaWindows CheckAlpogeExponentialScales
  if [ -f "$repo/.lake/suzuki-liu/PartIV.olean" ]; then
    export LEAN_PATH="$out:$repo/.lake/suzuki-liu:$LEAN_PATH"
    lean --trust=0 -DwarningAsError=true --root="$repo/scripts" -o "$out/CheckLiuCofactor.olean" "$repo/scripts/CheckLiuCofactor.lean"
    lean --trust=0 -DwarningAsError=true --root="$repo/scripts" -o "$out/CheckAlpogeLiuWindows.olean" "$repo/scripts/CheckAlpogeLiuWindows.lean"
    leanchecker -v CheckLiuCofactor CheckAlpogeLiuWindows
  fi
' sh "$repo" "$port"
