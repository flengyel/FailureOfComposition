#!/usr/bin/env bash
# Run Lake with one scheduler worker and inject the port's documented Lean
# compiler resource arguments into every module build, including dependencies.
set -euo pipefail

script_root=$(cd -- "$(dirname -- "$0")" && pwd)
lean_root=$(cd -- "$script_root/.." && pwd)
port_root=$(cd -- "$lean_root/.." && pwd)
wrapper="$script_root/Porting/lean-12288"
bounded_sysroot="$port_root/.codex-work/tmp/lean-sysroot-12288"

if [[ ${LEAN_NUM_THREADS:-1} != 1 ]]; then
  echo "bounded_lake.sh requires LEAN_NUM_THREADS=1" >&2
  exit 2
fi
export LEAN_NUM_THREADS=1

real_lean=$(cd "$lean_root" && elan which lean)
real_sysroot=$(cd -- "$(dirname -- "$real_lean")/.." && pwd)
expected_toolchain=leanprover/lean4:v4.35.0-rc2
actual_toolchain=$(tr -d '\r\n' <"$lean_root/lean-toolchain")
if [[ $actual_toolchain != "$expected_toolchain" ]]; then
  echo "Unexpected Lean toolchain: $actual_toolchain" >&2
  exit 65
fi
if [[ ! -x $wrapper ]]; then
  echo "Bounded Lean launcher is not executable: $wrapper" >&2
  exit 66
fi

mkdir -p "$bounded_sysroot/bin"
for directory in include lib share src; do
  source_path="$real_sysroot/$directory"
  target_path="$bounded_sysroot/$directory"
  [[ ! -e $source_path ]] && continue
  if [[ -L $target_path && $(readlink -f -- "$target_path") == $(readlink -f -- "$source_path") ]]; then
    continue
  elif [[ -e $target_path || -L $target_path ]]; then
    echo "Refusing unexpected bounded sysroot entry: $target_path" >&2
    exit 73
  fi
  ln -s "$source_path" "$target_path"
done
for source_path in "$real_sysroot"/bin/*; do
  name=$(basename -- "$source_path")
  [[ $name == lean ]] && continue
  target_path="$bounded_sysroot/bin/$name"
  if [[ -L $target_path && $(readlink -f -- "$target_path") == $(readlink -f -- "$source_path") ]]; then
    continue
  elif [[ -e $target_path || -L $target_path ]]; then
    echo "Refusing unexpected bounded sysroot entry: $target_path" >&2
    exit 73
  fi
  ln -s "$source_path" "$target_path"
done
bounded_lean="$bounded_sysroot/bin/lean"
if [[ -L $bounded_lean && $(readlink -f -- "$bounded_lean") == $(readlink -f -- "$wrapper") ]]; then
  :
elif [[ -e $bounded_lean || -L $bounded_lean ]]; then
  echo "Refusing unexpected bounded Lean launcher: $bounded_lean" >&2
  exit 73
else
  ln -s "$wrapper" "$bounded_lean"
fi

export FAILCOMP_REAL_LEAN="$real_lean"
export LAKE_OVERRIDE_LEAN=true
export LEAN_SYSROOT="$bounded_sysroot"
cd "$lean_root"
exec lake "$@"
