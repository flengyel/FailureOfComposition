#!/usr/bin/env bash
set -euo pipefail

export_file=${1:?export file required}
progress_stride=${2:-100}
export_directory=$(dirname -- "$export_file")
repository_root=/home/flengyel/src/FailureOfComposition-port
toolchain_prefix=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
conron="$toolchain_prefix/bin/con-ron"

[[ $export_file == "$repository_root/"* ]] || {
  printf 'export must be inside the task repository\n' >&2
  exit 2
}
[[ -f $export_file ]] || { printf 'missing export: %s\n' "$export_file" >&2; exit 2; }
[[ $progress_stride =~ ^[1-9][0-9]*$ ]] || {
  printf 'progress stride must be a positive integer\n' >&2
  exit 2
}

exec /usr/bin/bwrap \
  --ro-bind / / \
  --tmpfs /home --tmpfs /root --tmpfs /run/user --tmpfs /tmp \
  --dir /tmp/home --dev /dev --proc /proc --clearenv \
  --tmpfs /run --tmpfs /var \
  --ro-bind "$export_file" "$export_file" \
  --ro-bind "$conron" "$conron" \
  --ro-bind "$toolchain_prefix" "$toolchain_prefix" \
  --setenv LEAN_ABORT_ON_PANIC 1 --setenv HOME /tmp/home \
  --unshare-all --die-with-parent --new-session \
  --chdir "$export_directory" \
  -- "$conron" --verified --jobs=1 --progress="$progress_stride" "$export_file"
