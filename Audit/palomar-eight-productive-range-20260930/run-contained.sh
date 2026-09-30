#!/usr/bin/env bash
set -euo pipefail

repository_root=/home/flengyel/src/FailureOfComposition-port
run=$(realpath -m "${1:?explicit run directory required}")
deadline=${2:?deadline required}
workload_dir=${3:?workload directory required}
shift 3

case "$run" in
  "$repository_root"/.codex-work/palomar/eight-productive-range/*/runs/*) ;;
  *) echo "run directory is outside the Eight evidence hierarchy: $run" >&2; exit 2 ;;
esac
[[ $deadline =~ ^[0-9]+$ ]] && (( deadline > 0 && deadline <= 1200 )) || {
  echo "deadline outside 1..1200 seconds" >&2; exit 2;
}
[[ -d $workload_dir ]] || { echo "missing workload directory" >&2; exit 2; }
(( $# > 0 )) || { echo "payload command required" >&2; exit 2; }

[[ ! -e $run ]] || { echo "run evidence already exists: $run" >&2; exit 2; }
mkdir -p "$run/source-snapshot"

cd "$repository_root"
source scripts/verify-palomar.sh
supervisor="$repository_root/.codex-work/palomar/termsubst-integration/20260929T062653Z/tools/supervise_build.py"
memory_high=8G
memory_max=10G
memory_swap=0
physical_headroom=2147483648
available_reserve=4294967296
cpu_list=0

cp "$repository_root/Audit/palomar-eight-productive-range-20260930/run-contained.sh" \
  "$run/source-snapshot/"
cp "$supervisor" "$run/source-snapshot/supervise_build.py"
cp "$repository_root/scripts/verify-palomar.sh" "$run/source-snapshot/"
cp "$repository_root/scripts/palomar_launcher_checks.py" "$run/source-snapshot/"
find "$run/source-snapshot" -type f -print0 | sort -z | xargs -0 sha256sum \
  >"$run/source-snapshot/SHA256SUMS"

check_delegated_cgroup
check_no_checker_processes
check_phase_capacity checker "$memory_max" "$memory_swap" \
  "$physical_headroom" "$available_reserve" 0 "$run/capacity.json"

high_bytes=$(size_bytes "$memory_high")
max_bytes=$(size_bytes "$memory_max")
swap_bytes=$(size_bytes "$memory_swap")
prefix=/home/flengyel/.elan/toolchains/leanprover--lean4---v4.35.0-rc2
[[ $("$prefix/bin/lean" --print-prefix) == "$prefix" ]] || { echo "Lean prefix mismatch" >&2; exit 2; }
search_path="$prefix/bin:$PATH"
unit="palomar-eight-$(basename -- "$run" | tr -cd '[:alnum:]').service"

{
  printf 'project_head=%s\n' "$(git rev-parse HEAD)"
  printf 'project_branch=%s\n' "$(git branch --show-current)"
  printf 'memory_high=%s\nmemory_max=%s\nmemory_swap_max=%s\n' \
    "$memory_high" "$memory_max" "$memory_swap"
  printf 'physical_headroom_bytes=%s\navailable_reserve_bytes=%s\n' \
    "$physical_headroom" "$available_reserve"
  printf 'cpu_list=%s\nlean_num_threads=1\nfailcomp_style_jobs=1\n' "$cpu_list"
  printf 'deadline_seconds=%s\ntermination_grace_seconds=30\n' "$deadline"
  printf 'pressure_full_avg10_threshold=80\npressure_consecutive_seconds=60\n'
  printf 'started_at=%s\ncommand=' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf '%q ' "$@"
  printf '\n'
} >"$run/command.txt"
{
  printf 'unit=%s\nsupervisor=%s\n' "$unit" "$supervisor"
  printf 'supervisor_sha256=%s\n' "$(sha256sum "$supervisor" | cut -d' ' -f1)"
  printf 'lean_prefix=%s\n' "$prefix"
  printf 'lake_sha256=%s\nlean_sha256=%s\n' \
    "$(sha256sum "$prefix/bin/lake" | cut -d' ' -f1)" \
    "$(sha256sum "$prefix/bin/lean" | cut -d' ' -f1)"
} >"$run/unit.env"

set +e
systemd-run --user --unit="$unit" --wait --collect --quiet \
  --property=Delegate=yes --property=KillMode=control-group \
  --property=TasksMax=infinity --property=RuntimeMaxSec="$((deadline + 60))s" \
  --property=TimeoutStopSec=45s \
  --property="StandardOutput=append:$run/systemd.log" \
  --property="StandardError=append:$run/workload.log" \
  /usr/bin/python3 "$supervisor" --parent self --collect \
    --limit memory.oom.group=1 --limit "memory.swap.max=$swap_bytes" \
    --limit "memory.high=$high_bytes" --limit "memory.max=$max_bytes" \
    --limit "pids.max=$comparator_tasks_max" --deadline "$deadline" --grace 30 \
    --pressure-full-avg10 80 --pressure-consecutive-seconds 60 \
    --pressure-sample-seconds 5 --pressure-log "$run/pressure-guard.jsonl" \
    --telemetry-sample-seconds 5 --telemetry-log "$run/supervisor-telemetry.jsonl" \
    --cwd "$workload_dir" --status "$run/cgroup-status.json" \
    --stdout "$run/workload.log" \
    --setenv "PATH=$search_path" --setenv "HOME=$HOME" \
    --setenv "TMPDIR=$repository_root/.codex-work/tmp" \
    --setenv LEAN_NUM_THREADS=1 --setenv FAILCOMP_STYLE_JOBS=1 \
    --setenv GIT_TERMINAL_PROMPT=0 --setenv PYTHONDONTWRITEBYTECODE=1 \
    --setenv LANG=C.UTF-8 --setenv LC_ALL=C.UTF-8 -- \
    /usr/bin/taskset -c "$cpu_list" /usr/bin/bash "$repository_root/scripts/verify-palomar.sh" \
      --internal-cgroup-record-and-exec "$run" "$high_bytes" "$max_bytes" \
      "$swap_bytes" "$cpu_list" "$@" >>"$run/systemd.log" 2>&1
systemd_rc=$?
set -e

printf '%s\n' "$systemd_rc" >"$run/systemd-run.exit"
printf 'finished_at=%s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)" >"$run/finished.env"
exit "$systemd_rc"
