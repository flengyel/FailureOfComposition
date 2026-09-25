#!/usr/bin/env bash
# Reproducible local checks for the Palomar Challenge/Solution pair.
set -euo pipefail

script_dir=$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repository_root=$(CDPATH= cd -- "$script_dir/.." && pwd)
lean_root="$repository_root/Lean"
palomar_dir="$lean_root/FailureOfComposition/Palomar"
work_root="$repository_root/.codex-work/palomar"
expected_toolchain=leanprover/lean4:v4.35.0-rc2
expected_mathlib=065356127b1dc0016f66b7283ce0ce2c4055aa55
expected_foundation=e72cfe981aa65166f37fa4e2584f4806bc48d72f
expected_policy=792c7c0b9e798bd02719e795ef11fa2b5929e067
expected_submission=a59f25bd8a66bf6faf3a4f4260d412989c0185ea
expected_template=cb5c79b69a740d2dc299071fc35994627050d77a
gnu_time=/usr/bin/time
if [[ ! -x $gnu_time ]]; then
  gnu_time="$repository_root/.codex-work/tmp/gnu-time/usr/bin/time"
fi
launcher_checks="$script_dir/palomar_launcher_checks.py"

# Local Comparator containment. memory.max protects WSL RAM as an aggregate
# process-tree ceiling; memory.swap.max is a separate ceiling, not extra RAM.
# On this 16 GiB WSL instance these defaults leave more than 4 GiB of physical
# memory outside the Comparator cgroup. The host must provide the cgroup's swap
# allowance plus a separate 2 GiB reserve before a real retry is permitted.
comparator_memory_high=${PALOMAR_COMPARATOR_MEMORY_HIGH:-10G}
comparator_memory_max=${PALOMAR_COMPARATOR_MEMORY_MAX:-11G}
comparator_swap_max=${PALOMAR_COMPARATOR_SWAP_MAX:-20G}
comparator_cpu_list=${PALOMAR_COMPARATOR_CPUS:-0}
system_memory_headroom_bytes=${PALOMAR_SYSTEM_MEMORY_HEADROOM_BYTES:-4294967296}
system_memory_available_reserve_bytes=${PALOMAR_SYSTEM_MEMORY_AVAILABLE_RESERVE_BYTES:-1073741824}
system_swap_headroom_bytes=${PALOMAR_SYSTEM_SWAP_HEADROOM_BYTES:-2147483648}
comparator_tasks_max=${PALOMAR_COMPARATOR_TASKS_MAX:-512}
comparator_deadline_seconds=${PALOMAR_COMPARATOR_DEADLINE_SECONDS:-19800}
precheck_memory_high=${PALOMAR_PRECHECK_MEMORY_HIGH:-12G}
precheck_memory_max=${PALOMAR_PRECHECK_MEMORY_MAX:-12800M}
precheck_swap_max=${PALOMAR_PRECHECK_SWAP_MAX:-12G}
precheck_memory_headroom_bytes=${PALOMAR_PRECHECK_MEMORY_HEADROOM_BYTES:-2147483648}
precheck_memory_available_reserve_bytes=${PALOMAR_PRECHECK_MEMORY_AVAILABLE_RESERVE_BYTES:-1073741824}
precheck_swap_headroom_bytes=${PALOMAR_PRECHECK_SWAP_HEADROOM_BYTES:-2147483648}
precheck_deadline_seconds=${PALOMAR_PRECHECK_DEADLINE_SECONDS:-14400}
cgroup_supervisor="$work_root/upstream/PalomarSubmission/scripts/supervise_cgroup.py"
delegated_user_cgroup=

usage() {
  cat <<'EOF'
usage: scripts/verify-palomar.sh MODE [arguments]

Modes:
  --check-environment
      Read-only pin, tool, configuration, and Challenge-import inspection.
  --containment-test
      Run a small, reduced-resource process-tree diagnostic. This tests cgroup
      limits and CPU-affinity inheritance only; it is not Comparator or an
      official Palomar verification run.
  --capacity-test
      Record snapshot-only admission checks for both the contained preparatory
      phase and Comparator phase. This launches no Lean workload and reserves
      no resources against jobs started after the snapshots.
  --local-comparator
      Run the paired project check, then the toolchain's real Comparator with
      Lean's kernel and the bundled NanoDa and con-ron kernels. Evidence is
      retained below .codex-work/palomar/runs/.
  --resume-local-comparator PREVIOUS_RUN
      Retry only the interrupted Comparator stage after confirming that
      PREVIOUS_RUN contains a completed contained paired check whose recorded
      input manifest exactly matches current source, configuration, toolchain,
      and resolved dependencies. Historical runs without that manifest are
      reported as stale and are never relabeled. A new evidence directory is
      always used.
  --full-verifier EVENT_JSON RUN_DIR
      Run prepare, capacity, and execute from the pinned PalomarSubmission
      checkout already present at .codex-work/palomar/upstream/. This mode
      requires an isolated Python environment containing requirements.txt,
      Licensee/Bundler, a verifier-built bubblewrap 0.12.0 named by
      PALOMAR_BWRAP, and delegated cgroup-v2 memory/pids controllers. It uses
      palomar-standard-v1 and the explicit 19,800-second execution budget.

The full mode verifies a public immutable commit named by EVENT_JSON. It does
not submit, register, review, or upload anything.

Local Comparator defaults: one inherited CPU; MemoryHigh=10G; MemoryMax=11G;
MemorySwapMax=20G. The complete Comparator process tree is supervised in one
delegated cgroup. The launcher refuses a real run unless host RAM and swap leave
the separate headroom documented above. The preparatory paired check is also
contained, with phase-specific defaults MemoryHigh=12G, MemoryMax=12800M
(12.5 GiB), and MemorySwapMax=12G. Capacity checks are snapshots, not
reservations against unrelated workloads started later.
EOF
}

fail() {
  echo "error: $*" >&2
  exit 1
}

require_command() {
  command -v "$1" >/dev/null 2>&1 || fail "$1 is required"
}

manifest_revision() {
  local package=$1
  python3 - "$lean_root/lake-manifest.json" "$package" <<'PY'
import json
import pathlib
import sys

manifest = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
for package in manifest.get("packages", []):
    if package.get("name") == sys.argv[2]:
        print(package.get("rev", ""))
        raise SystemExit(0)
raise SystemExit(1)
PY
}

check_pins() {
  local actual
  actual=$(tr -d '\r\n' <"$lean_root/lean-toolchain")
  [[ $actual == "$expected_toolchain" ]] || fail "unexpected toolchain: $actual"
  actual=$(manifest_revision mathlib)
  [[ $actual == "$expected_mathlib" ]] || fail "unexpected Mathlib revision: $actual"
  actual=$(manifest_revision Foundation)
  [[ $actual == "$expected_foundation" ]] || fail "unexpected Foundation revision: $actual"
}

check_upstream() {
  local name expected directory actual
  while read -r name expected; do
    directory="$work_root/upstream/$name"
    [[ -d $directory/.git ]] || fail "missing pinned upstream checkout: $directory"
    actual=$(git -C "$directory" rev-parse HEAD)
    [[ $actual == "$expected" ]] || fail "$name is at $actual, expected $expected"
  done <<EOF
PalomarPolicy $expected_policy
PalomarSubmission $expected_submission
PalomarTemplate $expected_template
EOF
}

check_tools() {
  local prefix tool
  require_command bwrap
  require_command git
  require_command numfmt
  require_command python3
  require_command systemctl
  require_command systemd-run
  require_command taskset
  require_command timeout
  [[ -x $gnu_time ]] || fail "GNU time is required"
  [[ -x $launcher_checks ]] || fail "missing launcher evidence helper: $launcher_checks"
  prefix=$(cd "$lean_root" && lean --print-prefix)
  for tool in lake lean leanexport leanchecker nanoda_bin con-ron; do
    [[ -x $prefix/bin/$tool ]] || fail "$expected_toolchain does not bundle $tool"
  done
  [[ $(bwrap --version) == "bubblewrap 0.12.0" ]] ||
    fail "local bwrap is not version 0.12.0"
}

validate_config() {
  python3 - "$palomar_dir/comparator.json" <<'PY'
import json
import pathlib
import sys

path = pathlib.Path(sys.argv[1])
value = json.loads(path.read_text(encoding="utf-8"))
expected = [
    "FailureOfComposition.Palomar.obstruction_four_properties",
    "FailureOfComposition.Palomar.no_quotient_composition_productive",
    "FailureOfComposition.Palomar.no_quotient_composition_godel",
    "FailureOfComposition.Palomar.pi_one_characterization",
    "FailureOfComposition.Palomar.generated_congruence_classification",
    "FailureOfComposition.Palomar.weak_totality_counterexample",
    "FailureOfComposition.Palomar.range_counterexample_godel",
    "FailureOfComposition.Palomar.range_counterexample_productive",
    "FailureOfComposition.Palomar.generated_quotient_partial_recursive",
]
if value.get("theorem_names") != expected:
    raise SystemExit("comparator.json does not select the nine declarations in order")
if value.get("definition_names", []) != []:
    raise SystemExit("comparator.json must not declare definition holes")
if set(value.get("permitted_axioms", [])) != {
    "propext", "Quot.sound", "Classical.choice"
}:
    raise SystemExit("comparator.json has the wrong permitted-axiom set")
if "external_kernels" in value:
    raise SystemExit("submitted comparator.json must not contain external_kernels")
print("PASS comparator configuration selects all nine declarations and no definition holes")
PY
}

inspect_challenge() {
  local bytes lines
  bytes=$(wc -c <"$palomar_dir/Challenge.lean")
  lines=$(wc -l <"$palomar_dir/Challenge.lean")
  (( bytes <= 102400 )) || fail "Challenge exceeds 100 KiB"
  (( lines <= 1000 )) || fail "Challenge exceeds 1,000 lines"
  echo "Challenge bytes=$bytes lines=$lines"
  (
    cd "$lean_root"
    lake env lean --deps-json FailureOfComposition/Palomar/Challenge.lean
    lake env lean --src-deps FailureOfComposition/Palomar/Challenge.lean
  )
}

check_environment() {
  mkdir -p "$work_root"
  check_environment_static
  inspect_challenge
  echo "PASS Palomar tooling and pins"
}

check_environment_static() {
  mkdir -p "$work_root"
  check_pins
  check_upstream
  check_tools
  validate_config
}

new_run_directory() {
  local stamp directory
  stamp=$(date -u +%Y%m%dT%H%M%SZ)
  directory="$work_root/runs/${stamp}-$$"
  mkdir -p "$directory"
  printf '%s\n' "$directory"
}

write_protected_config() {
  local destination=$1 prefix
  prefix=$(cd "$lean_root" && lean --print-prefix)
  python3 - "$palomar_dir/comparator.json" "$destination" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
value = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
if "external_kernels" in value:
    raise SystemExit("submitted comparator configuration contains external_kernels")
value.pop("enable_nanoda", None)
value["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(
    json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8"
)
PY
  chmod 0444 "$destination"
}

size_bytes() {
  [[ $1 =~ ^[0-9]+[KMGT]?$ ]] || fail "unsupported resource size: $1"
  numfmt --from=iec "$1"
}

check_no_checker_processes() {
  local active
  active=$(ps -eo pid=,ppid=,comm=,args= | awk '
    $3 ~ /^(lean|lake|leanexport|leanchecker|nanoda_bin|con-ron)$/ { print }
  ')
  [[ -z $active ]] || fail "refusing overlapping Lean/Comparator processes:\n$active"
}

check_delegated_cgroup() {
  local mount_options user_cgroup controllers controller
  [[ -x $cgroup_supervisor ]] || fail "missing pinned cgroup supervisor: $cgroup_supervisor"
  systemctl --user is-system-running >/dev/null 2>&1 ||
    fail "the ordinary WSL user systemd manager is unavailable"
  mount_options=$(findmnt -no OPTIONS /sys/fs/cgroup)
  [[ ,$mount_options, == *,rw,* ]] ||
    fail "cgroup v2 is read-only; run this mode from an ordinary WSL terminal, not the Codex sandbox"
  user_cgroup=$(systemctl --user show -p ControlGroup --value)
  [[ -n $user_cgroup && -r /sys/fs/cgroup$user_cgroup/cgroup.controllers ]] ||
    fail "cannot resolve the delegated user cgroup"
  delegated_user_cgroup="/sys/fs/cgroup$user_cgroup"
  controllers=$(<"/sys/fs/cgroup$user_cgroup/cgroup.controllers")
  for controller in cpu memory pids; do
    [[ " $controllers " == *" $controller "* ]] ||
      fail "the delegated user cgroup lacks the $controller controller"
  done
}

check_phase_capacity() {
  [[ $# -eq 7 ]] ||
    fail "check_phase_capacity needs phase, limits, headroom, available reserve, and output"
  local phase=$1 maximum=$2 swap=$3 memory_headroom=$4 memory_reserve=$5
  local swap_headroom=$6 output=$7
  local maximum_bytes swap_bytes
  [[ -n $delegated_user_cgroup ]] || fail "delegated user cgroup was not resolved"
  maximum_bytes=$(size_bytes "$maximum")
  swap_bytes=$(size_bytes "$swap")
  python3 "$launcher_checks" capacity \
    --repository "$repository_root" --cgroup "$delegated_user_cgroup" \
    --phase "$phase" --memory-max "$maximum_bytes" --swap-max "$swap_bytes" \
    --memory-headroom "$memory_headroom" --memory-available-reserve "$memory_reserve" \
    --swap-headroom "$swap_headroom" \
    --output "$output"
}

internal_cgroup_record_and_exec() {
  [[ $# -ge 6 ]] || fail "internal cgroup launcher received too few arguments"
  local run=$1 expected_high=$2 expected_max=$3 expected_swap=$4 expected_cpus=$5
  local self relative leaf limits temporary actual_high actual_max actual_swap actual_oom
  shift 5
  self=$(< /proc/self/cgroup)
  [[ $self == 0::* ]] || fail "internal workload is not in cgroup v2"
  relative=${self#0::}
  leaf="/sys/fs/cgroup$relative"
  limits=$(dirname -- "$leaf")
  [[ $limits == /sys/fs/cgroup/*/palomar-* ]] ||
    fail "unexpected supervised cgroup path: $limits"
  actual_high=$(<"$limits/memory.high")
  actual_max=$(<"$limits/memory.max")
  actual_swap=$(<"$limits/memory.swap.max")
  actual_oom=$(<"$limits/memory.oom.group")
  [[ $actual_high == "$expected_high" ]] || fail "memory.high was not applied"
  [[ $actual_max == "$expected_max" ]] || fail "memory.max was not applied"
  [[ $actual_swap == "$expected_swap" ]] || fail "memory.swap.max was not applied"
  [[ $actual_oom == 1 ]] || fail "memory.oom.group was not applied"
  [[ $(nproc) == 1 ]] || fail "Comparator payload does not see exactly one available CPU"
  temporary="$run/containment.env.$$"
  {
    printf 'classification=aggregate_process_tree_containment\n'
    printf 'cgroup_leaf=%s\n' "$leaf"
    printf 'cgroup_limits=%s\n' "$limits"
    printf 'memory_high=%s\n' "$actual_high"
    printf 'memory_max=%s\n' "$actual_max"
    printf 'memory_swap_max=%s\n' "$actual_swap"
    printf 'memory_oom_group=%s\n' "$actual_oom"
    printf 'cpu_request=%s\n' "$expected_cpus"
    printf 'nproc=%s\n' "$(nproc)"
    awk '/^Cpus_allowed_list:/ { print "cpus_allowed_list=" $2 }' /proc/self/status
    printf 'payload_pid=%s\n' "$$"
  } >"$temporary"
  mv "$temporary" "$run/containment.env"
  exec "$@"
}

internal_containment_probe() {
  [[ $# -eq 1 ]] || fail "internal containment probe needs its evidence directory"
  local run=$1
  {
    printf 'role=parent\n'
    printf 'pid=%s\n' "$$"
    cat /proc/self/cgroup
  } >"$run/probe-parent.txt"
  (
    {
      printf 'role=child\n'
      printf 'pid=%s\n' "$BASHPID"
      cat /proc/self/cgroup
    } >"$run/probe-child.txt"
    python3 - "$run/probe-grandchild.txt" <<'PY'
import os
import pathlib
import sys
import time

path = pathlib.Path(sys.argv[1])
payload = bytearray(32 * 1024 * 1024)
for offset in range(0, len(payload), 4096):
    payload[offset] = 1
path.write_text(
    "role=grandchild\n"
    f"pid={os.getpid()}\n"
    + pathlib.Path("/proc/self/cgroup").read_text(encoding="ascii")
    + next(
        line for line in pathlib.Path("/proc/self/status").read_text().splitlines()
        if line.startswith("Cpus_allowed_list:")
    )
    + "\n",
    encoding="ascii",
)
time.sleep(0.25)
PY
  ) &
  wait "$!"
}

supervisor_field() {
  python3 - "$1" "$2" <<'PY'
import json
import pathlib
import sys

value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
field = value.get(sys.argv[2], "")
print(field if isinstance(field, (str, int, float)) else "")
PY
}

monitor_supervisor() {
  local status_file=$1 output=$2 state cgroup pids
  local attempts=0
  while (( attempts < 240 )); do
    if [[ -s $status_file ]]; then
      state=$(supervisor_field "$status_file" state 2>/dev/null || true)
      [[ $state == started ]] && break
      [[ $state == finished || $state == failed ]] && return 0
    fi
    sleep 0.25
    ((attempts += 1))
  done
  [[ ${state:-} == started ]] || return 0
  cgroup=$(supervisor_field "$status_file" cgroup)
  [[ $cgroup == /sys/fs/cgroup/* ]] || return 0
  while [[ -d $cgroup ]]; do
    state=$(supervisor_field "$status_file" state 2>/dev/null || true)
    {
      date -Ins
      free -b
      swapon --show --bytes
      for name in memory.current memory.peak memory.high memory.max \
          memory.swap.current memory.swap.peak memory.swap.max memory.events \
          memory.pressure pids.current pids.peak pids.max; do
        if [[ -r $cgroup/$name ]]; then
          printf '%s=' "$name"
          cat "$cgroup/$name"
        fi
      done
      pids=$(find "$cgroup" -type f -name cgroup.procs -exec cat {} + 2>/dev/null |
        sort -nu | tr '\n' ' ')
      if [[ -n $pids ]]; then
        ps -e -o pid=,ppid=,nlwp=,psr=,rss=,vsz=,stat=,comm=,args= | \
          awk -v wanted=" $pids " 'index(wanted, " " $1 " ") { print }'
      fi
    } >>"$output" 2>&1
    [[ $state == started ]] || break
    sleep 5
  done
}

run_supervised() {
  [[ $# -ge 9 ]] || fail "run_supervised received too few arguments"
  local run=$1 output=$2 unit_log=$3 high=$4 maximum=$5 swap=$6 deadline=$7 cwd=$8
  local high_bytes max_bytes swap_bytes unit monitor systemd_rc prefix search_path
  shift 8
  mkdir -p "$run"
  high_bytes=$(size_bytes "$high")
  max_bytes=$(size_bytes "$maximum")
  swap_bytes=$(size_bytes "$swap")
  unit="palomar-local-$(basename -- "$run" | tr -cd '[:alnum:]').service"
  prefix=$(cd "$lean_root" && lean --print-prefix)
  search_path="$prefix/bin:$PATH"
  {
    printf 'unit=%s\n' "$unit"
    printf 'supervisor=%s\n' "$cgroup_supervisor"
    printf 'supervisor_sha256=%s\n' "$(sha256sum "$cgroup_supervisor" | cut -d' ' -f1)"
  } >"$run/unit.env"
  monitor_supervisor "$run/cgroup-status.json" "$run/processes.log" &
  monitor=$!
  set +e
  systemd-run --user --unit="$unit" --wait --collect --quiet \
    --property=Delegate=yes --property=KillMode=control-group \
    --property=TasksMax=infinity --property=RuntimeMaxSec="$((deadline + 60))s" \
    --property=TimeoutStopSec=45s --property="StandardOutput=append:$unit_log" \
    --property="StandardError=append:$output" \
    /usr/bin/python3 "$cgroup_supervisor" --parent self --collect \
      --limit memory.oom.group=1 --limit "memory.swap.max=$swap_bytes" \
      --limit "memory.high=$high_bytes" --limit "memory.max=$max_bytes" \
      --limit "pids.max=$comparator_tasks_max" --deadline "$deadline" --grace 30 \
      --cwd "$cwd" --status "$run/cgroup-status.json" --stdout "$output" \
      --setenv "PATH=$search_path" --setenv "HOME=$HOME" \
      --setenv "TMPDIR=$repository_root/.codex-work/tmp" \
      --setenv LEAN_NUM_THREADS=1 --setenv FAILCOMP_STYLE_JOBS=1 \
      --setenv GIT_TERMINAL_PROMPT=0 --setenv PYTHONDONTWRITEBYTECODE=1 \
      --setenv LANG=C.UTF-8 --setenv LC_ALL=C.UTF-8 -- \
      /usr/bin/taskset -c "$comparator_cpu_list" /usr/bin/bash "$script_dir/verify-palomar.sh" \
        --internal-cgroup-record-and-exec "$run" "$high_bytes" "$max_bytes" "$swap_bytes" \
        "$comparator_cpu_list" "$@" >>"$unit_log" 2>&1
  systemd_rc=$?
  wait "$monitor" 2>/dev/null
  set -e
  printf '%s\n' "$systemd_rc" >"$run/systemd-run.exit"
}

finalize_comparator_run() {
  local run=$1 resume_of=$2
  python3 "$launcher_checks" finalize --kind comparator --run "$run" \
    --destination status.env --verification-kind local_comparator \
    --resume-of "$resume_of" --memory-high "$(size_bytes "$comparator_memory_high")" \
    --memory-max "$(size_bytes "$comparator_memory_max")" \
    --memory-swap-max "$(size_bytes "$comparator_swap_max")" \
    --cpu-list "$comparator_cpu_list" --output-name comparator.log
}

finalize_precheck_run() {
  local run=$1
  python3 "$launcher_checks" finalize --kind precheck --run "$run" \
    --destination precheck-status.env --verification-kind local_paired_precheck \
    --memory-high "$(size_bytes "$precheck_memory_high")" \
    --memory-max "$(size_bytes "$precheck_memory_max")" \
    --memory-swap-max "$(size_bytes "$precheck_swap_max")" \
    --cpu-list "$comparator_cpu_list" --output-name paired-check.log
}

write_precheck_manifest() {
  local destination=$1 prefix
  prefix=$(cd "$lean_root" && lean --print-prefix)
  python3 "$launcher_checks" precheck-manifest --repository "$repository_root" \
    --lean-prefix "$prefix" --output "$destination"
}

compare_precheck_manifests() {
  local expected=$1 actual=$2 report=$3
  python3 "$launcher_checks" compare-manifests --expected "$expected" \
    --actual "$actual" --report "$report"
}

run_precheck_phase() {
  [[ $# -ge 2 ]] || fail "run_precheck_phase needs an evidence directory and command"
  local run=$1
  shift
  run_supervised "$run" "$run/paired-check.log" "$run/systemd.log" \
    "$precheck_memory_high" "$precheck_memory_max" "$precheck_swap_max" \
    "$precheck_deadline_seconds" "$repository_root" "$@"
}

internal_precheck_payload() {
  [[ $# -eq 0 ]] || fail "internal precheck payload takes no arguments"
  inspect_challenge
  python3 "$palomar_dir/check_draft.py"
}

capacity_test() {
  local run
  check_pins
  check_upstream
  check_tools
  check_delegated_cgroup
  check_no_checker_processes
  run="$work_root/capacity-tests/$(date -u +%Y%m%dT%H%M%SZ)-$$"
  mkdir -p "$run"
  check_phase_capacity precheck "$precheck_memory_max" "$precheck_swap_max" \
    "$precheck_memory_headroom_bytes" "$precheck_memory_available_reserve_bytes" \
    "$precheck_swap_headroom_bytes" \
    "$run/precheck-capacity.json"
  check_phase_capacity comparator "$comparator_memory_max" "$comparator_swap_max" \
    "$system_memory_headroom_bytes" "$system_memory_available_reserve_bytes" \
    "$system_swap_headroom_bytes" \
    "$run/comparator-capacity.json"
  echo "PASS snapshot-only phase capacity checks: $run"
}

containment_test() {
  local run high=64M maximum=96M swap=0 status_rc
  check_pins
  check_upstream
  check_tools
  check_delegated_cgroup
  check_no_checker_processes
  run="$work_root/containment-tests/$(date -u +%Y%m%dT%H%M%SZ)-$$"
  mkdir -p "$run"
  {
    printf 'classification=reduced_resource_containment_diagnostic\n'
    printf 'official_palomar_verification=false\n'
    printf 'comparator_run=false\n'
    printf 'memory_high=%s\n' "$high"
    printf 'memory_max=%s\n' "$maximum"
    printf 'memory_swap_max=%s\n' "$swap"
    printf 'cpu_list=%s\n' "$comparator_cpu_list"
  } >"$run/diagnostic.env"
  run_supervised "$run" "$run/probe.log" "$run/systemd.log" "$high" "$maximum" "$swap" 60 \
    "$repository_root" \
    /usr/bin/bash "$script_dir/verify-palomar.sh" --internal-containment-probe "$run"
  set +e
  python3 - "$run" "$(size_bytes "$high")" "$(size_bytes "$maximum")" \
    "$(size_bytes "$swap")" "$comparator_cpu_list" <<'PY'
import json
import pathlib
import sys

run = pathlib.Path(sys.argv[1])
expected_high, expected_max, expected_swap, expected_cpu = sys.argv[2:]
status = json.loads((run / "cgroup-status.json").read_text(encoding="utf-8"))
containment = dict(
    line.split("=", 1)
    for line in (run / "containment.env").read_text(encoding="utf-8").splitlines()
    if "=" in line
)
expected = containment["cgroup_leaf"].removeprefix("/sys/fs/cgroup")
for name in ("probe-parent.txt", "probe-child.txt", "probe-grandchild.txt"):
    text = (run / name).read_text(encoding="ascii")
    if f"0::{expected}" not in text:
        raise SystemExit(f"{name} escaped the supervised cgroup")
if containment.get("memory_oom_group") != "1":
    raise SystemExit("memory.oom.group was not one")
for name, expected_value in {
    "memory_high": expected_high,
    "memory_max": expected_max,
    "memory_swap_max": expected_swap,
    "cpu_request": expected_cpu,
    "cpus_allowed_list": expected_cpu,
    "nproc": "1",
}.items():
    if containment.get(name) != expected_value:
        raise SystemExit(f"unexpected containment {name}: {containment.get(name)!r}")
try:
    systemd_exit = int((run / "systemd-run.exit").read_text(encoding="ascii").strip())
except (OSError, ValueError) as error:
    raise SystemExit(f"missing or malformed systemd completion: {error}") from error
if systemd_exit != 0:
    raise SystemExit(f"systemd-run failed with status {systemd_exit}")
events = status.get("memory_events") or {}
required_limits = {
    "memory.oom.group", "memory.swap.max", "memory.high", "memory.max", "pids.max"
}
if status.get("state") != "finished":
    raise SystemExit("bounded diagnostic supervisor did not finish")
if status.get("exit_status") != 0 or status.get("term_signal") is not None:
    raise SystemExit("bounded diagnostic payload did not finish successfully")
for name, expected_value in {
    "deadline_fired": False,
    "liveness_lost": False,
    "placement_ok": True,
    "populated_after_kill": False,
}.items():
    if status.get(name) is not expected_value:
        raise SystemExit(f"unclean supervisor field {name}: {status.get(name)!r}")
for name in ("placement_error", "launch_error"):
    if name not in status or status.get(name) is not None:
        raise SystemExit(f"unclean supervisor field {name}: {status.get(name)!r}")
limits = status.get("limits_applied")
if not isinstance(limits, dict) or any(limits.get(name) is not True for name in required_limits):
    raise SystemExit("one or more required diagnostic limits were not applied")
for name in ("high", "max", "oom", "oom_kill", "oom_group_kill"):
    if type(events.get(name)) is not int or events[name] < 0:
        raise SystemExit(f"missing or malformed memory event {name}")
for name in ("oom", "oom_kill", "oom_group_kill"):
    if events[name]:
        raise SystemExit(f"bounded diagnostic unexpectedly triggered {name}")
pids_events = status.get("pids_events")
if not isinstance(pids_events, dict) or pids_events.get("max") != 0:
    raise SystemExit("bounded diagnostic reached or omitted its pids limit evidence")
peak = int(status.get("memory_peak") or 0)
if not 16 * 1024**2 <= peak <= 96 * 1024**2:
    raise SystemExit(f"unexpected diagnostic memory peak: {peak}")
report = {
    "classification": "reduced_resource_containment_diagnostic",
    "official_palomar_verification": False,
    "comparator_run": False,
    "result": "pass",
    "infrastructure_clean": True,
    "systemd_exit_status": systemd_exit,
    "cgroup_leaf": expected,
    "limits_applied": status.get("limits_applied"),
    "memory_peak_bytes": peak,
    "memory_events": events,
    "nproc": 1,
}
(run / "result.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
print(f"PASS reduced-resource containment diagnostic: {run}")
PY
  status_rc=$?
  set -e
  return "$status_rc"
}

local_comparator() {
  local mode=$1 previous=${2:-} run config command_log comparator_log time_log prefix
  local precheck_manifest precheck_after precheck_run resume_of=none rc
  check_environment_static
  check_delegated_cgroup
  check_no_checker_processes
  run=$(new_run_directory)
  config="$run/protected-comparator.json"
  command_log="$run/commands.log"
  comparator_log="$run/comparator.log"
  time_log="$run/time.log"
  precheck_manifest="$run/precheck-inputs.json"
  precheck_after="$run/precheck-inputs.after.json"
  precheck_run="$run/precheck"
  write_protected_config "$config"
  prefix=$(cd "$lean_root" && lean --print-prefix)
  write_precheck_manifest "$precheck_manifest"

  if [[ $mode == resume ]]; then
    previous=$(readlink -f -- "$previous")
    [[ $previous == "$work_root"/runs/* ]] || fail "resume path is outside Palomar runs"
    if [[ ! -f $previous/precheck-inputs.json ]]; then
      set +e
      compare_precheck_manifests "$previous/precheck-inputs.json" "$precheck_manifest" \
        "$run/precheck-reuse.json"
      set -e
      echo "Comparator evidence: $run"
      fail "resume evidence has no content-bound precheck manifest; use --local-comparator"
    fi
    [[ -f $previous/precheck/precheck-status.env ]] || {
      printf '%s\n' \
        'classification=precheck_reuse' \
        'result=stale' \
        'reason=missing contained precheck status' >"$run/precheck-reuse.env"
      echo "Comparator evidence: $run"
      fail "resume evidence has no contained precheck status; use --local-comparator"
    }
    grep -Fxq 'result=pass' "$previous/precheck/precheck-status.env" ||
      fail "the previous contained precheck did not pass"
    grep -Fxq 'infrastructure_clean=true' "$previous/precheck/precheck-status.env" ||
      fail "the previous precheck infrastructure was not clean"
    grep -Fxq 'computational_success=true' "$previous/precheck/precheck-status.env" ||
      fail "the previous paired check did not succeed"
    compare_precheck_manifests "$previous/precheck-inputs.json" "$precheck_manifest" \
      "$run/precheck-reuse.json" || {
        echo "Comparator evidence: $run"
        fail "resume precheck inputs are stale; use --local-comparator"
      }
    resume_of=$previous
    printf 'Reused content-matched contained precheck from %s\n' "$previous" \
      >"$run/precheck-reused.log"
  else
    check_phase_capacity precheck "$precheck_memory_max" "$precheck_swap_max" \
      "$precheck_memory_headroom_bytes" "$precheck_memory_available_reserve_bytes" \
      "$precheck_swap_headroom_bytes" \
      "$run/precheck-capacity.json"
    run_precheck_phase "$precheck_run" \
      /usr/bin/bash "$script_dir/verify-palomar.sh" --internal-precheck-payload
    set +e
    finalize_precheck_run "$precheck_run"
    rc=$?
    set -e
    if (( rc != 0 )); then
      echo "Precheck evidence: $precheck_run"
      cat "$precheck_run/precheck-status.env"
      return "$rc"
    fi
    write_precheck_manifest "$precheck_after"
    compare_precheck_manifests "$precheck_manifest" "$precheck_after" \
      "$run/precheck-stability.json" || {
        echo "Precheck evidence: $precheck_run"
        fail "precheck inputs changed while the contained check was running"
      }
  fi

  {
    printf 'repository=%s\n' "$(git -C "$repository_root" rev-parse HEAD)"
    printf 'branch=%s\n' "$(git -C "$repository_root" branch --show-current)"
    printf 'toolchain=%s\n' "$expected_toolchain"
    printf 'mathlib=%s\n' "$expected_mathlib"
    printf 'foundation=%s\n' "$expected_foundation"
    printf 'resume_of=%s\n' "$resume_of"
    printf 'verification_kind=local_comparator\n'
    printf 'official_palomar_verification=false\n'
    printf 'submitted_config_sha256=%s\n' "$(sha256sum "$palomar_dir/comparator.json" | cut -d' ' -f1)"
    printf 'protected_config_sha256=%s\n' "$(sha256sum "$config" | cut -d' ' -f1)"
    printf 'memory_high=%s\n' "$comparator_memory_high"
    printf 'memory_max=%s\n' "$comparator_memory_max"
    printf 'memory_swap_max=%s\n' "$comparator_swap_max"
    printf 'cpu_list=%s\n' "$comparator_cpu_list"
    printf 'capacity_snapshot_only=true\n'
    printf 'precheck_input_manifest_sha256=%s\n' \
      "$(sha256sum "$precheck_manifest" | cut -d' ' -f1)"
    printf 'precheck_memory_high=%s\n' "$precheck_memory_high"
    printf 'precheck_memory_max=%s\n' "$precheck_memory_max"
    printf 'precheck_memory_swap_max=%s\n' "$precheck_swap_max"
    if [[ $mode == resume ]]; then
      printf 'precheck=reused content-matched contained paired check from %s\n' "$previous"
    else
      printf 'precheck=contained inspect_challenge and python3 Lean/FailureOfComposition/Palomar/check_draft.py\n'
    fi
    printf 'comparator=cd Lean && %s/bin/lake comparator --config %q\n' "$prefix" "$config"
  } >"$command_log"

  check_no_checker_processes
  check_phase_capacity comparator "$comparator_memory_max" "$comparator_swap_max" \
    "$system_memory_headroom_bytes" "$system_memory_available_reserve_bytes" \
    "$system_swap_headroom_bytes" \
    "$run/comparator-capacity.json"
  run_supervised "$run" "$comparator_log" "$run/systemd.log" \
    "$comparator_memory_high" "$comparator_memory_max" "$comparator_swap_max" \
    "$comparator_deadline_seconds" "$lean_root" "$gnu_time" -v -o "$time_log" \
      /usr/bin/timeout --signal=TERM --kill-after=30s "$comparator_deadline_seconds" \
      "$prefix/bin/lake" comparator --config "$config"
  set +e
  finalize_comparator_run "$run" "$resume_of"
  rc=$?
  set -e
  echo "Comparator evidence: $run"
  cat "$run/status.env"
  return "$rc"
}

full_verifier() {
  [[ $# -eq 2 ]] || fail "--full-verifier requires EVENT_JSON and RUN_DIR"
  local event=$1 run=$2 pipeline output bwrap_path bundle_path
  pipeline="$work_root/upstream/PalomarSubmission"
  output="$run/mechanical-report.json"
  bwrap_path=${PALOMAR_BWRAP:-}
  bundle_path=$(command -v bundle || true)
  [[ -n $bwrap_path && -x $bwrap_path ]] || fail "PALOMAR_BWRAP must name verifier-built bwrap 0.12.0"
  [[ -n $bundle_path ]] || fail "Bundler/Licensee is required"
  [[ -f $event ]] || fail "event file does not exist: $event"
  mkdir -p "$run"
  check_upstream
  export PALOMAR_EXECUTION_PROFILE=palomar-standard-v1
  (
    cd "$pipeline"
    python3 scripts/verify_submission.py prepare --event "$event" --work-dir "$run/work" \
      --output "$output" --licensee "$bundle_path"
    python3 - "$output" <<'PY'
import json, pathlib, sys
value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if value.get("status") != "pending" or value.get("stage") != "prepared":
    raise SystemExit("prepare did not produce status=pending, stage=prepared")
PY
    python3 scripts/verify_submission.py check-capacity --disk-path "$run" --output "$output"
    python3 scripts/verify_submission.py execute --work-dir "$run/work" --output "$output" \
      --bwrap "$bwrap_path" --bwrap-source-tag v0.12.0 \
      --execution-budget-seconds 19800 --workflow-url local-independent-review
  )
  python3 - "$output" <<'PY'
import json, pathlib, sys
value = json.loads(pathlib.Path(sys.argv[1]).read_text(encoding="utf-8"))
if value.get("status") != "pass" or value.get("stage") != "complete":
    raise SystemExit("full verifier did not produce status=pass, stage=complete")
print("PASS complete Palomar mechanical verifier")
PY
}

main() {
  local mode=${1:-}
  case "$mode" in
    --check-environment)
      [[ $# -eq 1 ]] || { usage >&2; return 2; }
      check_environment
      ;;
    --containment-test)
      [[ $# -eq 1 ]] || { usage >&2; return 2; }
      containment_test
      ;;
    --capacity-test)
      [[ $# -eq 1 ]] || { usage >&2; return 2; }
      capacity_test
      ;;
    --local-comparator)
      [[ $# -eq 1 ]] || { usage >&2; return 2; }
      local_comparator fresh
      ;;
    --resume-local-comparator)
      [[ $# -eq 2 ]] || { usage >&2; return 2; }
      local_comparator resume "$2"
      ;;
    --full-verifier)
      shift
      full_verifier "$@"
      ;;
    --internal-cgroup-record-and-exec)
      shift
      internal_cgroup_record_and_exec "$@"
      ;;
    --internal-containment-probe)
      shift
      internal_containment_probe "$@"
      ;;
    --internal-precheck-payload)
      shift
      internal_precheck_payload "$@"
      ;;
    *)
      usage >&2
      return 2
      ;;
  esac
}

if [[ ${BASH_SOURCE[0]} == "$0" ]]; then
  main "$@"
fi
