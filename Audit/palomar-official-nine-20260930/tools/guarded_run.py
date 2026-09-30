#!/usr/bin/env python3
"""Run one owned verifier process group with fail-closed host safeguards."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import time


CGROUP_ROOT = Path("/sys/fs/cgroup")


def mem_available() -> int:
    for line in Path("/proc/meminfo").read_text(encoding="ascii").splitlines():
        if line.startswith("MemAvailable:"):
            return int(line.split()[1]) * 1024
    raise RuntimeError("MemAvailable is unavailable")


def full_avg10() -> float:
    for line in Path("/proc/pressure/memory").read_text(encoding="ascii").splitlines():
        if line.startswith("full "):
            for field in line.split()[1:]:
                name, value = field.split("=", 1)
                if name == "avg10":
                    return float(value)
    raise RuntimeError("full memory PSI avg10 is unavailable")


def palomar_cgroups() -> set[Path]:
    base = CGROUP_ROOT / "user.slice" / f"user-{os.getuid()}.slice"
    if not base.is_dir():
        return set()
    return {
        path
        for path in base.rglob("palomar-*")
        if path.is_dir() and len(path.name) == len("palomar-") + 24
    }


def process_snapshot(pgid: int) -> list[dict[str, object]]:
    records: list[dict[str, object]] = []
    for proc in Path("/proc").iterdir():
        if not proc.name.isdigit():
            continue
        try:
            stat = (proc / "stat").read_text(encoding="ascii").split()
            process_group = int(stat[4])
            cgroup = (proc / "cgroup").read_text(encoding="ascii").strip()
            if process_group != pgid and "/palomar-" not in cgroup:
                continue
            status = (proc / "status").read_text(encoding="ascii")
            affinity = next(
                line.split(":", 1)[1].strip()
                for line in status.splitlines()
                if line.startswith("Cpus_allowed_list:")
            )
            command = (proc / "cmdline").read_bytes().replace(b"\0", b" ").decode(
                "utf-8", errors="replace"
            )
            records.append({
                "pid": int(proc.name),
                "ppid": int(stat[3]),
                "pgid": process_group,
                "affinity": affinity,
                "cgroup": cgroup,
                "command": command[:1000],
            })
        except (FileNotFoundError, PermissionError, StopIteration, ValueError):
            continue
    return records


def kill_owned_cgroups(before: set[Path]) -> list[str]:
    killed: list[str] = []
    for path in sorted(palomar_cgroups() - before):
        control = path / "cgroup.kill"
        try:
            control.write_text("1", encoding="ascii")
            killed.append(str(path))
        except FileNotFoundError:
            continue
        except OSError as error:
            killed.append(f"ERROR {path}: {error}")
    return killed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--job-started-at", type=float, required=True)
    parser.add_argument("--budget-seconds", type=int, default=19800)
    parser.add_argument("--minimum-available-bytes", type=int, default=2 * 1024**3)
    parser.add_argument("--pressure-threshold", type=float, default=80.0)
    parser.add_argument("--pressure-seconds", type=int, default=60)
    parser.add_argument("--sample-seconds", type=int, default=5)
    parser.add_argument("--grace-seconds", type=int, default=30)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a command is required after --")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    before = palomar_cgroups()
    (args.output_dir / "cgroups-before.json").write_text(
        json.dumps(sorted(map(str, before)), indent=2) + "\n", encoding="utf-8"
    )
    started_wall = time.time()
    started_mono = time.monotonic()
    stdout = (args.output_dir / "execute.stdout.log").open("wb")
    stderr = (args.output_dir / "execute.stderr.log").open("wb")
    proc = subprocess.Popen(
        command,
        cwd=Path.cwd(),
        stdin=subprocess.DEVNULL,
        stdout=stdout,
        stderr=stderr,
        start_new_session=True,
    )
    stop_reason: str | None = None
    monitor_error: str | None = None
    pressure_since: float | None = None
    peak_pressure = 0.0
    minimum_available = 2**63 - 1
    samples = 0
    telemetry = (args.output_dir / "host-telemetry.ndjson").open("w", encoding="utf-8")
    try:
        while proc.poll() is None:
            now_wall = time.time()
            try:
                available = mem_available()
                pressure = full_avg10()
                processes = process_snapshot(proc.pid)
            except Exception as error:  # fail closed if the monitor loses its inputs
                monitor_error = f"{type(error).__name__}: {error}"
                stop_reason = "host-monitor-failure"
                break
            samples += 1
            minimum_available = min(minimum_available, available)
            peak_pressure = max(peak_pressure, pressure)
            if pressure >= args.pressure_threshold:
                pressure_since = pressure_since or now_wall
            else:
                pressure_since = None
            record = {
                "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now_wall)),
                "elapsed_seconds": round(time.monotonic() - started_mono, 3),
                "mem_available_bytes": available,
                "host_full_memory_psi_avg10": pressure,
                "pressure_above_seconds": 0 if pressure_since is None else round(now_wall - pressure_since, 3),
                "processes": processes,
                "owned_cgroups": sorted(map(str, palomar_cgroups() - before)),
            }
            telemetry.write(json.dumps(record, sort_keys=True) + "\n")
            telemetry.flush()
            if available < args.minimum_available_bytes:
                stop_reason = "host-memory-reserve"
                break
            if pressure_since is not None and now_wall - pressure_since >= args.pressure_seconds:
                stop_reason = "host-pressure"
                break
            if now_wall - args.job_started_at >= args.budget_seconds:
                stop_reason = "job-budget"
                break
            time.sleep(args.sample_seconds)
    finally:
        telemetry.close()

    killed_cgroups: list[str] = []
    cleanup_started = time.monotonic()
    if proc.poll() is None:
        try:
            os.killpg(proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
        if stop_reason in {"host-memory-reserve", "host-monitor-failure"}:
            killed_cgroups.extend(kill_owned_cgroups(before))
        deadline = time.monotonic() + args.grace_seconds
        while proc.poll() is None and time.monotonic() < deadline:
            time.sleep(0.25)
        if proc.poll() is None:
            killed_cgroups.extend(kill_owned_cgroups(before))
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
    returncode = proc.wait()
    stdout.close()
    stderr.close()
    cleanup_deadline = time.monotonic() + args.grace_seconds
    remaining = palomar_cgroups() - before
    while remaining and time.monotonic() < cleanup_deadline:
        time.sleep(0.25)
        remaining = palomar_cgroups() - before
    if remaining:
        killed_cgroups.extend(kill_owned_cgroups(before))
        time.sleep(0.25)
        remaining = palomar_cgroups() - before
    result = {
        "command": command,
        "started_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(started_wall)),
        "job_started_at_epoch": args.job_started_at,
        "elapsed_seconds": round(time.monotonic() - started_mono, 3),
        "cleanup_seconds": round(time.monotonic() - cleanup_started, 3),
        "exit_status": returncode,
        "stop_reason": stop_reason,
        "monitor_error": monitor_error,
        "samples": samples,
        "minimum_mem_available_bytes": minimum_available if samples else None,
        "peak_host_full_memory_psi_avg10": peak_pressure,
        "minimum_available_guard_bytes": args.minimum_available_bytes,
        "pressure_threshold": args.pressure_threshold,
        "pressure_consecutive_seconds": args.pressure_seconds,
        "budget_seconds": args.budget_seconds,
        "killed_cgroups": killed_cgroups,
        "remaining_owned_cgroups": sorted(map(str, remaining)),
    }
    (args.output_dir / "guard-result.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return returncode


if __name__ == "__main__":
    raise SystemExit(main())
