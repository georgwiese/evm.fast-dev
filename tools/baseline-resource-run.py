#!/usr/bin/env python3
"""Run a command with resource evidence, disk and optional memory stop guards.

RSS is a sampled sum across the process group and double-counts shared pages;
MemAvailable is whole-host evidence, not per-command peak RAM. GNU time can be
used inside this wrapper for maximum individual-child RSS and CPU time.
"""
import argparse
import json
import math
import os
from pathlib import Path
import signal
import subprocess
import time


def sample(group, directory):
    memory = {}
    for line in Path("/proc/meminfo").read_text().splitlines():
        key, value = line.split(":", 1)
        if key in ("MemTotal", "MemAvailable", "SwapTotal", "SwapFree"):
            memory[key + "KiB"] = int(value.split()[0])
    rss_kib = 0
    processes = 0
    for path in Path("/proc").glob("[0-9]*/stat"):
        try:
            fields = path.read_text().rsplit(")", 1)[1].split()
            if int(fields[2]) == group:
                rss_kib += int(fields[21]) * os.sysconf("SC_PAGE_SIZE") // 1024
                processes += 1
        except (OSError, ValueError, IndexError):
            pass
    fs = os.statvfs(directory)
    used = fs.f_blocks - fs.f_bfree
    percent = math.ceil(100 * used / (used + fs.f_bavail))
    return dict(unix_time=time.time(), group_rss_sum_kib=rss_kib, processes=processes,
                disk_used_percent=percent, disk_available_bytes=fs.f_bavail * fs.f_frsize,
                **memory)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--max-used-memory-gib", type=float,
                    help="stop if MemTotal minus MemAvailable exceeds this many GiB")
    ap.add_argument("log", type=Path)
    ap.add_argument("command", nargs=argparse.REMAINDER)
    args = ap.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        ap.error("supply a command after --")
    if args.max_used_memory_gib is not None and args.max_used_memory_gib < 0:
        ap.error("--max-used-memory-gib must be nonnegative")
    args.log.parent.mkdir(parents=True, exist_ok=True)
    def limit_reason(point):
        if point["disk_used_percent"] > 85:
            return "disk use exceeds 85%"
        if args.max_used_memory_gib is not None and (
                point["MemTotalKiB"] - point["MemAvailableKiB"] >
                args.max_used_memory_gib * 1024 * 1024):
            return f"host used memory exceeds {args.max_used_memory_gib:g} GiB"
        return None
    # Check before launching, not only after the first sampling interval.
    reason = limit_reason(sample(-1, args.log.parent))
    if reason:
        raise SystemExit(f"{reason}; command not started")
    process = subprocess.Popen(command, start_new_session=True)
    with args.log.open("w") as log:
        try:
            while True:
                point = sample(process.pid, args.log.parent)
                log.write(json.dumps(point) + "\n")
                log.flush()
                reason = limit_reason(point)
                if reason:
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    try:
                        process.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        pass
                    # Kill remaining descendants even if the group leader exited.
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    raise SystemExit(f"{reason}; stopped process group")
                try:
                    code = process.wait(timeout=5)
                    break
                except subprocess.TimeoutExpired:
                    pass
        except KeyboardInterrupt:
            os.killpg(process.pid, signal.SIGTERM)
            raise
    raise SystemExit(code)


if __name__ == "__main__":
    main()
