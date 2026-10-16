#!/usr/bin/env python3
"""Run a command with periodic resource evidence and an 85% disk stop guard.

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
    ap.add_argument("log", type=Path)
    ap.add_argument("command", nargs=argparse.REMAINDER)
    args = ap.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        ap.error("supply a command after --")
    args.log.parent.mkdir(parents=True, exist_ok=True)
    # Check before launching, not only after the first sampling interval.
    if sample(-1, args.log.parent)["disk_used_percent"] > 85:
        raise SystemExit("disk use exceeds 85%; command not started")
    process = subprocess.Popen(command, start_new_session=True)
    with args.log.open("w") as log:
        try:
            while True:
                point = sample(process.pid, args.log.parent)
                log.write(json.dumps(point) + "\n")
                log.flush()
                if point["disk_used_percent"] > 85:
                    os.killpg(process.pid, signal.SIGTERM)
                    try:
                        process.wait(timeout=10)
                    except subprocess.TimeoutExpired:
                        pass
                    # Kill remaining descendants even if the group leader exited.
                    try:
                        os.killpg(process.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    raise SystemExit("disk use exceeds 85%; stopped process group")
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
