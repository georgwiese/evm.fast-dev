#!/usr/bin/env python3
"""Measure synthetic inputs sequentially, recording output without a PASS claim."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("elf", type=Path)
    ap.add_argument("manifest", type=Path)
    ap.add_argument("output", type=Path)
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--spike", type=Path, default=Path("tools/spike/spike_run"))
    args = ap.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    results = []
    for row in json.loads(args.manifest.read_text()):
        disk = shutil.disk_usage(args.output)
        if disk.used / disk.total > 0.85:
            raise SystemExit("disk usage exceeds 85%; stopped")
        label = row["label"]
        if Path(label).name != label or label in (".", ".."):
            raise ValueError("unsafe synthetic label")
        log = args.output / (label + ".log")
        out = args.output / (label + ".output")
        rss = args.output / (label + ".rss")
        input_path = args.manifest.parent / row["input_file"]
        command = ["/usr/bin/time", "-f", "%M", "-o", str(rss),
                   str(args.spike.resolve()), str(args.elf.resolve()),
                   str(input_path.resolve()), str(out.resolve())]
        started = time.monotonic()
        timed_out = False
        with log.open("w") as f:
            process = subprocess.Popen(command, stdout=f, stderr=subprocess.STDOUT,
                                       start_new_session=True)
            try:
                code = process.wait(timeout=args.timeout)
            except subprocess.TimeoutExpired:
                timed_out = True
                os.killpg(process.pid, signal.SIGKILL)
                code = process.wait()
        text = log.read_text(errors="replace")
        count = re.search(r"halted cleanly steps=(\d+)", text)
        peak = rss.read_text().splitlines()[-1] if rss.exists() and rss.stat().st_size else ""
        result = dict(row, rc=code, timeout=timed_out, seconds=time.monotonic() - started,
                      spike_instructions=int(count[1]) if count else None,
                      peak_rss_kib=int(peak) if peak.isdigit() else None,
                      output_hex=out.read_bytes().hex() if out.exists() else None)
        results.append(result)
        report = dict(elf_sha256=hashlib.sha256(args.elf.read_bytes()).hexdigest(),
                      kind="synthetic measurements; no conformance assertion", records=results)
        (args.output / "results.json").write_text(json.dumps(report, indent=2) + "\n")
        print(label, result["spike_instructions"], code, flush=True)


if __name__ == "__main__":
    main()
