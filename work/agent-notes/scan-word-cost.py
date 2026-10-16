#!/usr/bin/env python3
"""Record text hints for Word-to-Stack overhead; this is not a Lean proof."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
fixed = ROOT / "submission/InitECandidate/Proofs/StackAnalysis"
paths = sorted(fixed.glob("Data[0-9]*.lean"), key=lambda p: int(p.stem[4:]))
assert [int(p.stem[4:]) for p in paths] == list(range(64, 890))
records = []
for path in paths:
    data = path.read_bytes()
    source = data.decode()
    counts = {name: len(re.findall(r"\." + name + r"\b", source))
              for name in ("shareInst", "raise", "install", "mustTerminate")}
    records.append({"path": str(path.relative_to(ROOT)),
                    "sha256": hashlib.sha256(data).hexdigest(), "counts": counts,
                    "charged_constructor_occurrences": counts["shareInst"] + counts["raise"]})
result = {
    "description": "Text scan of fixed optimized Word literals. Named subprograms may be reused; these counts are NOT upper bounds on expanded syntax cost, kernel proofs, or a code-map integration theorem.",
    "files": len(records),
    "max_charged_constructor_occurrences": max(r["charged_constructor_occurrences"] for r in records),
    "records": records,
}
(ROOT / "work/agent-notes/word-cost-scan.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"files": len(records), "max_charged_constructor_occurrences": result["max_charged_constructor_occurrences"],
                  "totals": {name: sum(r["counts"][name] for r in records) for name in records[0]["counts"]}}))
