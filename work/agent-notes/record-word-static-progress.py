#!/usr/bin/env python3
"""Record only completed chunk builds, never the running/failing log suffix.

This is an evidence index, not a verifier. It relies on the local successful
Lake runs and their printed axiom sets, and must run against unchanged sources.
"""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
NOTES = ROOT / "work/agent-notes"
log_path = NOTES / "logs/word-static-all.log"
log = log_path.read_text()
completed = list(re.finditer(r"^END \d+/\d+ .+$", log, re.M))
if not completed:
    raise SystemExit("No completed chunks yet")
through = completed[-1][0]
log = log[:completed[-1].end()]
assert not re.search(r"^error:", log, re.M), "Do not record failed builds"
allowed = {"propext", "Classical.choice", "Quot.sound"}
facts = {}
for name, axiom_text in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", log):
    if not name.startswith("InitECandidate.Solver."):
        continue
    axioms = [a.strip() for a in axiom_text.split(",") if a.strip()]
    assert set(axioms) <= allowed, (name, axioms)
    facts[name] = axioms

path = NOTES / "proof-checks.json"
record = json.loads(path.read_text())
modules = {x["path"]: x for x in record["modules"]}
theorems = {x["theorem"]: x for x in record["theorems"]}
added = 0
for source in sorted((ROOT / "submission/InitECandidate/Solver/WordStatic").rglob("*.lean")):
    rel = str(source.relative_to(ROOT))
    if rel in modules:
        assert modules[rel]["sha256"] == hashlib.sha256(source.read_bytes()).hexdigest()
        continue
    names = re.findall(r"^#print axioms ([\w.]+)$", source.read_text(), re.M)
    if not names or not all(n in facts for n in names) or f"info: {rel}:" not in log:
        continue
    modules[rel] = {"path": rel, "sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
    added += 1
    for name in names:
        theorems[name] = {"theorem": name, "axioms": facts[name],
                          "successful_log": log_path.name, "completed_through": through}
record["modules"] = sorted(modules.values(), key=lambda x: x["path"])
record["theorems"] = list(theorems.values())
path.write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps({"completed_through": through, "added_modules": added,
                  "checked_modules_total": len(modules)}))
