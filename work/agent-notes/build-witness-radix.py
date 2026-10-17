#!/usr/bin/env python3
"""Offline development artifacts for the candidate radix routines.

The proposed AST/ELF is not a refinement proof or a submission. Fixed sources,
proofs and submission/Solution.lean are never edited by this script. Run under
tools/baseline-resource-run.py. A fresh --stem preserves previous evidence.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
NOTES = ROOT / "work/agent-notes"
NAMESPACE = "InitECandidate.Solver.WitnessRadix.RawProgram"


def command(args, output=None, errors=None):
    subprocess.run([str(a) for a in args], cwd=ROOT, check=True, stdout=output, stderr=errors)


def cpp(source, target, assembly=False):
    with target.open("w") as output:
        args = ["cpp", "-P"]
        if assembly:
            args += ["-x", "assembler-with-cpp"]
        else:
            args += ["-w", "-nostdinc", "-I", ROOT / "guest/src", "-I", NOTES, "-x", "c"]
        command(args + [source], output=output)


def function_span(source, name):
    match = re.search(r"\bfun\s+(?:1|\{[^}]+\})\s+" + re.escape(name) + r"\s*\(", source)
    if match is None:
        raise ValueError(f"missing function {name}")
    opening = source.index("{", match.end())
    depth, cursor = 1, opening + 1
    while depth:
        depth += (source[cursor] == "{") - (source[cursor] == "}")
        cursor += 1
    return match.start(), cursor


def render_ast(expanded, stem, check=False):
    generated = NOTES / f"{stem}-generated.lean"
    with generated.open("w") as output, (NOTES / "logs" / f"{stem}-parse.log").open("w") as errors:
        command([ROOT / ".lake/build/bin/gen-guest-ast", expanded, NAMESPACE], output, errors)
    source = generated.read_text()
    source = source[source.index("import Flapjack.Pancake.PanLang"):]
    source = source.replace("/-- The stateless guest as flapjack Pancake declarations. -/",
                            "/-- Candidate routines plus the parser-only global declaration. -/")
    sha = hashlib.sha256((NOTES / "witness-radix.pnk").read_bytes()).hexdigest()
    header = ("-- Candidate radix witness routines; NOT the fixed challenge source.\n"
              "-- Generated from work/agent-notes/witness-radix.pnk using the pinned parser.\n"
              f"-- Source SHA-256: {sha}\n"
              "-- Parser output is a proposed literal program, not refinement evidence.\n")
    prints = "\n" + "\n".join(f"#print axioms {NAMESPACE}.guestFn_{name}" for name in
                                 ("solver_radix_index", "nodedb_build", "nodedb_lookup")) + "\n"
    target = ROOT / "submission/InitECandidate/Solver/WitnessRadix/RawProgram.lean"
    proposed = header + source + prints
    if check:
        assert target.read_text() == proposed, "AST regeneration differs from the checked source"
    else:
        target.write_text(proposed)


def link(source, stem):
    assembly = NOTES / f"{stem}.S"
    with assembly.open("w") as output, (NOTES / "logs" / f"{stem}-compile.log").open("w") as errors:
        command([ROOT / ".lake/packages/flapjack/.lake/build/bin/flapjack-compile", "--assembly", source],
                output, errors)
    expanded = NOTES / f"{stem}.s"
    cpp(assembly, expanded, assembly=True)
    with expanded.open("a") as output:
        output.write("\n.globl cake_bitmaps\n.globl cake_main\n")
    obj = NOTES / f"{stem}.o"
    elf = NOTES / f"{stem}.elf"
    command(["riscv64-unknown-elf-as", "-march=rv64ima", "-mno-relax", "-o", obj, expanded])
    command(["riscv64-unknown-elf-ld", "-T", ROOT / "guest/runtime/guest.ld", "-nostdlib", "--no-relax",
             "-e", "_start", "-o", elf, ROOT / "guest/build/guest.start.o", obj])
    return elf


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stem", required=True, help="fresh evidence/output prefix")
    parser.add_argument("--ast-only", action="store_true")
    parser.add_argument("--check-ast", action="store_true", help="require identical AST; do not overwrite it")
    parser.add_argument("--unit", action="store_true")
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z0-9-]+", args.stem):
        parser.error("stem must contain lowercase letters, digits and hyphens")
    record = NOTES / f"{args.stem}-artifacts.json"
    if record.exists() or (NOTES / f"{args.stem}-candidate.pp.pnk").exists():
        parser.error("stem already used; choose a fresh stem")
    expanded = NOTES / f"{args.stem}-routines.pp.pnk"
    cpp(NOTES / "witness-radix.pnk", expanded)
    render_ast(expanded, args.stem, check=args.check_ast)
    products = [NOTES / "witness-radix.pnk", expanded,
                ROOT / "submission/InitECandidate/Solver/WitnessRadix/RawProgram.lean"]
    if not args.ast_only:
        original = (ROOT / "Guest/guest.pp.pnk").read_text()
        replacements = expanded.read_text()
        for name in ("nodedb_build", "nodedb_lookup"):
            start, end = function_span(original, name)
            new_start, new_end = function_span(replacements, name)
            original = original[:start] + replacements[new_start:new_end] + original[end:]
        start, end = function_span(replacements, "solver_radix_index")
        source = NOTES / f"{args.stem}-candidate.pp.pnk"
        source.write_text(original + "\n" + replacements[start:end] + "\n")
        products += [source, link(source, f"{args.stem}-candidate")]
    if args.unit:
        source = NOTES / f"{args.stem}-unit.pp.pnk"
        cpp(NOTES / "witness-radix-unit.pnk", source)
        elf = link(source, f"{args.stem}-unit")
        output = NOTES / f"{args.stem}-unit.output"
        with (NOTES / "logs" / f"{args.stem}-unit.log").open("w") as log:
            command([ROOT / "tools/spike/spike_run", elf, "/dev/null", output], log, log)
        assert output.read_bytes()[32] == 1, "compiled radix unit failed"
        products += [source, elf, output]
    record.write_text(json.dumps({
        "scope": "proposed program/development ELF; not proof of refinement or finite certificate",
        "artifacts": {str(p.relative_to(ROOT)): {"bytes": p.stat().st_size,
            "sha256": hashlib.sha256(p.read_bytes()).hexdigest()} for p in products},
    }, indent=2) + "\n")
    print(record.relative_to(ROOT))


if __name__ == "__main__":
    main()
