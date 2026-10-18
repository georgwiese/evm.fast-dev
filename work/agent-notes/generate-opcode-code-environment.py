#!/usr/bin/env python3
"""Untrusted literal original opcode signatures; Lean checks every index/body."""
from pathlib import Path
import argparse
import re

root = Path(__file__).resolve().parents[2]
ap = argparse.ArgumentParser()
ap.add_argument('--output', type=Path, required=True)
args = ap.parse_args()
if args.output.exists():
    raise SystemExit('Refusing to overwrite existing output')
source = (root / 'submission/InitECandidate/Solver/GasBudget/OpcodeChargeSites.lean').read_text()
kinds = re.findall(r'^  \| (\w+)$', source.split('inductive Kind where')[1].split('def Kind.body')[0], re.M)
ast = (root / 'Guest/Ast.lean').read_text().split('def guestAst :')[1]
functions = re.findall(r'guestFn_(\w+)', ast)
assert len(kinds) == 59
out = '''import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.GasBudget.OpcodeChargeSites

namespace InitECandidate.Solver.GasBudget.OpcodeChargeSites
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000

-- Literal original declaration data, not a replacement implementation.
def Kind.original : Kind → Decl (BitVec 64)
'''
out += ''.join(f'  | .{kind} => Guest.guestFn_{kind}\n' for kind in kinds)
out += '\ndef Kind.label : Kind → String\n'
out += ''.join(f'  | .{kind} => "{kind}"\n' for kind in kinds)
out += '''
def Kind.name (kind : Kind) : MlS := ofString kind.label
def Kind.signature (kind : Kind) : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL :=
  match kind.original with
  | .function fn => (fn.params.map paramToHOL, progToHOL fn.body, shapeToHOL fn.returnShape)
  | _ => ([], .skip, .one)

def Kind.index : Kind → Nat
'''
out += ''.join(f'  | .{kind} => {functions.index(kind)}\n' for kind in kinds)
out += '''
theorem signature_body (kind : Kind) : kind.signature.2.1 = kind.body := by cases kind <;> rfl

theorem signature_return (kind : Kind) : kind.signature.2.2 = .one := by
  cases kind <;> simp only [Kind.signature, Kind.original, shapeToHOL, '''
out += ', '.join('Guest.guestFn_' + kind for kind in kinds)
out += ''']

theorem original_index (kind : Kind) :
    (functionsHOL Input.OriginalCode.program)[kind.index]? = some (kind.name, kind.signature) := by
  cases kind <;> rfl

theorem installed (code) (environment : Input.OriginalCode.Installed code) (kind : Kind) :
    code.lookup kind.name = some (kind.signature.1, kind.body, .one) := by
  have original := Input.OriginalCode.indexed code environment kind.index (kind.name, kind.signature) (original_index kind)
  have pair : kind.signature = (kind.signature.1, kind.body, .one) := by
    rw [← signature_body kind, ← signature_return kind]
  rw [pair] at original
  exact original

end InitECandidate.Solver.GasBudget.OpcodeChargeSites

#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.signature_body
#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.signature_return
#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.original_index
#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.installed
'''
args.output.write_text(out)
