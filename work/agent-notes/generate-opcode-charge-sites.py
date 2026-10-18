#!/usr/bin/env python3
"""Untrusted original opcode-prefix catalogue; Lean checks every body_shape.

Only leading literal stack_pop declarations followed by charge_gas(N) qualify.
Refuses overwrite. --output allows exact reproduction checks.
"""
from pathlib import Path
import argparse
import re
root = Path(__file__).resolve().parents[2]
source = (root / 'Guest/guest.pp.pnk').read_text()
sites = []
for match in re.finditer(r'^fun 1 (op_\w+)\([^\n]*\) \{\n', source, re.M):
    tail = source[match.end():]
    names = []
    while popped := re.match(r'  var \{1,1,1,1\} (\w+) = stack_pop\(\);\n', tail):
        names.append(popped[1])
        tail = tail[popped.end():]
    if charged := re.match(r'  charge_gas\((\d+)\);\n', tail):
        sites.append((match[1], names, int(charged[1])))
assert len(sites) == 59
lines = ['import InitECandidate.Solver.GasBudget.OpcodeChargePrefix', '',
'namespace InitECandidate.Solver.GasBudget.OpcodeChargeSites',
'open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact',
'open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch', '',
'-- Generated proof data from unchanged original opcode prefixes.',
'-- body_shape checks every case against the original Guest AST.',
'inductive Kind where']
lines += ['  | ' + name for name, _, _ in sites]
lines += ['', 'def Kind.body : Kind → ProgHOL 64']
lines += [f'  | .{name} => match Guest.guestFn_{name} with | .function fn => progToHOL fn.body | _ => .skip' for name, _, _ in sites]
lines += ['', 'def Kind.names : Kind → List String']
lines += [f'  | .{name} => [' + ', '.join('"' + n + '"' for n in names) + ']' for name, names, _ in sites]
lines += ['', 'def Kind.fee : Kind → Nat']
lines += [f'  | .{name} => {fee}' for name, _, fee in sites]
lines += ['', 'def stripPops : Nat → ProgHOL 64 → ProgHOL 64',
'  | 0, program => program',
'  | count + 1, .decCall _ _ _ _ rest => stripPops count rest',
'  | _ + 1, _ => .skip', '',
'def Kind.suffix (kind : Kind) : ProgHOL 64 :=',
'  match stripPops kind.names.length kind.body with | .seq _ rest => rest | _ => .skip', '',
' theorem body_shape (kind : Kind) : kind.body = OpcodeChargePrefix.program kind.names (BitVec.ofNat 64 kind.fee) kind.suffix := by',
'  cases kind <;> simp only [Kind.body, Kind.names, Kind.fee, Kind.suffix, stripPops, OpcodeChargePrefix.program, StackPop.pops, StackPop.shape, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none, ' + ', '.join('Guest.guestFn_' + name for name, _, _ in sites) + '] <;> rfl', '',
' theorem fee_positive (kind : Kind) : 0 < (BitVec.ofNat 64 kind.fee).toNat := by',
'  cases kind <;> decide', '',
'/-- Actual normal execution of any of these59 original helpers reaches its',
'real suffix after a positive charge. This is a prefix contract, not a claim',
'about suffix gas preservation, covered exceptional paths or whole runtime. -/',
'theorem normal (kind : Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)',
'    (stackCode : source.code.lookup (ofString "stack_pop") = some ([], StackPop.body, StackPop.shape))',
'    (chargeCode : source.code.lookup (ofString "charge_gas") = some (RegularCharge.formals, RegularCharge.body, .one))',
'    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))',
'    (cap : regularBudget source.memory frame ≤ 16777216)',
'    (value : ValueHOL 64) (run : evaluateHOLFiniteState source kind.body = (some (.returned value), post)) :',
'    ∃ ready inner, kind.names.length + 1 ≤ source.clock ∧ ready.clock = source.clock - (kind.names.length + 1) ∧',
'      emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - (kind.names.length + 1)} ∧',
'      evaluateHOLFiniteState ready kind.suffix = (some (.returned value), inner) ∧',
'      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner ∧',
'      regularBudget ready.memory frame = regularBudget source.memory frame ∧',
'      (wordAt ready.memory (frame + 184#64)).toNat = (wordAt source.memory (frame + 184#64)).toNat + kind.fee ∧',
'      (wordAt source.memory (frame + 184#64)).toNat < (wordAt ready.memory (frame + 184#64)).toNat := by',
'  rw [body_shape] at run',
'  obtain ⟨ready, inner, fits, clock, frameEq, continuationRun, postEq, budget, credit⟩ :=',
'    OpcodeChargePrefix.normal kind.names source post frame (BitVec.ofNat 64 kind.fee) kind.suffix stackCode chargeCode ev cap value run',
'  have feeSmall : kind.fee < 2 ^ 64 := by cases kind <;> decide',
'  have positive := fee_positive kind',
'  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt feeSmall] at credit positive',
'  exact ⟨ready, inner, fits, clock, frameEq, continuationRun, postEq, budget, credit, by omega⟩', '',
'end InitECandidate.Solver.GasBudget.OpcodeChargeSites', '',
'#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.body_shape',
'#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.fee_positive',
'#print axioms InitECandidate.Solver.GasBudget.OpcodeChargeSites.normal']
parser = argparse.ArgumentParser()
parser.add_argument('--output', type=Path, default=root / 'submission/InitECandidate/Solver/GasBudget/OpcodeChargeSites.lean')
args = parser.parse_args()
assert not args.output.exists(), f'Refusing overwrite: {args.output}'
args.output.write_text('\n'.join(lines).replace('\n theorem ', '\ntheorem ') + '\n')
print({'sites': len(sites), 'bytes': args.output.stat().st_size})
