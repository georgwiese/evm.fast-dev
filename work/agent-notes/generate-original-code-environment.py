#!/usr/bin/env python3
"""Untrusted literal indices; every resulting original-body equality is checked by Lean."""
from pathlib import Path
import argparse
import re

root = Path(__file__).resolve().parents[2]
ap = argparse.ArgumentParser()
ap.add_argument('--output', type=Path, required=True)
args = ap.parse_args()
if args.output.exists():
    raise SystemExit('Refusing to overwrite existing output')
ast = (root / 'Guest/Ast.lean').read_text().split('def guestAst :')[1]
functions = re.findall(r'guestFn_(\w+)', ast)
effects = (root / 'submission/InitECandidate/Solver/GasBudget/ArithmeticEffects.lean').read_text()
kinds = re.findall(r'^  \| (\w+)$', effects.split('inductive Kind where')[1].split('def Kind.original')[0], re.M)
out = '''import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.GasBudget.ArithmeticEffects
import InitECandidate.Solver.GasBudget.ArithmeticStackCall
import InitECandidate.Solver.GasBudget.DispatchProgram
import InitECandidate.Solver.GasBudget.StopNormal
import InitECandidate.Solver.GasBudget.JumpdestNormal

namespace InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def originalEntry (declaration : Decl (BitVec 64)) : MlS × (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :=
  match declToHOL declaration with
  | .function fn => (fn.name, fn.params, fn.body, fn.returnShape)
  | _ => (ofString "", [], .skip, .one)

-- Literal positions in the unchanged source; this catalogue is not executable code.
def arithmeticIndex : ArithmeticEffects.Kind → Nat
'''
out += ''.join(f'  | .{kind} => {functions.index(kind)}\n' for kind in kinds)
out += '''
theorem arithmetic_index (kind : ArithmeticEffects.Kind) :
    (functionsHOL Input.OriginalCode.program)[arithmeticIndex kind]? = some (kind.name, kind.signature) := by
  cases kind <;> rfl

theorem arithmetic (code) (installed : Input.OriginalCode.Installed code) : ArithmeticEffects.Environment code := by
  intro kind
  exact Input.OriginalCode.indexed code installed (arithmeticIndex kind) (kind.name, kind.signature) (arithmetic_index kind)

'''
signatures = [
    ('stack_pop', 'StackPop', '[]', 'StackPop.shape'),
    ('stack_push', 'StackPush', 'StackPush.formals', '.one'),
    ('charge_gas', 'RegularCharge', 'RegularCharge.formals', '.one'),
    ('pc_add', 'PcAdd', 'PcAdd.formals', '.one'),
    ('op_dispatch', 'OpcodeDispatch', 'OpcodeDispatch.formals', '.one'),
    ('op_stop', 'Stop', '[]', '.one'),
    ('op_jumpdest', 'Jumpdest', '[]', '.one'),
]
for name, namespace, formals, shape in signatures:
    unfold = ['originalEntry', 'declToHOL', 'funDeclToHOL', f'Guest.guestFn_{name}', f'{namespace}.body']
    if formals != '[]':
        unfold.append(formals)
    if shape != '.one':
        unfold.append(shape)
    unfold += ['paramToHOL', 'shapeToHOL', 'List.map_cons', 'List.map_nil']
    out += f'''theorem {name} (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "{name}") = some ({formals}, {namespace}.body, {shape}) := by
  have found : (functionsHOL Input.OriginalCode.program)[{functions.index(name)}]? = some (originalEntry Guest.guestFn_{name}) := by rfl
  have checked := Input.OriginalCode.indexed code installed {functions.index(name)} _ found
  simpa only [{', '.join(unfold)}] using checked

'''
opcodes = ['op_add', 'op_mul', 'op_sub', 'op_signextend', 'op_shl', 'op_shr', 'op_sar']
out += 'def opcodeIndex : ArithmeticStackOpcode.Kind → Nat\n'
out += ''.join(f'  | .{kind} => {functions.index(kind)}\n' for kind in opcodes)
out += '''
theorem opcode_index (kind : ArithmeticStackOpcode.Kind) :
    (functionsHOL Input.OriginalCode.program)[opcodeIndex kind]? = some (kind.function, ([], kind.site.body, .one)) := by
  cases kind
'''
for kind in opcodes:
    out += f'''  case {kind} =>
    have found : (functionsHOL Input.OriginalCode.program)[{functions.index(kind)}]? = some (originalEntry Guest.guestFn_{kind}) := by rfl
    simpa only [opcodeIndex, ArithmeticStackOpcode.Kind.function, ArithmeticStackOpcode.Kind.label,
      ArithmeticStackOpcode.Kind.site, OpcodeChargeSites.Kind.body, originalEntry, declToHOL, funDeclToHOL,
      Guest.guestFn_{kind}, shapeToHOL, List.map_nil] using found
'''
out += '''
theorem arithmetic_opcode (code) (installed : Input.OriginalCode.Installed code) (kind : ArithmeticStackOpcode.Kind) :
    code.lookup kind.function = some ([], kind.site.body, .one) :=
  Input.OriginalCode.indexed code installed (opcodeIndex kind) _ (opcode_index kind)

end InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.arithmetic_index
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.arithmetic
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.opcode_index
#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.arithmetic_opcode
'''
out += ''.join(f'#print axioms InitECandidate.Solver.GasBudget.OriginalCodeEnvironment.{name}\n' for name, *_ in signatures)
args.output.write_text(out)
