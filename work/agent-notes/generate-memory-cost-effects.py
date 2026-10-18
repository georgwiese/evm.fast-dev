#!/usr/bin/env python3
"""Untrusted original memory-cost scaffolding; Lean checks effects/prices.
Reuses the explicit AST parser from generate-arithmetic-effects.py without
executing that generator. Refuses overwrite and supports exact reproduction.
"""
from pathlib import Path
import argparse
import ast
import re

root = Path(__file__).resolve().parents[2]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--no-exceptions', action='store_true')
args = parser.parse_args()
if args.output.exists():
    raise SystemExit('Refusing to overwrite existing output')
source = ast.parse((root/'work/agent-notes/generate-arithmetic-effects.py').read_text())
definitions = [node for node in source.body if isinstance(node, ast.FunctionDef)
               and node.name in {'split_terms', 'branch'}]
assert len(definitions) == 2
helpers = {}
exec(compile(ast.Module(body=definitions, type_ignores=[]), '<shared-ast-parser>', 'exec'), helpers)
split_terms, branch = helpers['split_terms'], helpers['branch']
guest = (root/'Guest/Ast.lean').read_text()
names = ['ceil32', 'words_of', 'memory_gas_cost', 'extend_memory_cost1']
functions = re.findall(r'guestFn_(\w+)', guest.split('def guestAst :')[1])
prices_source = (root/'submission/InitECandidate/Solver/GasBudget/ArithmeticClockPrice.lean').read_text()
prices = {name: int(price) for name, price in re.findall(r'^  \| \.(\w+) => some (\d+)$', prices_source, re.M)}
known_arithmetic = set(prices)

def program(name):
    definition = guest.split('def guestFn_'+name+' :', 1)[1].split('\ndef ', 1)[0]
    return definition.split('      body :=\n', 1)[1].split('\n      returnShape :=', 1)[0].strip()

def price_of(code):
    terms = split_terms(code)
    tag = terms[0]
    if tag == 'Prog.seq':
        return price_of(terms[1]) + price_of(terms[2])
    if tag == 'Prog.ite':
        return max(price_of(terms[2]), price_of(terms[3]))
    if tag == 'Prog.dec':
        return price_of(terms[4])
    if tag == 'Prog.decCall':
        return prices[terms[3].strip('"')] + 1 + price_of(terms[5])
    if tag == 'Prog.call':
        return prices[terms[2].strip('"')] + 1
    assert tag in {'Prog.skip', 'Prog.assign', 'Prog.return', 'Prog.primitive', 'Prog.raise'}, tag
    return 0

def code_fact(name):
    if name in known_arithmetic:
        return f'(OriginalCodeEnvironment.arithmetic code installed .{name})'
    assert name in names
    return f'(entry code installed .{name})'

def proof_fact(name, mode):
    if mode == 'safe':
        return f'(safe_{name} code installed)'
    if name in known_arithmetic:
        return f'(ArithmeticEffects.{mode}_{name} code (OriginalCodeEnvironment.arithmetic code installed))'
    return f'({mode}_{name} code installed)'

def steps(code, mode):
    terms = split_terms(code)
    tag = terms[0]
    namespace = {'pure': 'Input.LocalEffects', 'price': 'Input.ClockCost', 'safe': 'Input.NoException'}[mode]
    if tag == 'Prog.seq':
        extra = f' code _ _ {price_of(terms[1])} {price_of(terms[2])}' if mode == 'price' else ''
        return [f'apply {namespace}.sequence{extra}'] + branch(steps(terms[1], mode)) + branch(steps(terms[2], mode))
    if tag == 'Prog.ite':
        extra = f' code _ _ _ {price_of(terms[2])} {price_of(terms[3])}' if mode == 'price' else ''
        return [f'apply {namespace}.conditional{extra}'] + branch(steps(terms[2], mode)) + branch(steps(terms[3], mode))
    if tag == 'Prog.dec':
        extra = f' code _ _ _ _ {price_of(terms[4])}' if mode == 'price' else ''
        return [f'apply {namespace}.declared{extra}'] + steps(terms[4], mode)
    if tag == 'Prog.decCall':
        dependency = terms[3].strip('"')
        extra = f' {prices[dependency]} {price_of(terms[5])}' if mode == 'price' else ''
        return [f'refine {namespace}.scoped_body code _ _ (ofString "{dependency}") _ _ _ _ _{extra} '
                f'{code_fact(dependency)} {proof_fact(dependency, mode)} ?_'] + steps(terms[5], mode)
    if tag == 'Prog.call':
        dependency = terms[2].strip('"')
        if terms[1] == 'none':
            destination = 'none'
        elif 'VarKind.local' in terms[1]:
            destination = '(some (some _))'
        else:
            assert 'some (none, none)' in terms[1]
            destination = '(some none)'
        extra = f' {prices[dependency]}' if mode == 'price' else ''
        if mode == 'safe':
            assert destination == '(some none)', (dependency, destination)
            destination = ''
        return [f'exact {namespace}.call_body code {destination} (ofString "{dependency}") _ _ _ _{extra} '
                f'{code_fact(dependency)} {proof_fact(dependency, mode)}']
    leaves = {'Prog.skip': 'skip code', 'Prog.return': 'returned code _',
              'Prog.assign': 'assign code _ _', 'Prog.primitive': 'primitive code _ _ _',
              'Prog.raise': 'raised code _ _'}
    assert tag in leaves, tag
    if tag == 'Prog.assign':
        assert terms[1] == 'VarKind.local'
    return [f'exact {namespace}.{leaves[tag]}']

out = ['import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment',
       'import InitECandidate.Solver.GasBudget.ArithmeticClockPrice', '',
       'namespace InitECandidate.Solver.GasBudget.MemoryCostEffects',
       'open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact',
       'open Flapjack.Basis.Pure.MlString', '',
       'inductive Kind where']
out += ['  | '+name for name in names]
out += ['', 'def Kind.original : Kind → Decl (BitVec 64)']
out += [f'  | .{name} => Guest.guestFn_{name}' for name in names]
out += ['', 'def Kind.signature (kind : Kind) : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL :=',
        '  match kind.original with',
        '  | .function fn => (fn.params.map paramToHOL, progToHOL fn.body, shapeToHOL fn.returnShape)',
        '  | _ => ([], .skip, .one)',
        'def Kind.name (kind : Kind) : MlS := match kind.original with | .function fn => ofString fn.name | _ => ofString ""',
        'def Kind.body (kind : Kind) : ProgHOL 64 := kind.signature.2.1', '',
        'def Kind.index : Kind → Nat']
out += [f'  | .{name} => {functions.index(name)}' for name in names]
out += ['', 'set_option maxRecDepth 100000 in',
        'theorem original_index (kind : Kind) : (functionsHOL Input.OriginalCode.program)[kind.index]? = some (kind.name, kind.signature) := by',
        '  cases kind <;> rfl', '',
        'theorem entry (code) (installed : Input.OriginalCode.Installed code) (kind : Kind) : code.lookup kind.name = some kind.signature :=',
        '  Input.OriginalCode.indexed code installed kind.index (kind.name, kind.signature) (original_index kind)', '']
for name in names:
    prices[name] = price_of(program(name))
    for mode in ['pure', 'price']:
        target = f'Input.LocalEffects.Preserves code Kind.{name}.body' if mode == 'pure' else f'Input.ClockCost.Bound code Kind.{name}.body {prices[name]}'
        out += [f'theorem {mode}_{name} (code) (installed : Input.OriginalCode.Installed code) : {target} := by',
                f'  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_{name}, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]']
        out += ['  '+line for line in steps(program(name), mode)] + ['']
out += ['end InitECandidate.Solver.GasBudget.MemoryCostEffects', '',
        '#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.original_index',
        '#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.entry']
out += [f'#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.{mode}_{name}' for name in names for mode in ['pure', 'price']]
if args.no_exceptions:
    out = ['import InitECandidate.Solver.GasBudget.MemoryCostEffects',
           'import InitECandidate.Solver.Input.NoExceptionScoped', '',
           'namespace InitECandidate.Solver.GasBudget.MemoryCostEffects',
           'open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact',
           'open Flapjack.Basis.Pure.MlString', '']
    arithmetic_names = ['add_sat', 'sat_word', 'u256_is_zero', 'mul64x64']
    for name in arithmetic_names + names:
        kind = 'ArithmeticEffects.Kind' if name in arithmetic_names else 'Kind'
        out += [f'theorem safe_{name} (code) (installed : Input.OriginalCode.Installed code) : Input.NoException.Safe code {kind}.{name}.body := by',
                f'  simp only [{kind}.body, {kind}.signature, {kind}.original, Guest.guestFn_{name}, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]']
        out += ['  '+line for line in steps(program(name), 'safe')] + ['']
    out += ['end InitECandidate.Solver.GasBudget.MemoryCostEffects', '']
    out += [f'#print axioms InitECandidate.Solver.GasBudget.MemoryCostEffects.safe_{name}' for name in arithmetic_names + names]
args.output.write_text('\n'.join(out)+'\n')
print({name: prices[name] for name in names})
