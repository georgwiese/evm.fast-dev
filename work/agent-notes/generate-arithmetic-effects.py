#!/usr/bin/env python3
"""Untrusted original arithmetic-frame scaffolding; Lean checks all effects.
Refuses overwrite. --output allows exact reproduction checks.
"""
from pathlib import Path
import argparse
import re
root=Path(__file__).resolve().parents[2]
s=(root/'Guest/guest.pp.pnk').read_text()
heads=list(re.finditer(r'^fun [^\n]+? (\w+)\([^\n]*\) \{\n',s,re.M))
f={h[1]:s[h.end():heads[i+1].start() if i+1<len(heads) else len(s)] for i,h in enumerate(heads)}
calls={n:set(re.findall(r'\b(\w+)\(',b))&f.keys() for n,b in f.items()}
roots={n for n in f if n.startswith('u256_')}|{'sat_word','add_sat','min','max','ceil_log2','mul64x64','nlz32','div64by32','bit_length64','digits_to_u256','digits_len'}
closure=set(roots)
while True:
    old=len(closure)
    for n in list(closure): closure|=calls[n]
    if len(closure)==old:break
bad={n for n in closure if re.search(r'\b(?:st|st8|st32|stb|ffi|shmem)\b',f[n])}
good=set(); ordered=[]
while True:
    added=[n for n in sorted(closure-good-bad) if calls[n]<=good]
    if not added: break
    good.update(added);ordered+=added
assert len(ordered)==44
lines=['import InitECandidate.Solver.Input.LocalEffectsPrimitive', '',
'namespace InitECandidate.Solver.GasBudget.ArithmeticEffects',
'open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact',
'open Flapjack.Basis.Pure.MlString',
'open Input.LocalEffects', '',
'attribute [local irreducible] Input.LocalEffects.Preserves', '',
'-- Untrusted candidate catalogue. Every original body is checked below.',
'inductive Kind where']
lines += ['  | '+n for n in ordered]
lines += ['', 'def Kind.original : Kind → Decl (BitVec 64)']
lines += [f'  | .{n} => Guest.guestFn_{n}' for n in ordered]
lines += ['', 'def Kind.signature (kind : Kind) : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL :=',
'  match kind.original with',
'  | .function fn => (fn.params.map (fun pair => (ofString pair.1, shapeToHOL pair.2)), progToHOL fn.body, shapeToHOL fn.returnShape)',
'  | _ => ([], .skip, .one)', '',
'def Kind.body (kind : Kind) : ProgHOL 64 := kind.signature.2.1',
'def Kind.name (kind : Kind) : MlS := match kind.original with | .function fn => ofString fn.name | _ => ofString ""', '',
'def Environment (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) : Prop :=',
'  ∀ kind : Kind, code.lookup kind.name = some kind.signature', '']
ast=(root/'Guest/Ast.lean').read_text()
def split_terms(text):
    text=text.strip()
    if text.startswith('(') and text.endswith(')'):text=text[1:-1]
    result=[];start=0;depth=0;quoted=False;escaped=False
    for index,char in enumerate(text):
        if quoted:
            if escaped:escaped=False
            elif char=='\\':escaped=True
            elif char=='"':quoted=False
        elif char=='"':quoted=True
        elif char in '([{':depth+=1
        elif char in ')]}':depth-=1
        elif char.isspace() and depth==0:
            if start<index:result.append(text[start:index])
            start=index+1
    if start<len(text):result.append(text[start:])
    assert depth==0 and not quoted
    return result

def branch(proof):
    return ['· '+proof[0]]+['  '+line for line in proof[1:]]

def steps(program):
    terms=split_terms(program);tag=terms[0]
    if tag=='Prog.seq':
        assert len(terms)==3
        return ['apply Input.LocalEffects.sequence']+branch(steps(terms[1]))+branch(steps(terms[2]))
    if tag=='Prog.ite':
        assert len(terms)==4
        return ['apply Input.LocalEffects.conditional']+branch(steps(terms[2]))+branch(steps(terms[3]))
    if tag=='Prog.dec':
        assert len(terms)==5
        return ['apply Input.LocalEffects.declared']+steps(terms[4])
    if tag=='Prog.while':
        assert len(terms)==3
        return ['apply Input.LocalEffects.loop']+steps(terms[2])
    if tag=='Prog.decCall':
        assert len(terms)==6
        dep=terms[3].strip('"');assert dep in good
        return [f'refine Input.LocalEffects.scoped_body code _ _ (ofString "{dep}") _ _ _ _ _ (environment .{dep}) (pure_{dep} code environment) ?_']+steps(terms[5])
    if tag=='Prog.call':
        assert len(terms)==4
        dep=terms[2].strip('"');assert dep in good
        if terms[1]=='none':dest='none'
        elif 'VarKind.local' in terms[1]:dest='(some (some _))'
        else:
            assert 'some (none, none)' in terms[1],terms[1]
            dest='(some none)'
        return [f'exact Input.LocalEffects.call_body code {dest} (ofString "{dep}") _ _ _ _ (environment .{dep}) (pure_{dep} code environment)']
    leaves={'Prog.skip':'skip code','Prog.return':'returned code _','Prog.raise':'raised code _ _','Prog.primitive':'primitive code _ _ _','Prog.assign':'assign code _ _'}
    if tag in leaves:
        if tag=='Prog.assign':assert terms[1]=='VarKind.local'
        return ['exact Input.LocalEffects.'+leaves[tag]]
    if tag=='Prog.break':return ['exact (Input.LocalEffects.stopped code).1']
    if tag=='Prog.continue':return ['exact (Input.LocalEffects.stopped code).2']
    raise ValueError((tag,program[:100]))

for n in ordered:
    definition=ast.split('def guestFn_'+n+' :',1)[1].split('\ndef ',1)[0]
    program=definition.split('      body :=\n',1)[1].split('\n      returnShape :=',1)[0].strip()
    lines += [f'theorem pure_{n} (code) (environment : Environment code) : Preserves code Kind.{n}.body := by',
      f'  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_{n}, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]']
    lines += ['  '+line for line in steps(program)]
    lines += ['']
lines += ['theorem original_preserves (kind : Kind) (code) (environment : Environment code) : Preserves code kind.body := by',
'  cases kind with']
lines += [f'  | {n} => exact pure_{n} code environment' for n in ordered]
lines += ['', '/-- Every checked arithmetic helper retains all nonlocal fields at',
'every clock and for every outcome. No input-shape or callee-success premise. -/',
'theorem execution_frame (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)',
'    (environment : Environment source.code) (result : Option (PanSemResultExact 64))',
'    (run : evaluateHOLFiniteState source kind.body = (result, target)) :',
'    erase target = erase source := by',
'  have pureBody := original_preserves kind source.code environment',
'  unfold Input.LocalEffects.Preserves at pureBody',
'  have frame := pureBody source rfl',
'  simpa only [run] using frame', '',
'end InitECandidate.Solver.GasBudget.ArithmeticEffects', '',
'#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.original_preserves',
'#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.execution_frame']
def quiet_program(name):
    definition=ast.split('def guestFn_'+name+' :',1)[1].split('\ndef ',1)[0]
    return definition.split('      body :=\n',1)[1].split('\n      returnShape :=',1)[0].strip()
quiet_names=[name for name in ordered if not re.search(r'\bProg\.(?:while|call|decCall|tick|extCall)\b',quiet_program(name))]

def quiet_lines():
    result=['import InitECandidate.Solver.GasBudget.ArithmeticEffects',
      'import InitECandidate.Solver.Input.QuietClock', '',
      'namespace InitECandidate.Solver.GasBudget.ArithmeticEffects',
      'open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact', '',
      '-- Generated proof data: each true case is checked against the original AST.',
      'def Kind.quiet : Kind → Bool']
    result += [f'  | .{name} => '+('true' if name in quiet_names else 'false') for name in ordered]
    result += ['', 'theorem quiet_preserves (kind : Kind) (code) (checked : kind.quiet = true) : Input.QuietClock.Preserves code kind.body := by', '  cases kind with']
    for name in ordered:
        if name not in quiet_names:
            result += [f'  | {name} => cases checked']
        else:
            result += [f'  | {name} =>', f'    simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_{name}, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]']
            result += ['    '+line.replace('Input.LocalEffects','Input.QuietClock') for line in steps(quiet_program(name))]
    result += ['', '/-- Zero source clocks means no charged calls/loops; it does not',
      'mean zero straight-line target work. This covers all actual outcomes. -/',
      'theorem quiet_clock (kind : Kind) (checked : kind.quiet = true)',
      '    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (outcome : Option (PanSemResultExact 64))',
      '    (run : evaluateHOLFiniteState source kind.body = (outcome, target)) : target.clock = source.clock := by',
      '  have clock := quiet_preserves kind source.code checked source rfl',
      '  simpa only [run] using clock', '',
      'end InitECandidate.Solver.GasBudget.ArithmeticEffects', '',
      '#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.quiet_preserves',
      '#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.quiet_clock']
    return result

def program_price(program):
    terms=split_terms(program);tag=terms[0]
    if tag=='Prog.seq':return program_price(terms[1])+program_price(terms[2])
    if tag=='Prog.ite':return max(program_price(terms[2]),program_price(terms[3]))
    if tag=='Prog.dec':return program_price(terms[4])
    if tag=='Prog.call':return fixed_prices[terms[2].strip('"')]+1
    if tag=='Prog.decCall':return fixed_prices[terms[3].strip('"')]+1+program_price(terms[5])
    assert tag in {'Prog.skip','Prog.assign','Prog.primitive','Prog.return','Prog.raise','Prog.break','Prog.continue'},tag
    return 0

fixed_prices={}
for name in ordered:
    if not re.search(r'\bProg\.(?:while|tick|extCall)\b',quiet_program(name)) and calls[name]<=fixed_prices.keys():
        fixed_prices[name]=program_price(quiet_program(name))

def price_steps(program):
    terms=split_terms(program);tag=terms[0]
    if tag=='Prog.seq':
        return [f'apply Input.ClockCost.sequence code _ _ {program_price(terms[1])} {program_price(terms[2])}']+branch(price_steps(terms[1]))+branch(price_steps(terms[2]))
    if tag=='Prog.ite':
        return [f'apply Input.ClockCost.conditional code _ _ _ {program_price(terms[2])} {program_price(terms[3])}']+branch(price_steps(terms[2]))+branch(price_steps(terms[3]))
    if tag=='Prog.dec':return [f'apply Input.ClockCost.declared code _ _ _ _ {program_price(terms[4])}']+price_steps(terms[4])
    if tag=='Prog.decCall':
        dep=terms[3].strip('"')
        return [f'refine Input.ClockCost.scoped_body code _ _ (ofString "{dep}") _ _ _ _ _ {fixed_prices[dep]} {program_price(terms[5])} (environment .{dep}) (price_{dep} code environment) ?_']+price_steps(terms[5])
    if tag=='Prog.call':
        dep=terms[2].strip('"')
        if terms[1]=='none':dest='none'
        elif 'VarKind.local' in terms[1]:dest='(some (some _))'
        else:
            assert 'some (none, none)' in terms[1]
            dest='(some none)'
        return [f'exact Input.ClockCost.call_body code {dest} (ofString "{dep}") _ _ _ _ {fixed_prices[dep]} (environment .{dep}) (price_{dep} code environment)']
    return [line.replace('Input.LocalEffects','Input.ClockCost') for line in steps(program)]

def price_lines():
    result=['import InitECandidate.Solver.GasBudget.ArithmeticQuietClock',
      'import InitECandidate.Solver.Input.ClockCostScoped', '',
      'namespace InitECandidate.Solver.GasBudget.ArithmeticEffects',
      'open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact',
      'open Flapjack.Basis.Pure.MlString', '',
      '-- Every optional price is checked against its unchanged original body.',
      'def Kind.fixedPrice : Kind → Option Nat']
    result += [f'  | .{name} => '+('some '+str(fixed_prices[name]) if name in fixed_prices else 'none') for name in ordered]
    for name,price in fixed_prices.items():
        result += ['', f'theorem price_{name} (code) (environment : Environment code) : Input.ClockCost.Bound code Kind.{name}.body {price} := by']
        if name in quiet_names:
            result += [f'  exact Input.ClockCost.of_quiet code _ (quiet_preserves .{name} code rfl)']
        else:
            result += [f'  simp only [Kind.body, Kind.signature, Kind.original, Guest.guestFn_{name}, progToHOL, expToHOL, shapeToHOL, List.map_cons, List.map_nil, Option.map_none]']
            result += ['  '+line for line in price_steps(quiet_program(name))]
    result += ['', 'theorem fixed_price (kind : Kind) (price : Nat) (code) (environment : Environment code)',
      '    (checked : kind.fixedPrice = some price) : Input.ClockCost.Bound code kind.body price := by', '  cases kind with']
    for name in ordered:
        if name not in fixed_prices:result += [f'  | {name} => cases checked']
        else:
            result += [f'  | {name} =>', f'    have equal : price = {fixed_prices[name]} := by simpa only [Kind.fixedPrice, Option.some.injEq] using checked.symm',
              '    subst price', f'    exact price_{name} code environment']
    result += ['', '/-- Actual source clocks spent, for every real helper outcome.',
      'These are call/loop units and omit straight-line target instructions. -/',
      'theorem fixed_clock_spent (kind : Kind) (price : Nat) (checked : kind.fixedPrice = some price)',
      '    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : Environment source.code)',
      '    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source kind.body = (outcome, target)) :',
      '    source.clock - target.clock ≤ price := by',
      '  have cost := fixed_price kind price source.code environment checked source rfl',
      '  simpa only [run] using cost', '',
      'theorem fixed_call_spent (kind : Kind) (price : Nat) (checked : kind.fixedPrice = some price)',
      '    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (environment : Environment source.code)',
      '    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) (outcome : Option (PanSemResultExact 64))',
      '    (run : evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) kind.name arguments) = (outcome, target)) :',
      '    source.clock - target.clock ≤ price + 1 := by',
      '  have bound := Input.ClockCost.call_body source.code destination kind.name arguments kind.signature.1 kind.body kind.signature.2.2 price',
      '    (environment kind) (fixed_price kind price source.code environment checked)',
      '  have actual := bound source rfl',
      '  simpa only [run] using actual', '',
      'end InitECandidate.Solver.GasBudget.ArithmeticEffects', '',
      '#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.fixed_price',
      '#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.fixed_clock_spent',
      '#print axioms InitECandidate.Solver.GasBudget.ArithmeticEffects.fixed_call_spent']
    return result

parser=argparse.ArgumentParser()
parser.add_argument('--quiet',action='store_true',help='Generate the original zero-source-clock subcatalogue.')
parser.add_argument('--prices',action='store_true',help='Generate source call/loop clock prices for the closed no-loop helper subcatalogue.')
parser.add_argument('--output',type=Path)
args=parser.parse_args()
if args.quiet and args.prices:parser.error('--quiet and --prices are mutually exclusive')
if args.output is None:
    filename='ArithmeticClockPrice.lean' if args.prices else ('ArithmeticQuietClock.lean' if args.quiet else 'ArithmeticEffects.lean')
    args.output=root/'submission/InitECandidate/Solver/GasBudget'/filename
assert not args.output.exists(),f'Refusing overwrite: {args.output}'
args.output.write_text('\n'.join(price_lines() if args.prices else (quiet_lines() if args.quiet else lines))+'\n')
print({'helpers':len(fixed_prices) if args.prices else (len(quiet_names) if args.quiet else len(ordered)),'bytes':args.output.stat().st_size})
