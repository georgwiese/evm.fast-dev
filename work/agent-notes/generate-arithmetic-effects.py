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
parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=root/'submission/InitECandidate/Solver/GasBudget/ArithmeticEffects.lean');args=parser.parse_args()
assert not args.output.exists(),f'Refusing overwrite: {args.output}'
args.output.write_text('\n'.join(lines)+'\n')
print({'helpers':len(ordered),'bytes':args.output.stat().st_size})
