#!/usr/bin/env python3
"""Generate actual Software startup global-effect proofs; Lean must check them.

The source scan selects a closed acyclic call graph, never a runtime premise.
It does not alter the guest or certify generated proofs by itself.
"""
from pathlib import Path
from collections import Counter
import hashlib,json,re

ROOT=Path(__file__).resolve().parents[2]
source=(ROOT/'Guest/SoftwareAst.lean').read_text()
fragments=re.split(r'\ndef guestFn_(\w+) :','\n'+source)
functions={}

def parse(tokens,index):
    token=tokens[index]
    if token not in ('(', '['): return token,index+1
    closing=')' if token=='(' else ']'
    children=[];index+=1
    while tokens[index]!=closing:
        node,index=parse(tokens,index);children.append(node)
    return (token,children),index+1

def nodes(tree):
    if not isinstance(tree,tuple):return
    yield tree
    for child in tree[1]:yield from nodes(child)

def leaves(tree):
    if isinstance(tree,str):yield tree
    else:
        for child in tree[1]:yield from leaves(child)

for i in range(1,len(fragments),2):
    name,fragment=fragments[i:i+2]
    body=fragment.split('body :=',1)[1].split('\n      returnShape :=',1)[0]
    tokens=re.findall(r'"(?:\\.|[^"\\])*"|[()[\],]|[^\s()[\],]+',body)
    tree,end=parse(tokens,0)
    assert end==len(tokens),(name,end,len(tokens))
    calls={json.loads(n[1][3] if n[1][0]=='Prog.decCall' else n[1][2])
           for n in nodes(tree) if n[1] and n[1][0] in ('Prog.call','Prog.decCall')}
    functions[name]={'tree':tree,'calls':sorted(calls),'index':len(functions)}
roots=['sha256_init','keccak_init','ssz_init','mpt_init','u256_ws_init','secp256k1_init','bn254_init',
       'bls_precompiles_init','ripemd160_init','blake2_init','header_init','evm_init','fork_init']
seen=set();order=[];active=[]
def visit(name):
    assert name not in active,('recursive startup call graph',active,name)
    if name in seen:return
    active.append(name)
    for child in functions[name]['calls']:visit(child)
    active.pop();seen.add(name);order.append(name)
extra_roots=['decode_host_input','serialize_result','output_write']
for name in roots+extra_roots:visit(name)

def module(name):return ''.join(part[0].upper()+part[1:] for part in name.split('_'))
folder=ROOT/'submission/InitECandidate/Solver/Input/CurrentStartup'
folder.mkdir(exist_ok=True)
header='''namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
'''
code='''import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry

'''+header+'''
namespace Code
inductive Routine where
'''+''.join('  | '+n+'\n' for n in order)+'''
def declaration : Routine → Decl (BitVec 64)
'''+''.join(f'  | .{n} => Guest.Software.guestFn_{n}\n' for n in order)+'''
def entry (routine : Routine) := GasBudget.OriginalCodeEnvironment.originalEntry (declaration routine)
def name : Routine → MlS
'''+''.join(f'  | .{n} => ofString "{n}"\n' for n in order)+'''
def formals (routine : Routine) := (entry routine).2.1
def body (routine : Routine) := (entry routine).2.2.1
def shape (routine : Routine) := (entry routine).2.2.2

set_option maxRecDepth 100000 in
theorem installed (code) (installed : OriginalCode.Installed code) (routine : Routine) :
    code.lookup (name routine) = some (formals routine, body routine, shape routine) := by
  cases routine with
'''+''.join(f'  | {n} => exact OriginalCode.indexed code installed {functions[n]["index"]} (entry .{n}) (by rfl)\n' for n in order)+'''
end Code
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.Code.installed
'''
(folder/'Code.lean').write_text(code)
(folder/'Base.lean').write_text('''import InitECandidate.Solver.Input.CurrentStartup.Code
import InitECandidate.Solver.Input.GlobalByteEffects
import InitECandidate.Solver.Input.GlobalEffectsGlobalCall
import InitECandidate.Solver.Input.GlobalEffectsScoped

'''+header+'''
inductive Cursor where | scratch | frame

def key : Cursor → MlS
  | .scratch => ofString "scratch_ptr"
  | .frame => ofString "frame_mem_ptr"

end InitECandidate.Solver.Input.CurrentStartup
''')
constructors=Counter();assignments=Counter()
def proof(tree):
    if isinstance(tree,str):
        if tree=='Prog.skip':return '(GlobalEffects.skip (key cursor) code)'
        if tree=='Prog.break':return '(GlobalEffects.stopped (key cursor) code).1'
        if tree=='Prog.continue':return '(GlobalEffects.stopped (key cursor) code).2'
        raise ValueError(tree)
    vs=tree[1];head=vs[0];constructors[head]+=1
    common='(key cursor) code'
    if head=='Prog.seq':return f'(GlobalEffects.sequence {common} _ _\n  {proof(vs[1])}\n  {proof(vs[2])})'
    if head=='Prog.ite':return f'(GlobalEffects.conditional {common} _ _ _\n  {proof(vs[2])}\n  {proof(vs[3])})'
    if head=='Prog.dec':return f'(GlobalEffects.declared {common} _ _ _ _\n  {proof(vs[-1])})'
    if head=='Prog.while':return f'(GlobalEffects.loop {common} _ _\n  {proof(vs[-1])})'
    atomic={'Prog.store':('store','_ _'),'Prog.storeByte':('byte_store','_ _'),
            'Prog.return':('returned','_'),'Prog.raise':('raised','_ _'),
            'Prog.extCall':('external','_ _ _ _ _'),'Prog.shMemStore':('shared_store','_ _ _')}
    if head in atomic:
        lemma,args=atomic[head];return f'(GlobalEffects.{lemma} {common} {args})'
    if head=='Prog.shMemLoad':
        assert vs[2]=='VarKind.local',vs
        return f'(GlobalEffects.shared_load {common} _ _ _)'
    if head=='Prog.assign':
        if vs[1]=='VarKind.local':return f'(GlobalEffects.assign {common} _ _)'
        assert vs[1]=='VarKind.global',vs
        target=json.loads(vs[2]);assignments[target]+=1
        assert target not in ('scratch_ptr','frame_mem_ptr'),target
        return f'(GlobalEffects.global_other {common} _ _ (by cases cursor <;> decide))'
    if head in ('Prog.call','Prog.decCall'):
        callee=json.loads(vs[2] if head=='Prog.call' else vs[3])
        assert callee in seen,callee
        entry=f'(Code.installed code installed .{callee})'
        pure=f'({module(callee)}.preserves cursor code installed)'
        if head=='Prog.decCall':
            return (f'(GlobalEffects.scoped_body {common} _ _ (Code.name .{callee}) _ _ '
                    f'(Code.formals .{callee}) (Code.body .{callee}) (Code.shape .{callee})\n  {entry} {pure}\n  {proof(vs[-1])})')
        info=list(leaves(vs[1]))
        assert info.count('none')>=1,info
        if 'VarKind.global' in info:
            target=json.loads(info[info.index('VarKind.global')+2] if info[info.index('VarKind.global')+1]==',' else info[info.index('VarKind.global')+1])
            assert target not in ('scratch_ptr','frame_mem_ptr'),target
            return (f'(GlobalEffects.global_call_body {common} _ (Code.name .{callee}) _ '
                    f'(Code.formals .{callee}) (Code.body .{callee}) (Code.shape .{callee})\n'
                    f'  (by cases cursor <;> decide) {entry} {pure})')
        if vs[1]=='none':destination='none'
        elif 'VarKind.local' in info:destination='(some (some _))'
        else:destination='(some none)'
        return (f'(GlobalEffects.call_body {common} {destination} (Code.name .{callee}) _ '
                f'(Code.formals .{callee}) (Code.body .{callee}) (Code.shape .{callee})\n  {entry} {pure})')
    raise ValueError(head)

for name in order:
    imports=['InitECandidate.Solver.Input.CurrentStartup.Base']+[
        'InitECandidate.Solver.Input.CurrentStartup.'+module(child) for child in functions[name]['calls']]
    text=''.join('import '+p+'\n' for p in imports)+'\n'+header+f'''
namespace {module(name)}
-- Generated from actual fixed syntax. Lean must check this compositional proof.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .{name}) := by
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_{name}, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact {proof(functions[name]['tree'])}

end {module(name)}
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.{module(name)}.preserves
'''
    (folder/(module(name)+'.lean')).write_text(text)
report={'source':'Guest/SoftwareAst.lean','source_sha256':hashlib.sha256(source.encode()).hexdigest(),
        'roots':roots,'extra_roots':extra_roots,'order':order,'closure_functions':len(order),'syntax_constructors':dict(constructors),
        'global_assignment_names':dict(assignments),'acyclic_scan':True,'lean_build_required':True,
        'scope':'Generator/scanner output; not proof validation, timing or a whole-program bound.'}
(ROOT/'work/agent-notes/current-startup-globals-generation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('order','syntax_constructors')}))
aggregate=''.join('import InitECandidate.Solver.Input.CurrentStartup.'+module(n)+'\n' for n in roots+extra_roots)
aggregate+='\n'+header+'''
namespace Effects

theorem body_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) (routine : Code.Routine) :
    GlobalEffects.Preserves (key cursor) code (Code.body routine) := by
  cases routine with
'''+''.join(f'  | {n} => exact {module(n)}.preserves cursor code installed\n' for n in order)+'''
theorem call_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) (routine : Code.Routine)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves (key cursor) code (.call (GlobalEffects.callInfo destination) (Code.name routine) arguments) :=
  GlobalEffects.call_body (key cursor) code destination (Code.name routine) arguments
    (Code.formals routine) (Code.body routine) (Code.shape routine)
    (Code.installed code installed routine) (body_preserves cursor code installed routine)

end Effects
end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.Effects.body_preserves
#print axioms InitECandidate.Solver.Input.CurrentStartup.Effects.call_preserves
'''
(folder/'Effects.lean').write_text(aggregate)
report['generated_sources']=[{'path':str((folder/file).relative_to(ROOT)),
    'sha256':hashlib.sha256((folder/file).read_bytes()).hexdigest()}
    for file in ['Code.lean','Base.lean','Effects.lean']+[module(n)+'.lean' for n in order]]
(ROOT/'work/agent-notes/current-startup-globals-generation.json').write_text(json.dumps(report,indent=2)+'\n')
