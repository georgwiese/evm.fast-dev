#!/usr/bin/env python3
"""Generate normal-return host frames for actual Software startup; Lean must check them.

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
for name in roots:visit(name)
constructors=Counter()
def proof(tree):
    if isinstance(tree,str):
        if tree=='Prog.skip':return '(NormalHostEffects.skip code)'
        if tree=='Prog.break':return '(NormalHostEffects.stopped code).1'
        if tree=='Prog.continue':return '(NormalHostEffects.stopped code).2'
        raise ValueError(tree)
    vs=tree[1];head=vs[0];constructors[head]+=1
    if head=='Prog.seq':return f'(NormalHostEffects.sequence code _ _\n  {proof(vs[1])}\n  {proof(vs[2])})'
    if head=='Prog.ite':return f'(NormalHostEffects.conditional code _ _ _\n  {proof(vs[2])}\n  {proof(vs[3])})'
    if head=='Prog.dec':return f'(NormalHostEffects.declared code _ _ _ _\n  {proof(vs[-1])})'
    if head=='Prog.while':return f'(NormalHostEffects.loop code _ _\n  {proof(vs[-1])})'
    atomic={'Prog.store':('store','_ _'),'Prog.storeByte':('byte_store','_ _'),
            'Prog.return':('returned','_'),'Prog.raise':('raised','_ _'),
            'Prog.assign':('assign','_ _ _'),'Prog.primitive':('primitive','_ _ _')}
    if head in atomic:
        lemma,args=atomic[head];return f'(NormalHostEffects.{lemma} code {args})'
    if head in ('Prog.call','Prog.decCall'):
        callee=json.loads(vs[2] if head=='Prog.call' else vs[3])
        assert callee in seen,callee
        entry=f'(Code.installed code installed .{callee})'
        pure=f'({callee} code installed)'
        if head=='Prog.decCall':
            return (f'(NormalHostEffects.scoped_body code _ _ (Code.name .{callee}) _ _ '
                    f'(Code.formals .{callee}) (Code.body .{callee}) (Code.shape .{callee})\n  {entry} {pure}\n  {proof(vs[-1])})')
        info=list(leaves(vs[1]))
        assert info.count('none')>=1,info
        if vs[1]=='none':destination='none'
        elif 'VarKind.local' in info:destination='(some (some (.local, _)))'
        elif 'VarKind.global' in info:destination='(some (some (.global, _)))'
        else:destination='(some none)'
        return (f'(NormalHostEffects.call_body code {destination} (Code.name .{callee}) _ '
                f'(Code.formals .{callee}) (Code.body .{callee}) (Code.shape .{callee})\n  {entry} {pure})')
    raise ValueError(head)

text='''import InitECandidate.Solver.Input.CurrentStartup.Code
import InitECandidate.Solver.Input.NormalHostCall
import InitECandidate.Solver.Input.NormalHostLoop
import InitECandidate.Solver.Input.TrapNoReturn

namespace InitECandidate.Solver.Input.CurrentStartup.NormalHost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

-- Generated compositional proofs over actual fixed syntax. No helper return,
-- successful allocation, readable buffer or oracle behavior is assumed.
'''
for name in order:
    text+=f'''
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem {name} (code) (installed : OriginalCode.Installed code) :
    NormalHostEffects.Returning code (Code.body .{name}) := by
'''
    if name=='trap_with':
        text+='''  intro source codeEq value returned
  have same : Code.body .trap_with = Trap.body := by
    simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL, funDeclToHOL, Guest.Software.guestFn_trap_with, Trap.body]
  rw [same] at returned
  exact (Trap.never_returns source value returned).elim
'''
    else:
        text+=f'''  apply NormalHostEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_{name}, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact {proof(functions[name]['tree'])}
'''
text+='\nend InitECandidate.Solver.Input.CurrentStartup.NormalHost\n\n'
text+=''.join(f'#print axioms InitECandidate.Solver.Input.CurrentStartup.NormalHost.{name}\n' for name in order)
path=ROOT/'submission/InitECandidate/Solver/Input/CurrentStartup/NormalHost.lean'
path.write_text(text)
report={'source':'Guest/SoftwareAst.lean','source_sha256':hashlib.sha256(source.encode()).hexdigest(),
        'roots':roots,'order':order,'closure_functions':len(order),'syntax_constructors':dict(constructors),
        'acyclic_scan':True,'lean_build_required':True,
        'generated_source':str(path.relative_to(ROOT)), 'generated_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'scope':'Generator output only; host equality at actual returned bodies, not at terminal/exceptional bodies, and not a runtime bound.'}
(ROOT/'work/agent-notes/current-startup-normal-host-generation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('order','syntax_constructors','roots')}))
