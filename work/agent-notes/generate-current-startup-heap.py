#!/usr/bin/env python3
"""Generate actual Software normal heap-frontier proofs; Lean must check them.

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
roots=[n for n in roots if n!='evm_init']+['keccak256','heap_mark']
for name in roots:visit(name)
assert 'heap_release' not in seen
constructors=Counter()
def proof(tree):
    if isinstance(tree,str):
        if tree=='Prog.skip':return '(NormalHeapEffects.skip code)'
        if tree=='Prog.break':return '(NormalHeapEffects.stopped code).1'
        if tree=='Prog.continue':return '(NormalHeapEffects.stopped code).2'
        raise ValueError(tree)
    vs=tree[1];head=vs[0];constructors[head]+=1
    if head=='Prog.seq':return f'(NormalHeapEffects.sequence code _ _\n  {proof(vs[1])}\n  {proof(vs[2])})'
    if head=='Prog.ite':return f'(NormalHeapEffects.conditional code _ _ _\n  {proof(vs[2])}\n  {proof(vs[3])})'
    if head=='Prog.dec':return f'(NormalHeapEffects.declared code _ _ _ _\n  {proof(vs[-1])})'
    if head=='Prog.while':return f'(NormalHeapEffects.loop code _ _\n  {proof(vs[-1])})'
    atomic={'Prog.store':('store','_ _'),'Prog.storeByte':('byte_store','_ _'),
            'Prog.return':('returned','_'),'Prog.raise':('raised','_ _'),
            'Prog.shMemLoad':('shared_load','_ _ _')}
    if head in atomic:
        lemma,args=atomic[head];return f'(NormalHeapEffects.{lemma} code {args})'
    if head=='Prog.assign':
        if vs[1]=='VarKind.local':return '(NormalHeapEffects.assign code _ _)'
        assert vs[1]=='VarKind.global' and json.loads(vs[2])!='heap_ptr',vs
        return '(NormalHeapEffects.global_other code _ _ (by decide))'
    if head in ('Prog.call','Prog.decCall'):
        callee=json.loads(vs[2] if head=='Prog.call' else vs[3])
        assert callee in seen,callee
        entry=f'(Code.installed code installed .{callee})';pure=f'({callee} code installed)'
        if head=='Prog.decCall':
            return (f'(NormalHeapEffects.scoped_body code _ _ (Code.name .{callee}) _ _ '
                    f'(Code.formals .{callee}) (Code.body .{callee}) (Code.shape .{callee})\n  {entry} {pure}\n  {proof(vs[-1])})')
        info=list(leaves(vs[1]));assert info.count('none')>=1,info
        if vs[1]=='none':destination='none'
        elif 'VarKind.local' in info:destination='(some (some (.local, _)))'
        elif 'VarKind.global' in info:destination='(some (some (.global, _)))'
        else:destination='(some none)'
        return (f'(NormalHeapEffects.call_body code {destination} (Code.name .{callee}) _ '
                f'(Code.formals .{callee}) (Code.body .{callee}) (Code.shape .{callee})\n  {entry} {pure} (by unfold NormalHeapEffects.Safe; decide))')
    raise ValueError(head)
text='''import InitECandidate.Solver.Input.CurrentStartup.AllocationCursor
import InitECandidate.Solver.Input.NormalHeapCall
import InitECandidate.Solver.WitnessRadix.AllocationRequest

namespace InitECandidate.Solver.Input.CurrentStartup.HeapMonotone
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

-- Actual fixed-syntax proofs. The release operation is deliberately excluded;
-- its actual saved mark must be tracked in the EVM initializer separately.
'''
for name in order:
    text+=f'''
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem {name} (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Returning code (Code.body .{name}) := by
'''
    if name=='trap_with':
        text+='''  intro source codeEq lower initial value returned
  have same : Code.body .trap_with = Trap.body := by
    simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL, funDeclToHOL, Guest.Software.guestFn_trap_with, Trap.body]
  rw [same] at returned
  exact (Trap.never_returns source value returned).elim
'''
    elif name=='alloc':
        text+='''  intro source codeEq lower initial value returned
  obtain ⟨pointer, cell, lowerBound, bounded, aligned⟩ := initial
  have same : Code.body .alloc = WitnessRadix.PersistentAlloc.body := by
    simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL, funDeclToHOL, Guest.Software.guestFn_alloc, WitnessRadix.PersistentAlloc.body]
  rw [same] at returned
  have actual : evaluateHOLFiniteState source WitnessRadix.PersistentAlloc.body =
      (some (.returned value), (evaluateHOLFiniteState source WitnessRadix.PersistentAlloc.body).2) := Prod.ext returned rfl
  have codeInstalled : OriginalCode.Installed source.code := by rw [codeEq]; exact installed
  obtain ⟨next, heap, monotone, upper, multiple⟩ := WitnessRadix.PersistentAlloc.monotone_return source _ pointer cell bounded
    (trap_entry source.code codeInstalled) value actual
  exact ⟨next, heap, Nat.le_trans lowerBound monotone, upper, multiple⟩
'''
    else:
        text+=f'''  apply NormalHeapEffects.Preserves.returning
  simp only [Code.body, Code.entry, Code.declaration, GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL, funDeclToHOL, Guest.Software.guestFn_{name}, progToHOL, expToHOL,
    shapeToHOL, List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact {proof(functions[name]['tree'])}
'''
text+='\nend InitECandidate.Solver.Input.CurrentStartup.HeapMonotone\n\n'
text+=''.join(f'#print axioms InitECandidate.Solver.Input.CurrentStartup.HeapMonotone.{name}\n' for name in order)
path=ROOT/'submission/InitECandidate/Solver/Input/CurrentStartup/HeapMonotone.lean';path.write_text(text)
report={'source':'Guest/SoftwareAst.lean','source_sha256':hashlib.sha256(source.encode()).hexdigest(),
        'roots':roots,'order':order,'closure_functions':len(order),'syntax_constructors':dict(constructors),
        'excluded':['evm_init','heap_release'],'generated_source':str(path.relative_to(ROOT)),'generated_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
        'scope':'Generated normal-return heap-frontier proof terms, not validation, runtime bounds or a claim that heap_release is monotone.'}
(ROOT/'work/agent-notes/current-startup-heap-generation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('order','syntax_constructors','roots')}))

# Separate actual EVM initializer context: ordinary prefix and suffix around
# the one real saved-mark release. The release gets no monotonicity contract.
def take_context(tree,count):
    if count==0:return 'Prog.skip'
    vs=tree[1];head=vs[0]
    assert head in ('Prog.seq','Prog.dec','Prog.decCall'),(count,head)
    index=2 if head=='Prog.seq' else len(vs)-1
    changed=list(vs);changed[index]=take_context(vs[index],count-1)
    return tree[0],changed
remaining=functions['evm_init']['tree']
for _ in range(35):
    vs=remaining[1];assert vs[0] in ('Prog.seq','Prog.dec','Prog.decCall')
    remaining=vs[2] if vs[0]=='Prog.seq' else vs[-1]
assert remaining[1][0]=='Prog.seq'
release=remaining[1][1]
assert release[1][0]=='Prog.call' and json.loads(release[1][2])=='heap_release'
prefix=take_context(functions['evm_init']['tree'],35)
suffix=remaining[1][2]
prefix_proof=proof(prefix);suffix_proof=proof(suffix)
for name in order:
    prefix_proof=prefix_proof.replace('('+name+' code installed)','(HeapMonotone.'+name+' code installed)')
    suffix_proof=suffix_proof.replace('('+name+' code installed)','(HeapMonotone.'+name+' code installed)')
text='''import InitECandidate.Solver.Input.CurrentStartup.HeapMonotone
import InitECandidate.Solver.Input.CurrentStartup.EvmHeapProgram

namespace InitECandidate.Solver.Input.CurrentStartup.EvmHeap
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

-- Generated fixed-syntax contexts; the intervening release is handled using
-- its actual saved mark. Lean checks both contexts against literal source.
'''
for lemma,program,expand,generated in [
    ('prefix_pure','CallPrefix.program actions .skip','actions, CallPrefix.cutAt, CallPrefix.program',prefix_proof),
    ('suffix_pure','afterRelease','afterRelease, tail, CallPrefix.cutAt',suffix_proof)]:
    text+=f'''
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem {lemma} (code) (installed : OriginalCode.Installed code) :
    NormalHeapEffects.Preserves code ({program}) := by
  simp only [{expand}, Code.body, Code.entry, Code.declaration,
    GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL,
    Guest.Software.guestFn_evm_init, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_some, Option.map_none]
  exact {generated}
'''
text+='\nend InitECandidate.Solver.Input.CurrentStartup.EvmHeap\n\n'
text+=''.join(f'#print axioms InitECandidate.Solver.Input.CurrentStartup.EvmHeap.{name}\n' for name in ['prefix_pure','suffix_pure'])
path=ROOT/'submission/InitECandidate/Solver/Input/CurrentStartup/EvmHeapBounds.lean';path.write_text(text)
report['evm_context_source']=str(path.relative_to(ROOT));report['evm_context_sha256']=hashlib.sha256(path.read_bytes()).hexdigest()
report['evm_context_actions_before_release']=35
(ROOT/'work/agent-notes/current-startup-heap-generation.json').write_text(json.dumps(report,indent=2)+'\n')
