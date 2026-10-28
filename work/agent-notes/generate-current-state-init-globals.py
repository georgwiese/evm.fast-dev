#!/usr/bin/env python3
"""Generate one shared global-frame proof for the fixed state_init call graph.

The scan is reproducible selection, not certification. Lean checks every actual
code entry and composed body/handler proof. --check never writes sources.
"""
from pathlib import Path
import hashlib,json,re,sys
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

seen=set();order=[];active=[]
def visit(name):
    assert name not in active,('recursive call graph',active,name)
    if name in seen:return
    active.append(name)
    for child in functions[name]['calls']:visit(child)
    active.pop();seen.add(name);order.append(name)
visit('state_init')

def unwrap(tree):
    while isinstance(tree,tuple) and tree[0]=='(' and len(tree[1])==1:tree=tree[1][0]
    return tree

def some(tree):
    tree=unwrap(tree)
    assert isinstance(tree,tuple) and tree[1][0]=='some',tree
    return unwrap(tree[1][1])

def pair(tree):
    parts=unwrap(tree)[1]
    assert len(parts)==3 and parts[1]==',',tree
    return parts[0],parts[2]

def destination(tree):
    if tree=='none':return None
    kind,name=pair(some(tree))
    return kind,json.loads(name)

writes=set()
for name in order:
    for node in nodes(functions[name]['tree']):
        vs=node[1]
        if not vs:continue
        if vs[0]=='Prog.assign' and vs[1]=='VarKind.global':writes.add(json.loads(vs[2]))
        if vs[0]=='Prog.call' and vs[1]!='none':
            dest,handler=pair(some(vs[1]));chosen=destination(dest)
            if chosen and chosen[0]=='VarKind.global':writes.add(chosen[1])
writes=sorted(writes)

header="""namespace InitECandidate.Solver.Mpt.StateInitGlobals
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
"""
out='import InitECandidate.Solver.Input.OriginalCode\nimport InitECandidate.Solver.Input.OriginalEntry\nimport InitECandidate.Solver.Input.GlobalEffectsAtoms\nimport InitECandidate.Solver.Input.GlobalByteEffects\nimport InitECandidate.Solver.Input.GlobalEffectsLoop\nimport InitECandidate.Solver.Input.GlobalEffectsCaught\nimport InitECandidate.Solver.Input.GlobalEffectsGlobalCall\n\n'+header
out+='\nnamespace Code\ninductive Routine where\n'+''.join('  | '+n+'\n' for n in order)
out+='\ndef declaration : Routine → Decl (BitVec 64)\n'+''.join(f'  | .{n} => Guest.Software.guestFn_{n}\n' for n in order)
out+='\ndef entry (routine : Routine) := GasBudget.OriginalCodeEnvironment.originalEntry (declaration routine)\ndef name : Routine → MlS\n'+''.join(f'  | .{n} => ofString "{n}"\n' for n in order)
out+='\ndef formals (routine : Routine) := (entry routine).2.1\ndef body (routine : Routine) := (entry routine).2.2.1\ndef shape (routine : Routine) := (entry routine).2.2.2\n'
out+='\nset_option maxRecDepth 100000 in\ntheorem installed (code) (installed : OriginalCode.Installed code) (routine : Routine) :\n    code.lookup (name routine)=some (formals routine,body routine,shape routine) := by\n  cases routine with\n'
out+=''.join(f'  | {n} => exact OriginalCode.indexed code installed {functions[n]["index"]} (entry .{n}) (by rfl)\n' for n in order)
out+='end Code\n\n/-- Actual global destinations in this fixed call graph, including handlers. -/\ndef changed : List MlS := ['+', '.join('ofString '+json.dumps(n) for n in writes)+']\n'

def proof(tree):
    common='key code'
    other='(by intro equal; apply safe; rw [equal]; decide)'
    if isinstance(tree,str):
        if tree=='Prog.skip':return '(GlobalEffects.skip key code)'
        if tree=='Prog.break':return '(GlobalEffects.stopped key code).1'
        if tree=='Prog.continue':return '(GlobalEffects.stopped key code).2'
        raise ValueError(tree)
    vs=tree[1];head=vs[0]
    if head=='Prog.seq':return f'(GlobalEffects.sequence {common} _ _\n  {proof(vs[1])}\n  {proof(vs[2])})'
    if head=='Prog.ite':return f'(GlobalEffects.conditional {common} _ _ _\n  {proof(vs[2])}\n  {proof(vs[3])})'
    if head=='Prog.dec':return f'(GlobalEffects.declared {common} _ _ _ _\n  {proof(vs[-1])})'
    if head=='Prog.while':return f'(GlobalEffects.loop {common} _ _\n  {proof(vs[-1])})'
    atomic={'Prog.store':('store','_ _'),'Prog.storeByte':('byte_store','_ _'),'Prog.return':('returned','_'),'Prog.raise':('raised','_ _'),'Prog.extCall':('external','_ _ _ _ _'),'Prog.shMemStore':('shared_store','_ _ _')}
    if head in atomic:
        lemma,args=atomic[head];return f'(GlobalEffects.{lemma} {common} {args})'
    if head=='Prog.shMemLoad':
        assert vs[2]=='VarKind.local',vs
        return f'(GlobalEffects.shared_load {common} _ _ _)'
    if head=='Prog.assign':
        if vs[1]=='VarKind.local':return f'(GlobalEffects.assign {common} _ _)'
        assert vs[1]=='VarKind.global' and json.loads(vs[2]) in writes,vs
        return f'(GlobalEffects.global_other {common} _ _ {other})'
    if head in ('Prog.call','Prog.decCall'):
        callee=json.loads(vs[2] if head=='Prog.call' else vs[3])
        entry=f'(Code.installed code installed .{callee})'
        pure=f'(preserves_{callee} key code installed safe)'
        formal=f'(Code.formals .{callee}) (Code.body .{callee}) (Code.shape .{callee})'
        function=f'(Code.name .{callee})'
        if head=='Prog.decCall':return f'(GlobalEffects.scoped_body {common} _ _ {function} _ _ {formal}\n  {entry} {pure}\n  {proof(vs[-1])})'
        if vs[1]=='none':return f'(GlobalEffects.call_body {common} none {function} _ {formal} {entry} {pure})'
        dest,handler=pair(some(vs[1]));chosen=destination(dest)
        if handler!='none':
            assert not chosen or chosen[0]=='VarKind.local',chosen
            parts=some(handler)[1]
            assert len(parts)==5 and parts[1]==parts[3]==',',parts
            identifier,parameter,handler_program=parts[0],parts[2],parts[4]
            slot='none' if not chosen else '(some _)'
            return f'(GlobalEffects.caught_destination {common} {slot} {function} _ {formal} _ _ _\n  {entry} {pure}\n  {proof(handler_program)})'
        if chosen and chosen[0]=='VarKind.global':return f'(GlobalEffects.global_call_body {common} _ {function} _ {formal} {other} {entry} {pure})'
        slot='(some (some _))' if chosen else '(some none)'
        return f'(GlobalEffects.call_body {common} {slot} {function} _ {formal} {entry} {pure})'
    raise ValueError(head)

for name in order:
    out+=f"""
-- Generated from unchanged actual syntax; Lean checks the same body/handlers.
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem preserves_{name} (key : MlS) (code) (installed : OriginalCode.Installed code) (safe : key∉changed) :
    GlobalEffects.Preserves key code (Code.body .{name}) := by
  simp only [Code.body,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
    declToHOL,funDeclToHOL,Guest.Software.guestFn_{name},progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_some,Option.map_none]
  exact {proof(functions[name]['tree'])}
"""
out+='\nend InitECandidate.Solver.Mpt.StateInitGlobals\n\n#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.Code.installed\n'
out+=''.join('#print axioms InitECandidate.Solver.Mpt.StateInitGlobals.preserves_'+n+'\n' for n in order)
path=ROOT/'submission/InitECandidate/Solver/Mpt/StateInitGlobals.lean'
report={'source':'Guest/SoftwareAst.lean','source_sha256':hashlib.sha256(source.encode()).hexdigest(),'root':'state_init','acyclic_functions':order,'changed_globals':writes,'generated_source':str(path.relative_to(ROOT)),'generated_sha256':hashlib.sha256(out.encode()).hexdigest(),'lean_build_required':True}
if '--check' in sys.argv:assert path.read_text()==out,'Generated source differs'
else:
    path.write_text(out)
    (ROOT/'work/agent-notes/current-state-init-globals-generation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'closure_functions':len(order),'changed_globals':writes,'source_lines':len(out.splitlines()),'check_only':'--check' in sys.argv}))
