#!/usr/bin/env python3
"""Generate actual Software request-hash global-effect proofs; Lean must check them.

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
roots=['htr_new_payload_request']
seen=set();order=[];active=[]
def visit(name):
    assert name not in active,('recursive startup call graph',active,name)
    if name in seen:return
    active.append(name)
    for child in functions[name]['calls']:visit(child)
    active.pop();seen.add(name);order.append(name)
extra_roots=[]
for name in roots+extra_roots:visit(name)

def module(name):return ''.join(part[0].upper()+part[1:] for part in name.split('_'))
folder=ROOT/'submission/InitECandidate/Solver/Input/CurrentHash'
folder.mkdir(exist_ok=True)
# Reuse the already checked startup helper bodies where the literal declarations overlap.
startup_code=(ROOT/'submission/InitECandidate/Solver/Input/CurrentStartup/Code.lean').read_text()
shared=set(re.findall(r'  \| \.(\w+) => Guest\.Software\.guestFn_',startup_code))
def provider(name):
    return ('InitECandidate.Solver.Input.CurrentHash.SharedEffects' if name in shared else
            'InitECandidate.Solver.Input.CurrentHash.'+module(name))
def theorem_owner(name):
    return ('SharedEffects.' if name in shared else '')+module(name)

header='''namespace InitECandidate.Solver.Input.CurrentHash
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
end InitECandidate.Solver.Input.CurrentHash

#print axioms InitECandidate.Solver.Input.CurrentHash.Code.installed
'''
(folder/'Code.lean').write_text(code)
(folder/'Base.lean').write_text('import InitECandidate.Solver.Input.CurrentHash.Code\nimport InitECandidate.Solver.Input.CurrentStartup.Base\n\nnamespace InitECandidate.Solver.Input.CurrentHash\nopen Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact\nopen Flapjack.Basis.Pure.MlString\n\n/-- Fixed globals retained by the actual request-hash closure on every outcome. -/\ninductive Cursor where | scratch | frame | offsets | lengthChunk | zeroHashes | keccakState | keccakPad\n\ndef key : Cursor → MlS\n  | .scratch => ofString "scratch_ptr"\n  | .frame => ofString "frame_mem_ptr"\n  | .offsets => ofString "ssz_offs"\n  | .lengthChunk => ofString "ssz_len_chunk"\n  | .zeroHashes => ofString "zero_hashes"\n  | .keccakState => ofString "keccak_st"\n  | .keccakPad => ofString "keccak_pad"\n\nend InitECandidate.Solver.Input.CurrentHash\n')
# Reuse checked startup effects for arena, SSZ and Keccak workspace keys.
shared_text = 'import InitECandidate.Solver.Input.CurrentHash.Base\nimport InitECandidate.Solver.Input.CurrentStartup.OffsetsFrame\n'
shared_text += ''.join('import InitECandidate.Solver.Input.CurrentStartup.'+module(n)+'\n' for n in order if n in shared)
shared_text += '\n'+header+'\nnamespace SharedEffects\n'
for n in order:
    if n not in shared: continue
    owner=module(n)
    shared_text += f'''
namespace {owner}
theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :
    GlobalEffects.Preserves (key cursor) code (Code.body .{n}) := by
  cases cursor with
  | scratch => exact CurrentStartup.{owner}.preserves .scratch code installed
  | frame => exact CurrentStartup.{owner}.preserves .frame code installed
  | offsets => exact CurrentStartup.OffsetsFrame.{n} code installed .offsets
  | lengthChunk => exact CurrentStartup.OffsetsFrame.{n} code installed .lengthChunk
  | zeroHashes => exact CurrentStartup.OffsetsFrame.{n} code installed .zeroHashes
  | keccakState => exact CurrentStartup.OffsetsFrame.{n} code installed .keccakState
  | keccakPad => exact CurrentStartup.OffsetsFrame.{n} code installed .keccakPad
end {owner}
'''
shared_text += '\nend SharedEffects\nend InitECandidate.Solver.Input.CurrentHash\n'
shared_text += ''.join('\n#print axioms InitECandidate.Solver.Input.CurrentHash.SharedEffects.'+module(n)+'.preserves\n' for n in order if n in shared)
(folder/'SharedEffects.lean').write_text(shared_text)
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
        assert target not in ('scratch_ptr','frame_mem_ptr','ssz_offs','ssz_len_chunk','zero_hashes','keccak_st','keccak_pad'),target
        return f'(GlobalEffects.global_other {common} _ _ (by cases cursor <;> decide))'
    if head in ('Prog.call','Prog.decCall'):
        callee=json.loads(vs[2] if head=='Prog.call' else vs[3])
        assert callee in seen,callee
        entry=f'(Code.installed code installed .{callee})'
        pure=f'({theorem_owner(callee)}.preserves cursor code installed)'
        if head=='Prog.decCall':
            return (f'(GlobalEffects.scoped_body {common} _ _ (Code.name .{callee}) _ _ '
                    f'(Code.formals .{callee}) (Code.body .{callee}) (Code.shape .{callee})\n  {entry} {pure}\n  {proof(vs[-1])})')
        info=list(leaves(vs[1]))
        assert info.count('none')>=1,info
        if 'VarKind.global' in info:
            target=json.loads(info[info.index('VarKind.global')+2] if info[info.index('VarKind.global')+1]==',' else info[info.index('VarKind.global')+1])
            assert target not in ('scratch_ptr','frame_mem_ptr','ssz_offs','ssz_len_chunk','zero_hashes','keccak_st','keccak_pad'),target
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
    if name in shared: continue
    if name == 'sha256_pair':
        # Kept as a compact handwritten application of checked StraightBody syntax.
        assert (folder/'Sha256Pair.lean').exists()
        continue
    imports=list(dict.fromkeys(['InitECandidate.Solver.Input.CurrentHash.Base']+[
        provider(child) for child in functions[name]['calls']]))
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
end InitECandidate.Solver.Input.CurrentHash

#print axioms InitECandidate.Solver.Input.CurrentHash.{module(name)}.preserves
'''
    read_only = {'ssz_fail', 'host_input_byte', 'host_input_le32', 'ssz_check_offsets', 'precheck_host_ssz_header'}
    if name == 'memzero' or name in read_only:
        signature = 'theorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code)'
        extra = '' if name == 'memzero' else ' (installed : OriginalCode.Installed code)'
        text=text.replace(signature, 'theorem any_key (selected : MlS) (code)'+extra)
        text=text.replace('(key cursor)', 'selected')
        for child in functions[name]['calls']:
            assert child in read_only, (name, child)
            text=text.replace(module(child)+'.preserves cursor code installed',
                              module(child)+'.any_key selected code installed')
        marker='\nend '+module(name)
        wrapper=f"\ntheorem preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) :\n    GlobalEffects.Preserves (key cursor) code (Code.body .{name}) :=\n  any_key (key cursor) code"+('' if name == 'memzero' else ' installed')+'\n'
        text=text.replace(marker, wrapper+marker)
        text+=f'\n#print axioms InitECandidate.Solver.Input.CurrentHash.{module(name)}.any_key\n'
    (folder/(module(name)+'.lean')).write_text(text)
report={'source':'Guest/SoftwareAst.lean','source_sha256':hashlib.sha256(source.encode()).hexdigest(),
        'roots':roots,'extra_roots':extra_roots,'order':order,'closure_functions':len(order),'syntax_constructors':dict(constructors),
        'global_assignment_names':dict(assignments),'reused_startup_functions':sorted(set(order)&shared),'acyclic_scan':True,'lean_build_required':True,
        'retained_handwritten_functions':['sha256_pair'],
        'preserved_globals':['scratch_ptr','frame_mem_ptr','ssz_offs','ssz_len_chunk','zero_hashes','keccak_st','keccak_pad'],
        'scope':'Generator/scanner output; not proof validation, timing or a whole-program bound.'}
(ROOT/'work/agent-notes/current-hash-globals-generation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ('order','syntax_constructors')}))
aggregate=''.join('import '+provider(n)+'\n' for n in roots+extra_roots)
aggregate+='\n'+header+'''
namespace Effects

theorem body_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) (routine : Code.Routine) :
    GlobalEffects.Preserves (key cursor) code (Code.body routine) := by
  cases routine with
'''+''.join(f'  | {n} => exact {theorem_owner(n)}.preserves cursor code installed\n' for n in order)+'''
theorem call_preserves (cursor : Cursor) (code) (installed : OriginalCode.Installed code) (routine : Code.Routine)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64)) :
    GlobalEffects.Preserves (key cursor) code (.call (GlobalEffects.callInfo destination) (Code.name routine) arguments) :=
  GlobalEffects.call_body (key cursor) code destination (Code.name routine) arguments
    (Code.formals routine) (Code.body routine) (Code.shape routine)
    (Code.installed code installed routine) (body_preserves cursor code installed routine)

end Effects
end InitECandidate.Solver.Input.CurrentHash

#print axioms InitECandidate.Solver.Input.CurrentHash.Effects.body_preserves
#print axioms InitECandidate.Solver.Input.CurrentHash.Effects.call_preserves
'''
(folder/'Effects.lean').write_text(aggregate)
report['generated_sources']=[{'path':str((folder/file).relative_to(ROOT)),
    'sha256':hashlib.sha256((folder/file).read_bytes()).hexdigest()}
    for file in ['Code.lean','Base.lean','SharedEffects.lean','Effects.lean']+[module(n)+'.lean' for n in order if n not in shared]]
(ROOT/'work/agent-notes/current-hash-globals-generation.json').write_text(json.dumps(report,indent=2)+'\n')
