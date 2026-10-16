#!/usr/bin/env python3
"""Start quantitative static-code variants of the pinned Lab case proofs.
Generated files are ordinary Lean proofs and must be built before use.
"""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
source=root/'.lake/packages/flapjack/Flapjack/Compiler/Backend/LabToTarget/CompileCorrect'
dest=root/'submission/InitECandidate/Solver/LabBound'
modules=['Asm','Control','Cbw','ShareMem','CallFfi']
for module in modules:
    s=(source/(module+'.lean')).read_text()
    for dep in ['Asm','ShareMem']:
        s=s.replace('import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.'+dep,
                    'import InitECandidate.Solver.LabBound.'+dep)
    s='import InitECandidate.Solver.LabBound.Common\n'+s
    s=s.replace('namespace Flapjack.Compiler.Backend.LabToTarget','namespace InitECandidate.Solver.LabBound\nopen Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget\nopen InitECandidate.Solver\nvariable {bound limit : Nat}')
    s=s.replace('\nend Flapjack.Compiler.Backend.LabToTarget','\nend InitECandidate.Solver.LabBound')
    s=s.replace('holAligned_iff', 'Flapjack.holAligned_iff')
    s=s.replace('CompileCorrectFor S Q','BoundedCorrect S Q bound limit')
    s=s.replace('ms1 p ⟨','ms1 p bounded lines static ⟨')
    s=re.sub(r'obtain ⟨l, ms2, hl⟩ := (step(?:Nop)?OfLine(?:Mem)?) s1.ffi hrel hec',r'obtain ⟨l, ms2, small, hl⟩ := LabCost.\1 s1.ffi hrel hec bound bounded',s)
    s=re.sub(r'^( *)exact compileCorrect_step',lambda m:m[1]+'exact compileCorrect_step bounded lines static\n'+m[1]+'  (by first | exact small.trans (padded_le bound lines hpos)\n'+m[1]+'            | exact small.trans (Nat.le_trans (Nat.le_succ bound) (base_le bound limit)))\n'+m[1]+'  (by first | rfl | simpa only [incPc, decClock] using hcode)',s,flags=re.M)
    s=s.replace('    refine ⟨l, ms2, ?_⟩','    refine ⟨l, ms2, terminal_bound bound limit hclock small, ?_⟩')
    if module == 'ShareMem':
        s=s.replace('refine ⟨0, ms1, ?_⟩','refine ⟨0, ms1, by simpa using terminal_bound bound limit hclock (Nat.zero_le bound), ?_⟩')
        s=s.replace('obtain ⟨k, ms2, hk⟩ := ih','obtain ⟨k, ms2, upper, hk⟩ := ih')
        s=s.replace('hshare res _ s2 code2 labs _ _ p\n', 'hshare res { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer } s2 code2 labs _ _ p bounded lines static\n')
        s=s.replace('refine ⟨k, ms2, ?_⟩', 'refine ⟨k, ms2, ?_, ?_⟩\n    · simpa using recursive_bound bound limit hclock upper (by have := base_le bound limit; omega) (by decide : (1 : Nat) ≠ 0)')
    if module == 'CallFfi':
        s=s.replace('obtain ⟨k, ms3, hk⟩ := ih','obtain ⟨k, ms3, upper, hk⟩ := ih')
        s=s.replace('hcall res _ s2 code2 labs _ _ p\n','hcall res { shiftInterfer l mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer } s2 code2 labs _ _ p bounded lines static\n')
        s=s.replace('refine ⟨k + l, ms3, ?_⟩', 'refine ⟨k + l, ms3, ?_, ?_⟩\n    · have h := recursive_bound bound limit hclock upper (show l + 1 ≤ rate bound limit by have := base_le bound limit; omega) (by omega : l + 1 ≠ 0)\n      simpa using h')
    names=re.findall(r'^theorem (compileCorrect_\w+)',s,re.M)
    s+='\n'+''.join('#print axioms InitECandidate.Solver.LabBound.'+name+'\n' for name in names)
    (dest/(module+'.lean')).write_text(s)
