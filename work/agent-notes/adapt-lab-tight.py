#!/usr/bin/env python3
"""Generate the mixed instruction/NOP-cost Lab simulation from checked local proofs.
Only the cost interface changes; source/target semantics and relations are retained.
Run generated modules through Lean before using them as evidence.
"""
from pathlib import Path
base=Path(__file__).resolve().parents[2]/'submission/InitECandidate/Solver'
out=base/'LabBoundTight'
out.mkdir(exist_ok=True)
for name in ['Common','Asm','Control','Cbw','ShareMem','CallFfi','Assembly']:
    s=(base/'LabBound'/f'{name}.lean').read_text()
    s=s.replace('InitECandidate.Solver.LabBound','InitECandidate.Solver.LabBoundTight')
    s=s.replace('InitECandidate.Solver.LabCost','InitECandidate.Solver.LabCostTight').replace('LabCost.', 'LabCostTight.')
    s=s.replace('bounded lines', 'bounded nops lines')
    # NOP contract goes between the general encoder contract and line layout.
    s=s.replace('EncoderBound.Contract mc.target bound → LineBound', 'EncoderBound.Contract mc.target bound → NopBound.PaddingContract mc.target → LineBound')
    s=s.replace('(bounded : EncoderBound.Contract mc.target bound) (lines', '(bounded : EncoderBound.Contract mc.target bound) (nops : NopBound.PaddingContract mc.target) (lines')
    s=s.replace('LabCostTight.stepNopOfLine s1.ffi hrel hec bound bounded', 'LabCostTight.stepNopOfLine s1.ffi hrel hec bound bounded nops')
    s=s.replace('LabCostTight.stepNopOfLineMem s1.ffi hrel hec bound bounded', 'LabCostTight.stepNopOfLineMem s1.ffi hrel hec bound bounded nops')
    if name=='Common':
        s=s.replace('bound * (limit + 1) + 2','bound + limit / 4 + 2')
        s=s.replace('  have h := Nat.le_mul_of_pos_right bound (show 0 < limit + 1 by omega)\n','')
        s=s.replace('bound * (count + 1) ≤ rate bound limit', 'bound + count / 4 ≤ rate bound limit')
        s=s.replace('  have h := Nat.mul_le_mul_left bound (Nat.add_le_add_right small 1)\n','')
        s=s.replace('/-! A bounded Lab-to-target simulation for static programs.', '/-! A mixed instruction/NOP-cost Lab-to-target simulation for static programs.')
    (out/f'{name}.lean').write_text(s)
s=(base/'LabBound.lean').read_text().replace('InitECandidate.Solver.LabBound','InitECandidate.Solver.LabBoundTight')
s=s.replace('(16 * (limit + 1) + 2)', '(16 + limit / 4 + 2)')
s=s.replace('  have encoder :', '''  have nops : NopBound.PaddingContract mc.target := by
    rw [target]
    exact NopBound.riscv_padding
  have encoder :''')
s=s.replace('    bounded lines static', '    bounded nops lines static')
(base/'LabBoundTight.lean').write_text(s)
s=(base/'LabBound/StaticTarget.lean').read_text().replace('InitECandidate.Solver.LabBound','InitECandidate.Solver.LabBoundTight')
s=s.replace('import InitECandidate.Solver.LabBoundTight.Layout','import InitECandidate.Solver.LabBound.StaticTarget')
a=s.index('theorem static_of_stateRel');b=s.index('theorem riscv_static_target',a)
s=s[:a]+s[b:]
s=s.replace('(16 * (limit + 1) + 2)', '(16 + limit / 4 + 2)').replace('(static_of_stateRel ', '(LabBound.static_of_stateRel ')
s=s.replace('#print axioms InitECandidate.Solver.LabBoundTight.static_of_stateRel\n','')
(out/'StaticTarget.lean').write_text(s)
s=(base/'LabBound/PaddedRiscV.lean').read_text().replace('InitECandidate.Solver.LabBound','InitECandidate.Solver.LabBoundTight')
s=s.replace('import InitECandidate.Solver.LabBoundTight.PaddedProgram','import InitECandidate.Solver.LabBound.PaddedProgram')
s=s.replace('namespace InitECandidate.Solver.LabBoundTight\n','namespace InitECandidate.Solver.LabBoundTight\nopen InitECandidate.Solver.LabBound (fixedPaddedProgram fixedPaddedProgram_layout)\n')
s=s.replace('402 * s1.clock','24 * s1.clock')
(out/'PaddedRiscV.lean').write_text(s)
