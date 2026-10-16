#!/usr/bin/env python3
"""Expose <= 16 transition witnesses in pinned encoder proofs.
Generated Lean remains subject to ordinary kernel checking; no proof reflection.
"""
from pathlib import Path
import re
root=Path(__file__).resolve().parents[2]
source=root/'.lake/packages/flapjack/Flapjack/RiscV/CorrectnessEncoding'
dest=root/'submission/InitECandidate/Solver/BoundedEncoder'
modules=['Div','LongMul','Rejected','AddCarry','AddOverflow','SubOverflow','JumpReg',
         *['Shift'+op+kind for op in ['Lsl','Lsr','Asr','Ror'] for kind in ['Register','Immediate']],
         'Shift','Jump/Near','Jump/Far','Jump','Call/Near','Call/Far','Call',
         'JumpCmp/NearReg','JumpCmp/NearRegTest','JumpCmp/NearImm','JumpCmp/Near',
         'JumpCmp/FarReg','JumpCmp/FarRegTest','JumpCmp/FarImm','JumpCmp']
old='Flapjack.RiscV.TargetProof'; new='InitECandidate.Solver.BoundedEncoder'
module_map={'Flapjack.RiscV.CorrectnessEncoding.'+m.replace('/','.'):new+'.'+m.replace('/','.') for m in modules}
for module in modules:
    text=(source/(module+'.lean')).read_text()
    text=re.sub(r'^import (\S+)$',lambda m:'import '+module_map.get(m[1],m[1]),text,flags=re.M)
    text=re.sub(r'^namespace '+re.escape(old)+r'(\S*)$',lambda m:'namespace '+new+m[1]+'\nopen '+old+' '+old+m[1],text,flags=re.M)
    text=text.replace('end '+old,'end '+new)
    text=text.replace('TargetProof.kinds',new+'.kinds').replace('TargetProof.nonzero',new+'.nonzero')
    text=text.replace('riscv_encoder_correct_','encoder_bounded_')
    text=text.replace('∃ n : Nat, ∀ env','∃ n : Nat, n + 1 ≤ 16 ∧ ∀ env')
    text=re.sub(r'^  refine ⟨([0-9]+),\s*\?_⟩$',r'  refine ⟨\1, by decide, ?_⟩',text,flags=re.M)
    text=text.replace('  refine ⟨is.length - 1, ?_⟩','  refine ⟨is.length - 1, by simp [is, riscvAst], ?_⟩')
    # Audit every public constructor, leaving private branching helpers internal.
    namespace=re.search(r'^namespace (\S+)',text,re.M)[1]
    names=re.findall(r'^theorem (encoder_bounded_\w+|near_case|far_case|near_reg_simple|near_\w+_case|far_\w+_case)\b',text,re.M)
    text+='\n'+''.join('#print axioms '+namespace+'.'+name+'\n' for name in names)
    path=dest/(module+'.lean'); path.parent.mkdir(parents=True,exist_ok=True); path.write_text(text)
print(f'Generated {len(modules)} modules under {dest.relative_to(root)}')
