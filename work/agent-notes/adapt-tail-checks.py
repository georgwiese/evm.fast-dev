"""Reproduce the local adaptation of the fixed tail checks (no fixed-file edits)."""
from pathlib import Path
import re
src=Path('submission/InitECandidate/Proofs/BootstrapTailChecks.lean').read_text()
s=src.replace('import InitECandidate.Proofs.BootstrapStraightLine\nimport InitECandidate.Proofs.BootstrapTailMemory\nimport InitECandidate.Proofs.BootstrapCopyGuards','import InitECandidate.Solver.BootstrapChecks\nimport InitECandidate.Solver.BootstrapRegion')
s=s.replace('namespace InitECandidate.Proofs.BootstrapStraightLine','namespace InitECandidate.Solver.BootstrapTailChecks\nopen InitECandidate.Proofs.BootstrapStraightLine').replace('end InitECandidate.Proofs.BootstrapStraightLine','end InitECandidate.Solver.BootstrapTailChecks')
s=s.replace(' InitECandidate.Proofs.BootstrapCopyGuards','').replace('open InitECandidate.Proofs.BootstrapAsmComposition\n','')
pattern=r'private theorem tail_guard(\d+) : baselineMachineConfig\.progAddresses = [^\n]*\n    ffiEntryPcsDisjoint baselineMachineConfig [^\n]*? (\(riscvEnc [^\n]*\))\.length := by\n(.*?)(?=\nprivate|\n/--)'
def guard(m):
 n, enc, proof=m.groups(); state=f'(tailState{n} (copyState 4617))'
 proof=proof.replace('.symm, ?_⟩',', ?_, ?_⟩').replace('  apply bootstrap_ffi_disjoint\n','')
 return f'''private theorem tail_guard{n} : {state}.memDomain = bootstrapDomain ∧
    initialPc ≤ {state}.pc.toNat ∧
    {state}.pc.toNat + {enc}.length ≤ initialPc + 208 := by
'''+proof
s,count=re.subn(pattern,guard,s,flags=re.S)
assert count==32,count
s=s.replace('(domain : baselineMachineConfig.progAddresses = s.memDomain)','(domain : s.memDomain = bootstrapDomain)').replace('(ffi : ffiEntryPcsDisjoint baselineMachineConfig s (riscvEnc i).length)','(ffi : initialPc ≤ s.pc.toNat ∧ s.pc.toNat + (riscvEnc i).length ≤ initialPc + 208)')
a=s.index('private theorem trace_guards'); b=s.index('private theorem trace_thirty_two',a)
s=s[:a]+'''private theorem trace_guards {code s t} (h : TailCheckedTrace code s t) :
    InitECandidate.Solver.BootstrapRegion.Within bootstrapDomain initialPc (initialPc + 208) code s := by
  induction h with
  | nil => trivial
  | @cons s next final code i step domain ffi rest ih =>
    change s.memDomain = bootstrapDomain ∧ initialPc ≤ s.pc.toNat ∧
      s.pc.toNat + (riscvEnc i).length ≤ initialPc + 208 ∧
      InitECandidate.Solver.BootstrapRegion.Within bootstrapDomain initialPc (initialPc + 208)
        code (InitECandidate.Solver.WeightedTrace.after s i)
    have endpoint : InitECandidate.Solver.WeightedTrace.after s i = next := step.2.2.2.2.1
    rw [endpoint]
    exact ⟨domain, ffi.1, ffi.2, ih⟩

'''+s[b:]
s,count=re.subn(r'\(guard(\d+) : baselineMachineConfig\.progAddresses = s\d+\.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s\d+ \(riscvEnc i\d+\)\.length\)', lambda m:f'(guard{m[1]} : s{m[1]}.memDomain = bootstrapDomain ∧ initialPc ≤ s{m[1]}.pc.toNat ∧ s{m[1]}.pc.toNat + (riscvEnc i{m[1]}).length ≤ initialPc + 208)',s)
assert count==32,count
s=s.replace('EvaluatorGuards baselineMachineConfig','InitECandidate.Solver.BootstrapRegion.Within bootstrapDomain initialPc (initialPc + 208)')
s=s.replace('/-- A source trace carrying all ordinary evaluator guards. -/','/-- A source trace carrying static domain and PC-range facts. -/').replace('/-- All tail instructions execute ordinary target semantics in the compiler evaluator. -/','/-- Every tail instruction stays inside the startup code region. -/')
assert 'baselineMachineConfig' not in s
assert 'bootstrap_ffi_disjoint' not in s
s='''/- Adapted from the fixed Proofs/BootstrapTailChecks.lean. All original
ASM checks are retained; the compiler-configuration guards are factored into
closed domain/PC-range facts. No 47,000-module artifact proof is imported. -/
'''+s
s+='\n#print axioms InitECandidate.Solver.BootstrapTailChecks.tail_checked\n#print axioms InitECandidate.Solver.BootstrapTailChecks.tail_guards\n'
Path('submission/InitECandidate/Solver/BootstrapTailChecks.lean').write_text(s)
print('Adapted',len(s.splitlines()),'lines; 32 closed region facts')
