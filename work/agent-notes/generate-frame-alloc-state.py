#!/usr/bin/env python3
"""Emit additional allocator state-frame facts from its actual evaluator."""
from pathlib import Path
root=Path(__file__).resolve().parents[2]
entry=(root/'submission/InitECandidate/Solver/GuestWork/FrameAllocEntry.lean').read_text()
ns=entry[entry.index('namespace '):entry.index('/-- The actual successful')]
ns=ns.replace('set_option maxRecDepth','set_option linter.unusedSimpArgs false\nset_option maxRecDepth')
initial=entry[entry.index('  have roundedGuard'):entry.index('  simp [Named71')]
args=entry[entry.index('  simp [Named71')+8:entry.index('] at execution')]
fields='hmetadata hheap hstack hamount hreturn stackSafe metadataDomain metadataValue globalsEq pointerDomain pointerValue scratchDomain scratchValue saveDomain metadataNotSave scratchNotSave fits roundedFits'
s='import InitECandidate.Solver.GuestWork.FrameAllocAllClocks\n\n'+ns+'''
/-- The actual allocator preserves the caller's stack, metadata and heap-base
registers, code, domains and FFI on every non-timeout run satisfying its guards. -/
theorem preserved {C F : Type}
    (source post : StackSemStateFiniteExact 64 C F) (result : Option (StackSemResult 64))
    (metadata offset heap globals stack pointer scratch amount : BitVec 64)
    (returnLabel returnOffset : Nat)
    (valid : Ready source metadata offset heap globals stack pointer scratch amount returnLabel returnOffset)
    (run : evaluate (Named71.2, source) = (result, post))
    (notTimeout : result ≠ some .timeOut) :
    post.code = source.code ∧
    post.regs.lookup 24 = source.regs.lookup 24 ∧
    post.regs.lookup 25 = source.regs.lookup 25 ∧
    post.regs.lookup 26 = source.regs.lookup 26 ∧
    post.mdomain = source.mdomain ∧ post.ffi = source.ffi := by
  have enoughClock : 4 ≤ source.clock := by
    by_contra tooSmall
    have timedOut := small_timeout source metadata offset heap globals stack pointer scratch amount
      returnLabel returnOffset valid (by omega)
    rw [run] at timedOut
    exact notTimeout timedOut.1
  obtain ⟨FIELDS⟩ := valid
INITIAL
  simp [ARGS] at run
  rcases run with ⟨rfl, rfl⟩
  simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hstack, hmetadata, hheap, BitVec.sub_add_cancel]

end InitECandidate.Solver.GuestWork.FrameAllocEntry
#print axioms InitECandidate.Solver.GuestWork.FrameAllocEntry.preserved
'''.replace('FIELDS',', '.join(fields.split())).replace('INITIAL',initial.rstrip()).replace('ARGS',args)
(root/'submission/InitECandidate/Solver/GuestWork/FrameAllocState.lean').write_text(s)
