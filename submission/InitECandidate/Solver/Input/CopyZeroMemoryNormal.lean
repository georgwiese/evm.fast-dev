import InitECandidate.Solver.Input.MemoryNormal
import InitECandidate.Solver.WitnessRadix.CopyNormalCall
import InitECandidate.Solver.WitnessRadix.CopyGeneralCost
import InitECandidate.Solver.WitnessRadix.ZeroNormal
import InitECandidate.Solver.WitnessRadix.ZeroCost

namespace InitECandidate.Solver.Input.MemoryAt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- A genuine normal original memcpy preserves every word outside both
literal and backing-word destinations. No copy-output oracle is assumed. -/
theorem copy_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (src dst query : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (CopyGeneral.values dst src length))
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (inputArena : AllocatedBytes.Arena src length) (outArena : AllocatedBytes.Arena dst length)
    (away : CopyGeneral.Away dst query length)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memcpy") arguments)=(none,post)) : post.memory query=source.memory query := by
  have exactRun := CopyGeneral.call_normal source post arguments src dst length args (CopyGeneral.original_code source.code installed)
    (AllocatedBytes.copy_mapped source src dst length domain inputArena outArena) (by have h:=outArena.upper; have l:=outArena.lower; omega) run
  rw [exactRun.2.2]
  exact CopyGeneral.call_memory_away source src dst query length away

/-- Normal aligned original memzero retains every word outside its actual
zeroed range, including zero-length calls and insufficient-clock prefixes
excluded by the same observed normal return. -/
theorem zero_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (arguments : List (ExpHOL 64)) (dst query : BitVec 64) (length : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Zero.values dst length))
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (arena : AllocatedBytes.Arena dst length) (aligned : dst.toNat%8=0) (multiple : length%8=0)
    (away : ∀ offset<length,query≠byteAddress dst offset)
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "memzero") arguments)=(none,post)) : post.memory query=source.memory query := by
  have exactRun := Zero.call_normal source post arguments dst length args (Zero.original_code source.code installed)
    (by have h:=arena.upper; have l:=arena.lower; omega) multiple aligned
    (by intro offset inside divisible; exact AllocatedBytes.word_mapped source dst length offset domain arena (by omega) aligned divisible) run
  rw [exactRun.2]
  exact Zero.final_memory_away source.memory dst query length away

end InitECandidate.Solver.Input.MemoryAt

#print axioms InitECandidate.Solver.Input.MemoryAt.copy_normal
#print axioms InitECandidate.Solver.Input.MemoryAt.zero_normal
