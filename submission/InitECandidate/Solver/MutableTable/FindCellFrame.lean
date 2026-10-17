import InitECandidate.Solver.MutableTable.FindChain32

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack PanSemStateFiniteExact

/-- Actual used-byte reading depends only on its mapped aligned cell and
byte order; the rest of the memory may change. -/
theorem usedByte_of_cell (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64)
    (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be)
    (memory : source.memory (panByteAlignHOL (width := 64) (p.used + index)) = target.memory (panByteAlignHOL (width := 64) (p.used + index))) :
    usedByte source p index = usedByte target p index := by
  classical
  by_cases mapped : target.memaddrs (panByteAlignHOL (width := 64) (p.used + index))
  all_goals simp [usedByte, panMemLoadByteHOL, domain, endian, memory, mapped]

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.usedByte_of_cell
