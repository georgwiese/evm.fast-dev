import InitECandidate.Solver.Input.PackBytesSuffix

namespace InitECandidate.Solver.Input.PackBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Whole unchanged pack_bytes at the actual input length and allocated
arena. The original copy, short padding and allocator caller are included;
every actual non-timeout failure pays only its real executed prefix. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor : BitVec 64) (n : Nat)
    (small : n≤134217728) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (padded n)) (aligned : cursor.toNat%8=0)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤n/8+72 := by
  obtain ⟨paid,final,remaining,endpoint⟩ := allocation_prefix source post cursor n small count installed heap arena result run notTimeout
  let entry := buffered source cursor n
  have fields := buffered_fields source cursor n
  have pEntry := (buffered_other source cursor n "p" (by decide) (by decide)).trans pointer
  have nEntry := (buffered_other source cursor n "n" (by decide) (by decide)).trans count
  have price := buffer_cost entry p cursor n small installed domain pEntry fields.1 nEntry fields.2.1 inputArena arena aligned
  rw [remaining] at price
  change entry.clock-final.clock≤n/8+71 at price
  have monotone := evaluateHOLFiniteState_clock_le entry afterBuffer
  rw [remaining] at monotone
  change final.clock≤entry.clock at monotone
  have clock : entry.clock=source.clock-1 := fields.2.2.1
  have endpointClock : post.clock=final.clock := by rw [endpoint]; rfl
  rw [endpointClock]
  omega

end InitECandidate.Solver.Input.PackBytes

#print axioms InitECandidate.Solver.Input.PackBytes.body_cost
