import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame
import InitECandidate.Solver.Mpt.WitnessCoreLoopProgram

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The four data locals remain words in every phase, even when their
values are inactive until a later real assignment. Mode/top/go are
retained separately by the physical control invariant. -/
structure DataWords (source : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  pointer : ∃ word,source.locals.lookup (ofString "cur_p")=some (.val (.word word))
  length : ∃ word,source.locals.lookup (ofString "cur_n")=some (.val (.word word))
  result : ∃ word,source.locals.lookup (ofString "result")=some (.val (.word word))
  slot : ∃ word,source.locals.lookup (ofString "slot")=some (.val (.word word))

/-- Real decode/resolve work preserves the witness-database prefix below
its incoming heap, while resolver HASH stores modify separate above-heap scratch. -/
structure DatabaseFrame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) : Prop where
  domain : post.memaddrs=source.memaddrs
  endian : post.be=source.be
  code : post.code=source.code
  memory : ∀ query : BitVec 64,query.toNat<heap.toNat→ post.memory query=source.memory query

theorem DatabaseFrame.of_decode (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64)
    (frame : WitnessDecode.LiveFrame source post heap cursor limit) :
    DatabaseFrame source post heap :=
  ⟨frame.domain,frame.endian,frame.code,frame.memoryBefore⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.DatabaseFrame.of_decode
