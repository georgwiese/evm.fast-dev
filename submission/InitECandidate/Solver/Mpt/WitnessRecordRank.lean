import InitECandidate.Solver.Mpt.WitnessRecordView
import InitECandidate.Solver.Mpt.WitnessRecordArena

namespace InitECandidate.Solver.Mpt.WitnessStackRank

theorem remaining_mono (first second : Nat) (stack : List Frame) (phase : Phase) (go : Bool) (bound : first≤second) :
    rank first stack phase go≤rank second stack phase go := by
  simp only [rank]
  omega

/-- Actual rounding may consume more than88bytes; any decrease of at least
one real record allowance still pays for the new pending frame and phase. -/
theorem push_decreased (remaining next : Nat) (stack : List Frame) (frame : Frame) (drop : next+1≤remaining) :
    rank next (frame::stack) .resolve true<rank remaining stack .decode true :=
  lt_of_le_of_lt (remaining_mono next (remaining-1) (frame::stack) .resolve true (by omega)) (push remaining (by omega) stack frame)

end InitECandidate.Solver.Mpt.WitnessStackRank

namespace InitECandidate.Solver.Mpt.WitnessRecord
open Flapjack PanSemStateFiniteExact

/-- The genuine original88-byte allocation supplies the resource decrease
used by the core push rank, with the same current cursor and live limit. -/
theorem allocation_rank_push (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (room : Arenas.Room .down cursor limit 88#64)
    (stack : List WitnessStackRank.Frame) (payload : Payload) :
    WitnessStackRank.rank (WitnessStackRank.recordsLeft (pointer cursor).toNat limit.toNat) (payload.frame::stack) .resolve true<
      WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) stack .decode true :=
  WitnessStackRank.push_decreased _ _ stack payload.frame (allowance_decreases source cursor limit arena room)

/-- Uniform initial potential for any materializer context whose real
cursor remains below the immutable database band. The actual arena lower
bound is used; the stronger first-root constants are not presumed later. -/
theorem initial_rank_upper (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616) :
    WitnessStackRank.rank (WitnessStackRank.recordsLeft cursor.toNat limit.toNat) [] .decode true≤6864962 := by
  have lower:=arena.lower
  simp only [WitnessStackRank.rank,WitnessStackRank.recordsLeft,WitnessStackRank.pending,WitnessStackRank.phaseWeight,
    List.map_nil,List.sum_nil,ite_true,Nat.add_zero]
  omega

end InitECandidate.Solver.Mpt.WitnessRecord

#print axioms InitECandidate.Solver.Mpt.WitnessStackRank.remaining_mono
#print axioms InitECandidate.Solver.Mpt.WitnessStackRank.push_decreased
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.allocation_rank_push
#print axioms InitECandidate.Solver.Mpt.WitnessRecord.initial_rank_upper
