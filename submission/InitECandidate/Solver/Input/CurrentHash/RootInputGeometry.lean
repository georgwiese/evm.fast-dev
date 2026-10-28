import InitECandidate.Solver.Input.CurrentHash.RootArguments

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

variable {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {blob si record rq root array ch cursor : BitVec 64} {length start size : Nat}

theorem State.header_count_bound (state : State input source blob si record rq root array ch cursor length start size) : headerCount input≤134217728 := by
  obtain ⟨requestStart,requestSize,counts,requests⟩ := state.data.requestImage
  have inside:=requests.inside
  rw [requests.startEq] at inside
  have bounded:=requests.inputBound
  unfold headerCount
  omega

/-- Both real source offsets and the quotient-sized root list fit the same
copied input. A zero count remains valid even without an ordered-offset premise. -/
theorem State.header_span (state : State input source blob si record rq root array ch cursor length start size) :
    18+Guest.GasLimit.le32 input 22+32*headerCount input≤input.length%2^64 := by
  have lengthEq:=state.data.payload.lengthEq
  have minimum:=state.data.payload.minimum
  have upper:=state.data.payload.sliceUpper
  obtain ⟨requestStart,requestSize,counts,requests⟩ := state.data.requestImage
  have inside:=requests.inside
  rw [requests.startEq] at inside
  unfold headerCount
  by_cases ordered : Guest.GasLimit.le32 input 22≤Guest.GasLimit.le32 input 58
  · omega
  · omega

theorem State.header_roots_arena (state : State input source blob si record rq root array ch cursor length start size) :
    AllocatedBytes.Arena (headerPointer input blob) (32*headerCount input) := by
  have arena := AllocatedBytes.Arena.subrange blob (input.length%2^64) (18+Guest.GasLimit.le32 input 22) (32*headerCount input) state.input_bounds.2.1 state.header_span
  have pointer : byteAddress blob (18+Guest.GasLimit.le32 input 22)=headerPointer input blob := by
    change blob+BitVec.ofNat 64 (18+Guest.GasLimit.le32 input 22)=blob+18#64+BitVec.ofNat 64 (Guest.GasLimit.le32 input 22)
    rw [BitVec.ofNat_add,←BitVec.add_assoc]
  rw [pointer] at arena
  exact arena

theorem State.header_copy_arena (state : State input source blob si record rq root array ch cursor length start size) : AllocatedBytes.Arena (blob+18#64+8#64) 32 := by
  have upper := (PayloadHash.offset_ranges state.data.payload state.input_bounds.1).1
  have minimum := state.data.payload.minimum
  have arena := AllocatedBytes.Arena.subrange blob (input.length%2^64) 26 32 state.input_bounds.2.1 (by omega)
  rw [BitVec.add_assoc]
  exact arena

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.header_count_bound
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.header_span
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.header_roots_arena
#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.header_copy_arena
