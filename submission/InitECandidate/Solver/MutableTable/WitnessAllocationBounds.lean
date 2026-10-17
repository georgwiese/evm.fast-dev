import InitECandidate.Solver.MutableTable.WitnessCallResult

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Bounds on the actual selected allocation cursor, rather than an assumed
capacity. The selected power is retained by the real caller contract. -/
theorem ConstructorPairResult.heap_bounds (source right leftTarget rightTarget : PanSemStateFiniteExact 64 Guest.HostMemory)
    (leftArguments rightArguments : List (Flapjack.Pancake.PanLang.ExpHOL 64)) {records table count : Nat}
    (observation : DictionaryObservation records table count) (sliceFor : BitVec 64 → Graph.Slice) (scratch : BitVec 64)
    (maximum : Nat) (region safe : BitVec 64 → Prop)
    (result : ConstructorPairResult source right leftTarget rightTarget leftArguments rightArguments observation sliceFor scratch maximum region safe) :
    2701131776≤observation.heapEnd ∧ observation.heapEnd%8=0 ∧
      observation.heapEnd≤table+72+57*(4*count+4)+7 ∧ observation.heapEnd≤33806089496 := by
  have ready:=result.dictionary.ready
  have lower:=ready.recordsLower
  have before:=ready.recordsBefore
  have aligned:=ready.tableAligned
  have padded:=ready.padded
  have capacity:=result.capacityBound
  have padding:=Constructor.padding_bound (2^observation.bits)
  refine ⟨?_,?_,?_,ready.fits⟩
  · change 2701131776≤observation.plan.table+72+57*observation.plan.capacity+observation.plan.padding
    omega
  · change (observation.plan.table+72+57*observation.plan.capacity+observation.plan.padding)%8=0
    omega
  · change table+72+57*(2^observation.bits)+Constructor.padding (2^observation.bits)≤table+72+57*(4*count+4)+7
    omega

theorem ConstructorPairResult.heap_words (source right leftTarget rightTarget : PanSemStateFiniteExact 64 Guest.HostMemory)
    (leftArguments rightArguments : List (Flapjack.Pancake.PanLang.ExpHOL 64)) {records table count : Nat}
    (observation : DictionaryObservation records table count) (sliceFor : BitVec 64 → Graph.Slice) (scratch : BitVec 64)
    (maximum : Nat) (region safe : BitVec 64 → Prop)
    (result : ConstructorPairResult source right leftTarget rightTarget leftArguments rightArguments observation sliceFor scratch maximum region safe) :
    leftTarget.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 observation.heapEnd))) ∧
      rightTarget.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 observation.heapEnd))) := by
  have leftGlobals:=congrArg (fun state=>state.globals) result.leftControl
  have rightGlobals:=congrArg (fun state=>state.globals) result.rightControl
  change leftTarget.globals=source.globals.update _ at leftGlobals
  change rightTarget.globals=right.globals.update _ at rightGlobals
  constructor
  · rw [leftGlobals];simp [HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [rightGlobals];simp [HolFiniteMapExact.lookup_update,FUPDATE]

/-- A deliberately generous frontend cursor bound suffices for both witness
allocations at the maximum encoded input size. Establishing that cursor bound
from startup/decoding/header execution remains a separate obligation. -/
theorem two_map_room (table bytes nodeCount codeCount : Nat)
    (inputBound : bytes≤134217712) (counts : nodeCount+codeCount≤bytes/4)
    (cursorBound : table≤2701131776+128*bytes+1048576) :
    table+72+57*(4*nodeCount+4)+7+72+57*(4*codeCount+4)+7≤33806089496 := by
  omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.ConstructorPairResult.heap_bounds
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.ConstructorPairResult.heap_words
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.two_map_room
