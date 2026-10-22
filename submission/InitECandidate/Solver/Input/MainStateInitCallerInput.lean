import InitECandidate.Solver.Input.MainStateInitBoundary
import InitECandidate.Solver.Input.MainStateInitCallerLocals
import InitECandidate.Solver.MutableTable.WitnessBuildOutputFields

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessConstructors

/-- Actual older decoded storage and its separation from the reached
initializer allocation frontier. No future initializer result is included. -/
structure CallerInput (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) : Prop where
  memory : HashInput.Frame source current inputPointer.toNat (initialHeap root).toNat
  heap : ∃ heap,current.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ (initialHeap root).toNat≤heap.toNat

theorem caller_input (input : Guest.InputBlob) (source headerTarget nodeTarget codeTarget : PanSemStateFiniteExact 64 Guest.HostMemory)
    (headerRows root codeArray heap codeTable currentHeap : BitVec 64) (parent : ValueHOL 64)
    (headerReturned : HeaderReturn input source headerTarget headerRows root)
    (nodeReturned : MutableTable.WitnessBuild.Returned
      (RunAttempt.constructorEntry (parentSource source headerTarget input root) (countWord input) (hashArray input root) parent)
      nodeTarget (VarList.decodedArray (DecoderCall.witnessArray input) (nodeBytes input)) heap (nodeCount input) (nodeSlices input)
      2713714976#64 2713715176#64 2713717584#64)
    (codeReturned : MutableTable.WitnessBuild.Returned
      (RunAttempt.codeEntry (RunAttempt.constructorEntry (parentSource source headerTarget input root) (countWord input) (hashArray input root) parent) nodeTarget heap)
      codeTarget (VarList.decodedArray codeArray (codeBytes input)) codeTable (codeCount input) (codeSlices input)
      2713714976#64 2713715176#64 2713717584#64)
    (heapCell : codeTarget.globals.lookup (ofString "heap_ptr")=some (.val (.word currentHeap))) :
    CallerInput source (callerState input source headerTarget nodeTarget codeTarget root heap codeTable parent) root := by
  let ready:=RunAttempt.constructorEntry (parentSource source headerTarget input root) (countWord input) (hashArray input root) parent
  let codeSource:=RunAttempt.codeEntry ready nodeTarget heap
  obtain ⟨headerHeap,headerCell,headerBound,headerAligned,afterHashes⟩:=headerReturned.currentHeap
  have nodeEntry : headerTarget.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by
    have entry:=nodeReturned.entryHeap
    have parentGlobals : (parentSource source headerTarget input root).globals=headerTarget.globals:=rfl
    simpa [ready,RunAttempt.constructorEntry,putGlobal,RunAttempt.parentEntry,RunAttempt.countEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "block_hashes"≠ofString "heap_ptr" from by decide,
      show ofString "block_hashes_n"≠ofString "heap_ptr" from by decide,parentGlobals] using entry
  have sameHeap : headerHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (headerCell.symm.trans nodeEntry)))
  rw [sameHeap] at afterHashes
  have beforeHashes:=headerReturned.geometry.hsBefore
  change (initialHeap root).toNat+8*(countWord input).toNat+8≤(hashArray input root).toNat at beforeHashes
  change (hashArray input root).toNat+32*(countWord input).toNat+32≤heap.toNat at afterHashes
  have nodeLower : (initialHeap root).toNat≤heap.toNat:=by omega
  have nodeGrows:=nodeReturned.toNormal.heap_geometry ready nodeTarget _ heap _ _ _ _ codeTable codeReturned.entryHeap
  have codeGrows:=codeReturned.toNormal.heap_geometry codeSource codeTarget _ codeTable _ _ _ _ currentHeap heapCell
  have nodeFrame:=nodeReturned.toNormal.input_frame ready nodeTarget _ heap _ _ _ _ inputPointer.toNat (initialHeap root).toNat
    (by decide) (by decide) (by decide) nodeLower
  have codeFrame:=codeReturned.toNormal.input_frame codeSource codeTarget _ codeTable _ _ _ _ inputPointer.toNat (initialHeap root).toNat
    (by decide) (by decide) (by decide) (by omega)
  refine ⟨⟨?_⟩,⟨currentHeap,heapCell,by omega⟩⟩
  intro query lower upper
  exact (codeFrame.words query lower upper).trans
    ((nodeFrame.words query lower upper).trans (headerReturned.memory.words query lower upper))

theorem CallerInput.at_entry (source current target : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (input : CallerInput source current root) (same : LocalEffects.erase target=LocalEffects.erase current) :
    CallerInput source target root := by
  have memory:=LocalEffects.memory_of_erase current target same
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change target.globals=current.globals at globals
  obtain ⟨heap,cell,before⟩:=input.heap
  exact ⟨input.memory.of_memory source current target _ _ memory,heap,by rw [globals]; exact cell,before⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.caller_input
#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.CallerInput.at_entry
