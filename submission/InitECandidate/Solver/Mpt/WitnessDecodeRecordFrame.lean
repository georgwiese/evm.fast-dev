import InitECandidate.Solver.Mpt.WitnessDecodeRecordNormal
import InitECandidate.Solver.Rlp.ValidationWriteFrame

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual initialized record lies wholly below the incoming cursor.
Every older active record, input row and database cell above that cursor
survives. Only the scratch global changes, and the real caller costs one tick. -/
theorem record_call_frame (kind : RecordKind)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (words : String→BitVec 64) (arena : Rlp.Validation.Arena source cursor limit)
    (ready : ∀ field∈kind.fields words,field.value.Ready (bind source kind.name (WitnessRecord.pointer cursor)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source kind.call=(some (.returned value),target)) :
    Rlp.Validation.Above source target cursor.toNat ∧
      (∀ key,key≠ofString "scratch_ptr"→target.globals.lookup key=source.globals.lookup key) ∧
      target.clock=source.clock-1 := by
  obtain ⟨room,recordArena,nextArena,upper,decreases,valueEq,funded,targetEq⟩:=record_call_normal kind source target cursor limit words arena ready installed value normal
  have memory:=congrArg PanSemStateFiniteExact.memory targetEq
  change target.memory=WordWrites.write source.memory (LocalFields.writes (WitnessRecord.pointer cursor) (kind.fields words)) at memory
  have globals:=congrArg PanSemStateFiniteExact.globals targetEq
  change target.globals=(Arenas.post source .down cursor 88#64).globals at globals
  have clock:=congrArg PanSemStateFiniteExact.clock targetEq
  change target.clock=source.clock-1 at clock
  refine ⟨?_,?_,clock⟩
  · intro query below
    rw [memory]
    apply WordWrites.write_away
    intro member
    simp only [LocalFields.writes,List.map_map,Function.comp_def] at member
    obtain ⟨field,inFields,same⟩:=List.mem_map.mp member
    have geometry:=kind.geometry words field inFields
    have number:=byteAddress_toNat (WitnessRecord.pointer cursor) field.offset (by have bound:=recordArena.upper; omega)
    change (WitnessRecord.pointer cursor+BitVec.ofNat 64 field.offset).toNat=(WitnessRecord.pointer cursor).toNat+field.offset at number
    have numeric:=congrArg BitVec.toNat same
    rw [number] at numeric
    omega
  · intro key other
    rw [globals]
    simp [Arenas.post,Arenas.pointerName,HolFiniteMapExact.update,FUPDATE,Ne.symm other]

/-- Real record stores protect both sides of the live scratch interval:
the earlier persistent input/heap and every older pending frame above it. -/
theorem record_call_outside (kind : RecordKind)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (words : String→BitVec 64) (arena : Rlp.Validation.Arena source cursor limit)
    (ready : ∀ field∈kind.fields words,field.value.Ready (bind source kind.name (WitnessRecord.pointer cursor)))
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source kind.call=(some (.returned value),target)) :
    Rlp.Validation.Outside source target limit.toNat cursor.toNat := by
  obtain ⟨room,recordArena,nextArena,upper,decreases,valueEq,funded,targetEq⟩:=record_call_normal kind source target cursor limit words arena ready installed value normal
  have memory:=congrArg PanSemStateFiniteExact.memory targetEq
  change target.memory=WordWrites.write source.memory (LocalFields.writes (WitnessRecord.pointer cursor) (kind.fields words)) at memory
  have runtime:=congrArg Rlp.Validation.scratchMetadata targetEq
  change Rlp.Validation.scratchMetadata target=Rlp.Validation.scratchMetadata source at runtime
  obtain ⟨buffer,lower,inside,aligned,active⟩:=WitnessRecord.allocation_bounds source cursor limit arena room
  refine ⟨runtime,?_⟩
  intro query location
  rw [memory]
  apply WordWrites.write_away
  intro member
  simp only [LocalFields.writes,List.map_map,Function.comp_def] at member
  obtain ⟨field,inFields,same⟩:=List.mem_map.mp member
  have geometry:=kind.geometry words field inFields
  have number:=byteAddress_toNat (WitnessRecord.pointer cursor) field.offset (by have bound:=recordArena.upper; omega)
  change (WitnessRecord.pointer cursor+BitVec.ofNat 64 field.offset).toNat=(WitnessRecord.pointer cursor).toNat+field.offset at number
  have numeric:=congrArg BitVec.toNat same
  rw [number] at numeric
  rcases location with before|after <;> omega

/-- Actual pending-frame creation retains a live parser arena and spends
one whole record from its finite allowance. The range follows from the live
entry's real cursor globals; it is not an extra future-allocation premise. -/
theorem record_call_live (kind : RecordKind)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (words : String→BitVec 64) (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (ready : ∀ field∈kind.fields words,field.value.Ready (bind source kind.name (WitnessRecord.pointer cursor)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source kind.call=(some (.returned value),target)) :
    Rlp.LiveArena target ∧ Rlp.Validation.Arena target (WitnessRecord.pointer cursor) limit ∧
      value=.rStruct [.val (.word 1#64),.val (.word (WitnessRecord.pointer cursor))] ∧
      ((WitnessRecord.pointer cursor).toNat-limit.toNat)/88+1≤(cursor.toNat-limit.toNat)/88 ∧
      Rlp.Validation.Outside source target limit.toNat cursor.toNat := by
  obtain ⟨lower,upper⟩:=WitnessRecord.live_cursor_bounds live arena
  obtain ⟨room,recordArena,next,before,decreases,valueEq,funded,targetEq⟩:=record_call_normal kind source target cursor limit words arena ready live.code value normal
  have codeEq:=congrArg PanSemStateFiniteExact.code targetEq
  change target.code=source.code at codeEq
  have finalLive:=Rlp.LiveArena.of_validation next lower (by omega) (by rw [codeEq]; exact live.code)
  exact ⟨finalLive,next,valueEq,decreases,record_call_outside kind source target cursor limit words arena ready live.code value normal⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.record_call_frame

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.record_call_outside
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.record_call_live
