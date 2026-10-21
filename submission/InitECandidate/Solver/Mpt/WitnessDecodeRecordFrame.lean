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

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.record_call_frame
