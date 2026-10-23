import InitECandidate.Solver.Input.CoreDecodeResumeNormal
import InitECandidate.Solver.Mpt.WitnessRecordPathBytes

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Resume the original core from a derived genuine decoder result.
Every result executes its actual terminal or push path. A push writes only
the real new record below the incoming cursor, so all preceding storage
protected by the whole decoder frame remains protected. -/
theorem core_decode_resume_nibbles_normal (source ready : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit previous oldResult oldSlot oldMode : BitVec 64) (value : ValueHOL 64)
    (arena : Rlp.Validation.Arena source cursor limit) (frame : Mpt.WitnessDecode.NormalFrame source ready heap cursor limit)
    (result : Mpt.WitnessDecode.NibbleResult ready db pointer length heap cursor limit value)
    (dCell : ready.locals.lookup (ofString "d")=some value)
    (topCell : ready.locals.lookup (ofString "top")=some (.val (.word previous)))
    (resultCell : ready.locals.lookup (ofString "result")=some (.val (.word oldResult)))
    (slotCell : ready.locals.lookup (ofString "slot")=some (.val (.word oldSlot)))
    (modeCell : ready.locals.lookup (ofString "mode")=some (.val (.word oldMode))) :
    ∃ next,evaluateHOLFiniteState ready Mpt.WitnessCore.afterDecode=(none,next) ∧
      Mpt.WitnessDecode.NormalFrame source next heap cursor limit ∧
      Mpt.WitnessDecode.NibbleResult next db pointer length heap cursor limit value ∧
      ((∃ node,value=.rStruct [.val (.word 0#64),.val (.word node)] ∧ next=Mpt.WitnessCore.delivered ready node) ∨
        ∃ data : Mpt.WitnessRecord.Description,
          value=.rStruct [.val (.word 1#64),.val (.word (Mpt.WitnessRecord.pointer cursor))] ∧ data.payload.Fresh ∧
          Mpt.WitnessRecord.View next (Mpt.WitnessRecord.pointer cursor) db data ∧
          next=Mpt.WitnessCore.pushed ready (Mpt.WitnessRecord.pointer cursor) previous data.payload) := by
  cases result with
  | empty scratch=>
    let next:=Mpt.WitnessCore.delivered ready 0#64
    have run:=Mpt.WitnessCore.after_decode_terminal ready 0#64 oldResult oldMode dCell resultCell modeCell
    have nextFrame:=frame.of_erase source next ready heap cursor limit rfl
    have nextScratch:=scratch.of_fields ready next cursor limit rfl rfl
    exact ⟨next,run,nextFrame,.empty nextScratch,Or.inl ⟨0#64,rfl,rfl⟩⟩
  | leaf node nibbles nibbleLength valuePointer valueLength finalHeap view freshPath freshNode scratch heapCell heapArena heapAligned nodeBefore pathBytes pathAligned pathBefore=>
    let next:=Mpt.WitnessCore.delivered ready node
    have run:=Mpt.WitnessCore.after_decode_terminal ready node oldResult oldMode dCell resultCell modeCell
    have nextFrame:=frame.of_erase source next ready heap cursor limit rfl
    have nextResult : Mpt.WitnessDecode.NibbleResult next db pointer length heap cursor limit (.rStruct [.val (.word 0#64),.val (.word node)]):=
      .leaf node nibbles nibbleLength valuePointer valueLength finalHeap (view.of_fields next rfl rfl) freshPath freshNode (scratch.of_fields ready next cursor limit rfl rfl) heapCell heapArena heapAligned nodeBefore
        (pathBytes.of_agreement ready.memory next.memory ready.memaddrs next.memaddrs ready.be next.be nibbles nibbleLength.toNat rfl rfl (by intros; rfl)) pathAligned pathBefore
    exact ⟨next,run,nextFrame,nextResult,Or.inl ⟨node,rfl,rfl⟩⟩
  | record data finalHeap view parentPointer parentLength before freshRows freshPayload fresh initial heapCell heapArena heapAligned scratch drop pathBytes=>
    let record:=Mpt.WitnessRecord.pointer cursor
    let next:=Mpt.WitnessCore.pushed ready record previous data.payload
    have run:=Mpt.WitnessCore.after_decode_push ready record db previous oldSlot oldMode data view dCell topCell slotCell modeCell
    have room : Arenas.Room .down cursor limit 88#64:=by
      change limit.toNat+88≤cursor.toNat
      omega
    have recordBounds:=Mpt.WitnessRecord.allocation_bounds source cursor limit arena room
    have recordBelow : record.toNat<cursor.toNat:=by
      have upper : record.toNat+88≤cursor.toNat:=recordBounds.2.2.1
      omega
    let linked : PanSemStateFiniteExact 64 Guest.HostMemory:={ready with memory:=StoreWord.put ready.memory record previous}
    have linkedFrame:=frame.store_below source ready heap cursor limit record previous recordBelow
    have nextFrame:=linkedFrame.of_erase source next linked heap cursor limit rfl
    have nextView:=Mpt.WitnessCore.pushed_view ready record db previous data view
    have linkedInitial:=initial.store_record ready record db previous data view
    have nextInitial:=linkedInitial.of_fields linked next data.payload rfl
    have nextResult : Mpt.WitnessDecode.NibbleResult next db pointer length heap cursor limit (.rStruct [.val (.word 1#64),.val (.word record)]):=
      .record data finalHeap nextView parentPointer parentLength before freshRows freshPayload fresh nextInitial heapCell heapArena heapAligned (scratch.of_fields ready next record limit rfl rfl) drop (pathBytes.pushed ready record db previous data view)
    exact ⟨next,run,nextFrame,nextResult,Or.inr ⟨data,rfl,fresh,nextView,rfl⟩⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_decode_resume_nibbles_normal
