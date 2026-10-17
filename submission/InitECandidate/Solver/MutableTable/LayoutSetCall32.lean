import InitECandidate.Solver.MutableTable.LayoutSet32

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
attribute [local instance] Classical.propDecidable

/-- The actual ignored-result original setter call restores caller locals,
extends the represented build history for new and duplicate keys, and pays
at most7*processed+7 source clocks, with no growth. -/
theorem set_build_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (keyPointer : BitVec 64) (count : Nat) (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits)
    (built : Built bits source plan keyPointer count input logical) (processed : input.length≤plan.count)
    (key : Find.Key32) (value : BitVec 64) (words : Fin 4→BitVec 64)
    (aligned : keyPointer.toNat%8=0) (before : keyPointer.toNat+32≤plan.table) (little : source.be=false)
    (view : MemoryBytes.WordView source keyPointer words) (bytes : MemoryBytes.ByteView source keyPointer key)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (copyCode : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw")=some (TableCall.formals,Insert.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (findCode : source.code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one))
    (setCode : source.code.lookup (ofString "htab_set")=some (TableCall.formals,Set.body,.one))
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some (TableCall.values (BitVec.ofNat 64 plan.table) keyPointer value)) (enough : 7*input.length+7≤source.clock) :
    ∃ index nextCount paid memory,index<plan.capacity ∧ count≤nextCount ∧ nextCount≤count+1 ∧ paid≤7*input.length+7 ∧
      evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") expressions)=
        (none,{source with memory:=memory,clock:=source.clock-paid}) ∧
      Built bits {source with memory:=memory,clock:=source.clock-paid} plan keyPointer nextCount
        (input++[(key,value)]) (Placement.put logical index key value) ∧
      ((memory=updateMemory source.memory plan index value ∧ nextCount=count) ∨
        (memory=resultMemory source.memory plan keyPointer index count value words ∧ nextCount=count+1)) := by
  classical
  obtain ⟨callee,called,tLocal,keyLocal,valueLocal⟩:=TableCall.environment source.code.lookup (ofString "htab_set") Set.body
    (BitVec.ofNat 64 plan.table) keyPointer value setCode
  let entry:=callEntryStateHOLFinite source callee
  have entryBuilt:=built_fields source entry plan bits keyPointer count input logical rfl rfl rfl built
  obtain ⟨index,nextCount,paid,memory,target,inside,countLower,countUpper,bound,run,frame,next,kind⟩:=set_build entry plan ready domain keyPointer count input logical
    bits small power entryBuilt processed key value words tLocal keyLocal valueLocal aligned before little
    (word_view_fields source entry keyPointer words rfl rfl view) (MemoryBytes.byteView_of_fields source entry rfl rfl rfl keyPointer key bytes)
    hashCode copyCode insertCode memeqCode findCode (by change 7*input.length+6≤source.clock-1;omega)
  have callerFrame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-1-paid}:=frame
  have actual:=ignored_memory_call source target (ofString "htab_set") .one expressions
    (TableCall.values (BitVec.ofNat 64 plan.table) keyPointer value) Set.body callee (.val (.word 0#64)) paid memory args called (by omega) run
    (by simp [shapeEqHOL,shapeOfHOLExact]) callerFrame
  let post:={source with memory:=memory,clock:=source.clock-(paid+1)}
  have memoryEq : target.memory=post.memory:=congrArg (fun s=>s.memory) callerFrame
  have domainEq : target.memaddrs=post.memaddrs:=congrArg (fun s=>s.memaddrs) callerFrame
  have endian : target.be=post.be:=congrArg (fun s=>s.be) callerFrame
  refine ⟨index,nextCount,paid+1,memory,inside,countLower,countUpper,by omega,?_,
    built_fields target post plan bits keyPointer nextCount _ _ memoryEq domainEq endian next,kind⟩
  have subtract : source.clock-1-paid=source.clock-(paid+1):=by omega
  simpa only [subtract] using actual

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.set_build_call
