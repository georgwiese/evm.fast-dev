import InitECandidate.Solver.MutableTable.BuildInvariant32
import InitECandidate.Solver.MutableTable.TableCallEnvironment

namespace InitECandidate.Solver.MutableTable.Layout32
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
attribute [local instance] Classical.propDecidable

theorem built_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (bits : Nat) (keyPointer : BitVec 64) (count : Nat) (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (memory : source.memory=target.memory) (domain : source.memaddrs=target.memaddrs) (endian : source.be=target.be)
    (built : Built bits source plan keyPointer count input logical) : Built bits target plan keyPointer count input logical :=
  ⟨header_fields source target plan keyPointer count memory domain built.header,
    key_model_fields source target (parameters plan keyPointer) plan.capacity logical memory domain endian built.keys,
    value_model_fields source target _ plan.capacity logical memory domain built.values,built.trace,built.countBound⟩

/-- Actual ignored-result raw-insertion caller extends the checked build
history, restores caller locals and includes all call/body clocks. -/
theorem insert_build_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (keyPointer : BitVec 64) (count : Nat) (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits)
    (built : Built bits source plan keyPointer count input logical) (room : input.length<plan.capacity)
    (key : Find.Key32) (value : BitVec 64) (absent : lastValue key input=none) (words : Fin 4→BitVec 64)
    (aligned : keyPointer.toNat%8=0) (before : keyPointer.toNat+32≤plan.table) (little : source.be=false)
    (view : MemoryBytes.WordView source keyPointer words) (bytes : MemoryBytes.ByteView source keyPointer key)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (copyCode : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw")=some (TableCall.formals,Insert.body,.one))
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=
      some (TableCall.values (BitVec.ofNat 64 plan.table) keyPointer value)) (enough : input.length+4≤source.clock) :
    ∃ index paid,index<plan.capacity ∧ paid≤input.length+4 ∧
      evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_insert_raw") expressions)=
        (none,{source with memory:=resultMemory source.memory plan keyPointer index count value words,clock:=source.clock-paid}) ∧
      Built bits {source with memory:=resultMemory source.memory plan keyPointer index count value words,clock:=source.clock-paid}
        plan keyPointer (count+1) (input++[(key,value)]) (Placement.put logical index key value) := by
  classical
  obtain ⟨callee,called,tLocal,keyLocal,valueLocal⟩:=TableCall.environment source.code.lookup (ofString "htab_insert_raw") Insert.body
    (BitVec.ofNat 64 plan.table) keyPointer value insertCode
  let entry:=callEntryStateHOLFinite source callee
  have entryBuilt:=built_fields source entry plan bits keyPointer count input logical rfl rfl rfl built
  obtain ⟨index,paid,target,inside,bound,run,frame,nextBuilt⟩:=insert_build entry plan ready domain keyPointer count input logical bits small power entryBuilt room
    key value absent words tLocal keyLocal valueLocal aligned before little (word_view_fields source entry keyPointer words rfl rfl view)
    (MemoryBytes.byteView_of_fields source entry rfl rfl rfl keyPointer key bytes) hashCode copyCode (by change input.length+3≤source.clock-1;omega)
  let memory:=resultMemory source.memory plan keyPointer index count value words
  have callerFrame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-1-paid}:=frame
  have actual:=ignored_memory_call source target (ofString "htab_insert_raw") .one expressions
    (TableCall.values (BitVec.ofNat 64 plan.table) keyPointer value) Insert.body callee (.val (.word 0#64)) paid memory args called (by omega) run
    (by simp [shapeEqHOL,shapeOfHOLExact]) callerFrame
  have subtract : source.clock-1-paid=source.clock-(paid+1):=by omega
  let post:={source with memory:=memory,clock:=source.clock-(paid+1)}
  have memoryEq : target.memory=post.memory:=congrArg (fun s=>s.memory) callerFrame
  have domainEq : target.memaddrs=post.memaddrs:=congrArg (fun s=>s.memaddrs) callerFrame
  have endian : target.be=post.be:=congrArg (fun s=>s.be) callerFrame
  refine ⟨index,paid+1,inside,by omega,?_,built_fields target post plan bits keyPointer (count+1) (input++[(key,value)]) _ memoryEq domainEq endian nextBuilt⟩
  simpa only [subtract] using actual

end InitECandidate.Solver.MutableTable.Layout32

#print axioms InitECandidate.Solver.MutableTable.Layout32.insert_build_call
