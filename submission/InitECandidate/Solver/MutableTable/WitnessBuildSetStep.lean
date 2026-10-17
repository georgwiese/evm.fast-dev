import InitECandidate.Solver.MutableTable.WitnessBuildProgram
import InitECandidate.Solver.MutableTable.BuildHashFrame32

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual original witness-builder suffix after hashing: the real setter
call, duplicate/new-key invariant update and ordinal increment. It preserves
all earlier input/record memory and every nonlocal control/FFI field. -/
theorem after_hash_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (domain : source.memaddrs=InitE.ordinaryDomain)
    (scratch : BitVec 64) (count index : Nat) (input : List (Find.Key32×BitVec 64)) (logical : Find.Model32 (BitVec 64))
    (bits : Nat) (small : bits<64) (power : plan.capacity=2^bits)
    (built : Layout32.Built bits source plan scratch count input logical) (processed : input.length=index) (inside : index<plan.count)
    (locals : Locals source plan index) (key : Find.Key32) (words : Fin 4→BitVec 64)
    (global : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word scratch)))
    (aligned : scratch.toNat%8=0) (before : scratch.toNat+32≤plan.table) (little : source.be=false)
    (view : MemoryBytes.WordView source scratch words) (bytes : MemoryBytes.ByteView source scratch key)
    (hashCode : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (copyCode : source.code.lookup (ofString "memcpy")=some (Copy32.formals,Copy32.body,.one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw")=some (TableCall.formals,Insert.body,.one))
    (memeqCode : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (findCode : source.code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one))
    (setCode : source.code.lookup (ofString "htab_set")=some (TableCall.formals,Set.body,.one))
    (enough : 7*index+7≤source.clock) :
    ∃ slot nextCount paid target,slot<plan.capacity ∧ count≤nextCount ∧ nextCount≤count+1 ∧ paid≤7*index+7 ∧
      evaluateHOLFiniteState source afterHash=(none,target) ∧
      Layout32.Built bits target plan scratch nextCount (input++[(key,recordAddress plan index)]) (Placement.put logical slot key (recordAddress plan index)) ∧
      Locals target plan (index+1) ∧ KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source ∧
      target.clock=source.clock-paid ∧
      (∀ query,query.toNat<plan.table→target.memory query=source.memory query) ∧
      (∀ name : MlS,ofString "i"≠name→target.locals.lookup name=source.locals.lookup name) := by
  have args:=set_arguments source plan index locals scratch global
  obtain ⟨slot,nextCount,paid,memory,slotInside,countLower,countUpper,bound,callRun,next,kind⟩:=Layout32.set_build_call source plan ready domain scratch count input logical
    bits small power built (by omega) key (recordAddress plan index) words aligned before little view bytes hashCode copyCode insertCode memeqCode findCode setCode _ args
    (by simpa only [processed] using enough)
  let post:={source with memory:=memory,clock:=source.clock-paid}
  let target:=bind post "i" (BitVec.ofNat 64 (index+1))
  have read : eval post (addConst (localVar "i") 1#64)=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,post,locals.index,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  have advance:=StateSteps.assign_execute post "i" (addConst (localVar "i") 1#64) (BitVec.ofNat 64 index) (BitVec.ofNat 64 (index+1)) locals.index read
  have advancedLocals : Locals target plan (index+1) := by
    constructor
    · exact (bind_lookup_other _ "i" "t" _ (by decide)).trans locals.table
    · exact (bind_lookup_other _ "i" "slice_arr" _ (by decide)).trans locals.records
    · exact (bind_lookup_other _ "i" "n" _ (by decide)).trans locals.count
    · exact bind_lookup_same _ _ _
  have finalBuilt:=Layout32.built_fields post target plan bits scratch nextCount _ _ rfl rfl rfl next
  have run : evaluateHOLFiniteState source afterHash=(none,target) := by
    change evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htab_set") setArguments)=(none,post) at callRun
    rw [afterHash,StateSteps.next_sequence source post _ _ callRun (Nat.sub_le _ _)]
    exact advance
  refine ⟨slot,nextCount,paid,target,slotInside,countLower,countUpper,by omega,run,finalBuilt,advancedLocals,rfl,rfl,?_,?_⟩
  · intro query earlier
    change memory query=source.memory query
    rcases kind with ⟨rfl,same⟩|⟨rfl,same⟩
    · exact Layout32.update_earlier source.memory plan ready slot slotInside (recordAddress plan index) query earlier
    · have countInside : count<plan.capacity:=by have:=built.countBound;have:=ready.room;omega
      exact Layout32.result_earlier source.memory plan ready scratch slot count slotInside countInside (recordAddress plan index) query words earlier
  · intro name different
    simp [target,post,WitnessRadix.QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,different]

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.after_hash_step
