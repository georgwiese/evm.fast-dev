import InitECandidate.Solver.Input.MainEvmTemporary
import InitECandidate.Solver.WitnessRadix.KeccakOriginalEnvironment

namespace InitECandidate.Solver.Input.Main.EvmInitialization
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def actions := [topicAction,systemAction,nullAction,emptyAction,keyAction,headerAction]
def template (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) := InitializerAllocations.template source cursor actions

theorem valid : ∀ action,action ∈ actions → InitializerAllocations.Valid action := by
  intro action member
  simp only [actions,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact actions_valid.1
  · exact actions_valid.2.1
  · exact actions_valid.2.2.1
  · exact actions_valid.2.2.2.1
  · exact actions_valid.2.2.2.2.1
  · exact actions_valid.2.2.2.2.2

private theorem control_from_context (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (context : InitializerAllocations.context target = InitializerAllocations.context source) (globals : target.globals = source.globals) :
    KeccakAbsorb.hashControl target = KeccakAbsorb.hashControl source := by
  have restored := congrArg (fun state => KeccakAbsorb.hashControl {state with globals := source.globals}) context
  change KeccakAbsorb.hashControl {target with globals := source.globals} = KeccakAbsorb.hashControl source at restored
  simpa only [← globals] using restored

theorem topic_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    KeccakAbsorb.hashControl (topicReady source cursor) = KeccakAbsorb.hashControl (InitializerAllocations.template source cursor [topicAction]) := by
  have globals : (topicReady source cursor).globals = (InitializerAllocations.template source cursor [topicAction]).globals := by
    apply HolFiniteMapExact.ext
    funext query
    by_cases heapKey : ofString "heap_ptr" = query
    all_goals by_cases topicKey : ofString "transfer_topic" = query
    all_goals simp [topicReady,InitializerAllocations.template,InitializerAllocations.reserve,topicAction,InitializerAllocations.constant,putGlobal,
      stringReleased,HeapScope.releasePost,stringWritten,InitializerBytes.written,stringAllocated,PersistentAlloc.post,marked,QueryBranch.bind,setVarHOLFinite,
      HolFiniteMapExact.update,FUPDATE,heapKey,topicKey]
  have context := (temporary_context source cursor).trans (InitializerAllocations.template_context source cursor [topicAction]).symm
  exact control_from_context _ _ context globals

theorem topic_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (topicReady source cursor).globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 (cursor + 32)))) := by
  have globals : (topicReady source cursor).globals = (InitializerAllocations.template source cursor [topicAction]).globals :=
    by
      have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) (topic_control source cursor)
      exact h
  rw [globals]
  simp [InitializerAllocations.template,InitializerAllocations.reserve,topicAction,InitializerAllocations.constant,putGlobal,HolFiniteMapExact.update,FUPDATE,show ofString "transfer_topic" ≠ ofString "heap_ptr" from by decide]

theorem topic_binding (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (topicReady source cursor).globals.lookup (ofString "transfer_topic") = some (.val (.word (BitVec.ofNat 64 cursor))) := by
  simp [topicReady,InitializerAllocations.template,InitializerAllocations.reserve,topicAction,InitializerAllocations.constant,putGlobal,HolFiniteMapExact.update,FUPDATE]

theorem string_binding (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) :
    (topicReady source cursor).locals.lookup (ofString "s") = some (.val (.word (BitVec.ofNat 64 cursor))) := by
  change (InitializerAllocations.template (stringReleased source cursor) cursor [topicAction]).locals.lookup _ = _
  rw [InitializerAllocations.template_locals_value]
  simp [stringReleased,HeapScope.releasePost,stringWritten,InitializerBytes.written,stringAllocated,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

theorem temporary_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (key : MlS)
    (notHeap : key ≠ ofString "heap_ptr") (notTopic : key ≠ ofString "transfer_topic") :
    (topicReady source cursor).globals.lookup key = source.globals.lookup key := by
  have globals : (topicReady source cursor).globals = (InitializerAllocations.template source cursor [topicAction]).globals :=
    by
      have h := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.globals) (topic_control source cursor)
      exact h
  rw [globals]
  exact InitializerAllocations.template_other source cursor [topicAction] key notHeap
    (by intro action member; have same := List.mem_singleton.mp member; subst action; exact notTopic)

theorem topic_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : Nat) (stp pad : BitVec 64)
    (installed : OriginalCode.Installed source.code) (environment : Keccak256.Environment source stp pad) :
    Keccak256.Environment (topicReady source cursor) stp pad := by
  have context := temporary_context source cursor
  exact Keccak256.original_environment (topicReady source cursor) stp pad
    (InitializerAllocations.installed_of_context source _ context installed)
    ((InitializerAllocations.domain_of_context source _ context).trans environment.domain)
    ((InitializerAllocations.oracle_of_context source _ context).trans environment.hashCode.oracleEq)
    ((temporary_other source cursor (ofString "keccak_st") (by decide) (by decide)).trans environment.stateGlobal)
    ((temporary_other source cursor (ofString "keccak_pad") (by decide) (by decide)).trans environment.scratchGlobal)

end InitECandidate.Solver.Input.Main.EvmInitialization

#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.valid
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.topic_control
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.topic_heap
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.topic_binding
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.string_binding
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.temporary_other
#print axioms InitECandidate.Solver.Input.Main.EvmInitialization.topic_environment
