import InitECandidate.Solver.Mpt.WitnessCoreReturnProgram
import InitECandidate.Solver.Mpt.WitnessRecordIntervalFrame
import InitECandidate.Solver.WitnessRadix.StoreWord
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def returnCacheState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child hash : BitVec 64) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  if hash=0#64 ∨ child=0#64 then source else {source with memory:=StoreWord.put source.memory (child+24#64) hash}

/-- The actual normalized bitwise conjunction only stores HASH24 when
both pending hash and result are nonzero. Mapping follows from current
nonnull-result ownership, not an assumption that the store succeeds. -/
theorem cache_return_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child hash : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (ownership : child=0#64 ∨ AllocatedBytes.Arena child 32 ∧ child.toNat%8=0)
    (hashCell : source.locals.lookup (ofString "hash")=some (.val (.word hash)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child))) :
    evaluateHOLFiniteState source cacheReturnHash=(none,returnCacheState source child hash) := by
  have zeroZero : (AndOp.and (0#64 : BitVec 64) (AndOp.and 0#64 18446744073709551615#64))=0#64:=by decide
  have zeroOne : (AndOp.and (0#64 : BitVec 64) (AndOp.and 1#64 18446744073709551615#64))=0#64:=by decide
  have oneZero : (AndOp.and (1#64 : BitVec 64) (AndOp.and 0#64 18446744073709551615#64))=0#64:=by decide
  have oneOne : (AndOp.and (1#64 : BitVec 64) (AndOp.and 1#64 18446744073709551615#64))=1#64:=by decide
  have choice : evaluateHOLFiniteState source cacheReturnHash=
      if hash=0#64 ∨ child=0#64 then (none,source) else evaluateHOLFiniteState source (writeAt "result" 24#64 (localVar "hash")):=by
    rw [cache_return_hash_shape,evaluateHOLFiniteState_ite]
    by_cases hashZero : hash=0#64 <;> by_cases childZero : child=0#64 <;>
      simp [cacheReturnTest,truthy,evalHOLExact,evalListHOLExact,localVar,toExact,hashCell,resultCell,hashZero,childZero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,valueIsWord,valueWord,wordOpHOL,wordOp,evaluateHOLFiniteState_skip,zeroZero,zeroOne,oneZero,oneOne]
  rw [choice]
  by_cases skipped : hash=0#64 ∨ child=0#64
  · rw [if_pos skipped,returnCacheState,if_pos skipped]
  · rw [if_neg skipped,returnCacheState,if_neg skipped]
    obtain ⟨nodeArena,aligned⟩ : AllocatedBytes.Arena child 32 ∧ child.toNat%8=0:=ownership.resolve_left (fun zero=>skipped (Or.inr zero))
    have mapped : source.memaddrs (child+24#64):=AllocatedBytes.word_mapped source child 32 24 domain nodeArena (by decide) aligned (by decide)
    have addressRead : eval source (.op .add [localVar "result",.const 24#64])=some (.val (.word (child+24#64))):=by
      simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,resultCell,valueIsWord,valueWord,wordOpHOL,wordOp]
    have hashRead : eval source (localVar "hash")=some (.val (.word hash)):=by simp [eval,evalHOLExact,localVar,toExact,hashCell]
    exact StoreWord.execute source _ _ _ _ addressRead hashRead mapped

/-- A returned child after the active frame's allocation frontier cannot
overwrite that frame, its earlier row array or stage data when HASH24 is
cached. This applies to every older ordered active frame as well. -/
theorem return_cache_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db child hash : BitVec 64)
    (data : WitnessRecord.Description) (view : WitnessRecord.View source record db data)
    (ownership : child=0#64 ∨ AllocatedBytes.Arena child 32 ∧ child.toNat%8=0)
    (separated : hash≠0#64→ child≠0#64→ 2713731432≤child.toNat ∧ data.BeforeHeap child.toNat) :
    WitnessRecord.View (returnCacheState source child hash) record db data := by
  unfold returnCacheState
  split
  · exact view
  · rename_i stored
    obtain ⟨nodeLower,before⟩:=separated (fun zero=>stored (Or.inl zero)) (fun zero=>stored (Or.inr zero))
    obtain ⟨nodeArena,aligned⟩ : AllocatedBytes.Arena child 32 ∧ child.toNat%8=0:=ownership.resolve_left (fun zero=>stored (Or.inr zero))
    have nodeUpper:=nodeArena.upper
    have number : (child+24#64).toNat=child.toNat+24:=byteAddress_toNat child 24 (by omega)
    have recordUpper:=view.ceiling
    apply view.interval_frame source {source with memory:=StoreWord.put source.memory (child+24#64) hash} record db data 0 child.toNat (Nat.zero_le _) (by omega)
      (Nat.zero_le _) before.1 (Nat.zero_le _) before.2 rfl
    intro query lower upper
    have away : query≠child+24#64:=by intro same; have numeric:=congrArg BitVec.toNat same; rw [number] at numeric; omega
    exact if_neg away

theorem return_cache_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child hash query : BitVec 64)
    (away : query≠child+24#64) : (returnCacheState source child hash).memory query=source.memory query := by
  unfold returnCacheState
  split
  · rfl
  · exact if_neg away

theorem after_return_hash_trace (source : PanSemStateFiniteExact 64 Guest.HostMemory) (child hash : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (ownership : child=0#64 ∨ AllocatedBytes.Arena child 32 ∧ child.toNat%8=0)
    (hashCell : source.locals.lookup (ofString "hash")=some (.val (.word hash)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child))) :
    evaluateHOLFiniteState source afterReturnHash=evaluateHOLFiniteState (returnCacheState source child hash) returnStages := by
  have clock : (returnCacheState source child hash).clock≤source.clock:=by unfold returnCacheState; split <;> exact Nat.le_refl _
  rw [after_return_hash_shape,StateSteps.next_sequence source _ _ _ (cache_return_execute source child hash domain ownership hashCell resultCell) clock]

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.cache_return_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_cache_view
#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_cache_memory
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_return_hash_trace
