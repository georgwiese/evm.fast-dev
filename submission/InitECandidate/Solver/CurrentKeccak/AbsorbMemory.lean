import InitECandidate.Solver.CurrentKeccak.AbsorbCost
import InitECandidate.Solver.CurrentKeccak.PermutationCall
import InitECandidate.Solver.Input.OperationResult
import InitECandidate.Solver.Input.MemoryNormal
import InitECandidate.Solver.Input.NormalWordDeclaration
import InitECandidate.Solver.Input.CopyAnyCost

namespace InitECandidate.Solver.CurrentKeccak.Absorb
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input Input.CounterFlow WitnessRadix WitnessRadix.QueryBranch

/-- An out-of-domain first input byte makes either actual lane expression fail.
This also covers the unaligned path's explicit eight-byte reconstruction. -/
private theorem input_word_unmapped
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (blk index : BitVec 64) (unaligned : Bool)
    (blockCell : source.locals.lookup (ofString "blk")=some (.val (.word blk)))
    (counter : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (outside : CopyAny.ordinaryEnd≤(blk+index).toNat) :
    eval source (inputWord unaligned)=none := by
  classical
  have addressRead : eval source (address "blk")=some (.val (.word (blk+index))) := by
    simp [eval,address,evalHOLExact,evalListHOLExact,toExact,localVar,blockCell,counter,
      valueIsWord,valueWord,wordOpHOL,wordOp]
  have wordAbsent : ¬source.memaddrs (blk+index) := by
    rw [domain]
    intro mapped
    have upper:=(CopyAny.ordinary_bounds _ mapped).2.1
    omega
  have byteAbsent : ¬source.memaddrs (panByteAlignHOL (width:=64) (blk+index)) := by
    rw [domain]
    intro mapped
    have upper:=CopyAny.ordinary_byte_upper _ mapped
    omega
  have byteFailure : eval source (byte [])=none := by
    simp only [eval] at addressRead ⊢
    rw [byte,evalHOLExact,addressRead]
    simp [panMemLoadByteHOL,toExact,byteAbsent]
  simp only [eval] at addressRead
  cases unaligned with
  | false=>
    simp only [inputWord,Bool.false_eq_true,↓reduceIte,eval,evalHOLExact,
      isWfShapeExactHOL,addressRead,memLoadHOLExact,toExact,wordAbsent]
  | true=>
    simp only [eval] at byteFailure ⊢
    simp only [inputWord,↓reduceIte,evalHOLExact,evalListHOLExact,byteFailure]

/-- A continuing actual lane has read its first input word or byte from the
fixed ordinary domain, regardless of the other lane values. -/
theorem lane_input_upper
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk index : BitVec 64) (unaligned : Bool)
    (cell : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (blockCell : source.locals.lookup (ofString "blk")=some (.val (.word blk)))
    (counter : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (run : evaluateHOLFiniteState source (laneBody unaligned)=(none,post)) :
    (blk+index).toNat<CopyAny.ordinaryEnd := by
  classical
  by_contra outside
  have failed:=input_word_unmapped source blk index unaligned blockCell counter domain (by omega)
  obtain ⟨middle,front,back⟩:=Input.sequence_none source post _ _ run
  have addressRead : eval source (address "stp")=some (.val (.word (stp+index))) := by
    simp [eval,address,evalHOLExact,evalListHOLExact,toExact,localVar,cell,counter,
      valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨value,memory,read,stored,endpoint⟩:=Input.store_at_normal source middle _ _ (stp+index) addressRead front
  simp only [eval] at failed read
  rw [evalHOLExact,evalListHOLExact,evalListHOLExact,failed,evalListHOLExact] at read
  cases first : evalHOLExact source.toExact (.load .one (address "stp")) <;> simp [first] at read

private theorem loop_input_upper
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64) (unaligned : Bool)
    (cell : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (blockCell : source.locals.lookup (ofString "blk")=some (.val (.word blk)))
    (counter : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (run : evaluateHOLFiniteState source (loop unaligned)=(none,post)) : blk.toNat<CopyAny.ordinaryEnd := by
  have read : eval source condition=some (.val (.word 1#64)) := by
    simp [eval,condition,localVar,evalHOLExact,toExact,counter,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess]
  obtain ⟨funded,middle,front,back,clock⟩:=Input.while_none_step source post (ofString "stp")
    condition (laneBody unaligned) (lane_safe unaligned) read run
  have upper:=lane_input_upper (decClockHOLFinite source) middle stp blk 0#64 unaligned cell blockCell counter domain front
  simpa only [BitVec.add_zero] using upper

/-- Normal block absorption has genuinely read the block's first byte.
No precondition on the block pointer or cached input length is assumed. -/
theorem body_input_upper
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk : BitVec 64)
    (cell : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (blockCell : source.locals.lookup (ofString "blk")=some (.val (.word blk)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    blk.toNat<CopyAny.ordinaryEnd := by
  rw [body_shape] at run
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_return_word source post "i" (.const 0#64) 0#64 _ value rfl run
  let entry:=QueryBranch.bind source "i" 0#64
  have entryCell : entry.locals.lookup (ofString "stp")=some (.val (.word stp)) :=
    (bind_lookup_other source "i" "stp" 0#64 (by decide)).trans cell
  have entryBlock : entry.locals.lookup (ofString "blk")=some (.val (.word blk)) :=
    (bind_lookup_other source "i" "blk" 0#64 (by decide)).trans blockCell
  have safe : LocalPrefix (ofString "stp") (.ite alignment (loop false) (loop true)) :=
    .ite _ (.loop _ (lane_safe false)) (.loop _ (lane_safe true))
  obtain ⟨middle,front,back⟩:=Input.sequence_returned entry inner _ _ value (safe.summary_full entry).2.1 continued
  have test : eval entry alignment=some (.val (.word (if blk &&& 7#64=0#64 then 1#64 else 0#64))) := by
    by_cases aligned : blk &&& 7#64=0#64
    all_goals simp [eval,alignment,evalHOLExact,evalListHOLExact,toExact,localVar,entryBlock,
      valueIsWord,valueWord,wordOpHOL,wordOp,AndOp.and,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,aligned]
  simp only [eval] at test
  rw [evaluateHOLFiniteState_ite,test] at front
  by_cases aligned : blk &&& 7#64=0#64
  · simp only [if_pos aligned,show (1#64 : BitVec 64)≠0#64 from by decide,↓reduceIte] at front
    exact loop_input_upper entry middle stp blk false entryCell entryBlock (bind_lookup_same _ _ _) domain front
  · simp only [if_neg aligned,↓reduceIte] at front
    exact loop_input_upper entry middle stp blk true entryCell entryBlock (bind_lookup_same _ _ _) domain front

private theorem loop_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp query : BitVec 64) (unaligned : Bool)
    (cell : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (counter : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (away : ∀ offset : Nat,offset<200 → offset%8=0 → query≠stp+BitVec.ofNat 64 offset)
    (run : evaluateHOLFiniteState source (loop unaligned)=(none,post)) : post.memory query=source.memory query := by
  let invariant:=fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>
    ∃ index : BitVec 64,state.locals.lookup (ofString "i")=some (.val (.word index)) ∧ index.toNat≤136 ∧ index.toNat%8=0 ∧
      state.locals.lookup (ofString "stp")=some (.val (.word stp))
  apply MemoryAt.loop_normal source.code (ofString "stp") condition (laneBody unaligned) query (fun current=>(lane_safe unaligned).summary_full current) invariant ?_
    source post rfl ⟨0#64,counter,by decide,by decide,cell⟩ run
  intro current installed ready observed actual nonzero funded target bodyRun
  obtain ⟨index,indexCell,bounded,aligned,stpCell⟩:=ready
  have small : index.toNat<9223372036854775808 := by omega
  have expected : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) condition=
      some (.val (.word (if index.toNat<136 then 1#64 else 0#64))) := by
    simp [condition,localVar,evalHOLFinite,evalHOLExact,toExact,indexCell,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL,Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,small]
  have active : index.toNat<136 := by
    apply Classical.byContradiction
    intro inactive
    rw [if_neg inactive] at expected
    have zero : observed=0#64 := by simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using actual.symm.trans expected
    exact nonzero zero
  have nextCell:=(lane_advance unaligned) (decClockHOLFinite current) target index indexCell bodyRun
  have number : (index+8#64).toNat=index.toNat+8 := by
    rw [BitVec.toNat_add_of_lt (by change index.toNat+8<2^64; omega)]
    rfl
  have safe:=(lane_safe unaligned).summary_full (decClockHOLFinite current)
  unfold LocalSummary at safe
  rw [bodyRun] at safe
  have targetStp:=(safe.1 rfl).trans stpCell
  have nextInvariant : invariant target := ⟨index+8#64,nextCell,by rw [number]; omega,by rw [number]; omega,targetStp⟩
  obtain ⟨middle,front,back⟩:=Input.sequence_none (decClockHOLFinite current) target _ _ bodyRun
  have addressRead : eval (decClockHOLFinite current) (address "stp")=some (.val (.word (stp+index))) := by
    simp [eval,address,decClockHOLFinite,decClockHOLExact,evalHOLExact,evalListHOLExact,toExact,localVar,indexCell,stpCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨value,memory,read,stored,endpoint⟩:=Input.store_at_normal (decClockHOLFinite current) middle _ _ (stp+index) addressRead front
  obtain ⟨word,rfl⟩:=Input.operation_word_result (decClockHOLFinite current) .xor _ value read
  have first:=Input.word_store_normal (decClockHOLFinite current) middle _ _ (stp+index) word addressRead read front
  have assignment:=Input.LocalEffects.assign middle.code (ofString "i") (.op .add [localVar "i",.const 8#64]) middle rfl
  change evaluateHOLFiniteState middle (.assign .local (ofString "i") (.op .add [localVar "i",.const 8#64]))=(none,target) at back
  rw [back] at assignment
  have memoryEq : target.memory query=current.memory query := by
    rw [congrFun (LocalEffects.memory_of_erase middle target assignment) query,first.2]
    exact if_neg (by simpa using away index.toNat (by omega) aligned)
  exact ⟨nextInvariant,memoryEq⟩

/-- A real absorbed block writes only the actual200-byte state region,
including the complete software permutation call. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp blk query : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (cell : source.locals.lookup (ofString "stp")=some (.val (.word stp)))
    (blockCell : source.locals.lookup (ofString "blk")=some (.val (.word blk)))
    (away : ∀ offset : Nat,offset<200 → offset%8=0 → query≠stp+BitVec.ofNat 64 offset)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  rw [body_shape] at run
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_return_word source post "i" (.const 0#64) 0#64 _ value rfl run
  let entry:=bind source "i" 0#64
  have entryCell : entry.locals.lookup (ofString "stp")=some (.val (.word stp)) := (bind_lookup_other source "i" "stp" 0#64 (by decide)).trans cell
  have entryBlock : entry.locals.lookup (ofString "blk")=some (.val (.word blk)) := (bind_lookup_other source "i" "blk" 0#64 (by decide)).trans blockCell
  have safe : LocalPrefix (ofString "stp") (.ite alignment (loop false) (loop true)) :=
    .ite _ (.loop _ (lane_safe false)) (.loop _ (lane_safe true))
  obtain ⟨middle,front,back⟩:=Input.sequence_returned entry inner _ _ value (safe.summary_full entry).2.1 continued
  have first : middle.memory query=entry.memory query := by
    have test : eval entry alignment=some (.val (.word (if blk &&& 7#64=0#64 then 1#64 else 0#64))) := by
      by_cases aligned : blk &&& 7#64=0#64
      all_goals simp [eval,alignment,evalHOLExact,evalListHOLExact,toExact,localVar,entryBlock,valueIsWord,valueWord,wordOpHOL,wordOp,AndOp.and,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL,aligned]
    simp only [eval] at test
    rw [evaluateHOLFiniteState_ite,test] at front
    by_cases aligned : blk &&& 7#64=0#64
    · simp only [if_pos aligned,show (1#64 : BitVec 64)≠0#64 from by decide,↓reduceIte] at front
      exact loop_memory entry middle stp query false entryCell (bind_lookup_same _ _ _) away front
    · simp only [if_neg aligned,↓reduceIte] at front
      exact loop_memory entry middle stp query true entryCell (bind_lookup_same _ _ _) away front
  have nextCell : middle.locals.lookup (ofString "stp")=some (.val (.word stp)) := by
    have kept:=(safe.summary_full entry).1
    rw [front] at kept
    exact (kept rfl).trans entryCell
  have nextInstalled : OriginalCode.Installed middle.code := by
    have same:=(evaluation_fields entry middle _ none front).2.2.2
    rw [same]
    exact installed
  obtain ⟨final,called,returned⟩:=Input.sequence_returned middle inner _ _ value
    ((LocalPrefix.call (key:=ofString "stp") none (ofString "keccak_f1600") [localVar "stp"] (by intro name impossible; cases impossible)).summary_full middle).2.1 back
  have args : evalListHOLFinite middle (h:=fun address=>Classical.propDecidable (middle.memaddrs address)) [localVar "stp"]=some [.val (.word stp)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,nextCell]
  have second:=Permutation.call_memory middle final stp query nextInstalled [localVar "stp"] args away called
  have last:=LocalEffects.returned final.code (.const 0#64) final rfl
  rw [returned] at last
  rw [endpoint]
  exact (congrFun (LocalEffects.memory_of_erase final inner last) query).trans (second.trans first)

end InitECandidate.Solver.CurrentKeccak.Absorb

#print axioms InitECandidate.Solver.CurrentKeccak.Absorb.body_memory

#print axioms InitECandidate.Solver.CurrentKeccak.Absorb.lane_input_upper
#print axioms InitECandidate.Solver.CurrentKeccak.Absorb.body_input_upper
