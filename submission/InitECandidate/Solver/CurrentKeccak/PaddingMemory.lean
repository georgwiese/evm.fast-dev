import InitECandidate.Solver.CurrentKeccak.MemoryFrame

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix WitnessRadix.QueryBranch

structure PaddingLocals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pointer index out : BitVec 64) (rem : Nat) : Prop where
  state : source.locals.lookup (ofString "stp")=some (.val (.word stp))
  pointer : source.locals.lookup (ofString "p")=some (.val (.word pointer))
  index : source.locals.lookup (ofString "i")=some (.val (.word index))
  out : source.locals.lookup (ofString "out")=some (.val (.word out))
  remainder : source.locals.lookup (ofString "rem")=some (.val (.word (BitVec.ofNat 64 rem)))

theorem PaddingLocals.after {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {stp pointer index out pad query : BitVec 64} {rem : Nat}
    (cells : PaddingLocals source stp pointer index out rem) (step : Frame source target stp pad query) : PaddingLocals target stp pointer index out rem :=
  ⟨step.cell _ _ cells.state,step.cell _ _ cells.pointer,step.cell _ _ cells.index,step.cell _ _ cells.out,step.cell _ _ cells.remainder⟩

/-- Real padding, final absorption and digest output preserve every word
outside the two workspace buffers and output. The short remainder and current
input extent must be derived from the actual preceding block-loop exit. -/
theorem padding_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad pointer index out query : BitVec 64) (rem : Nat)
    (environment : Environment source stp pad) (cells : PaddingLocals source stp pointer index out rem)
    (short : rem<136) (inputArena : AllocatedBytes.Arena (pointer+index) rem) (outArena : AllocatedBytes.Arena out 32)
    (stateAway : ∀ offset : Nat,offset<200 → offset%8=0 → query≠stp+BitVec.ofNat 64 offset)
    (padAway : CopyGeneral.Away pad query 136) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source paddingTail=(some (.returned value),post)) : post.memory query=source.memory query := by
  obtain ⟨zeroed,zeroRun,afterZero⟩:=Input.sequence_returned source post zeroPad _ value
    ((LocalPrefix.call (key:=ofString "p") none _ _ (by intro name impossible; cases impossible)).summary_full source).2.1 run
  have zeroArgs : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [Hash.pad,.const 136#64]=some (Zero.values pad 136) := by
    simp [Hash.pad,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,environment.padGlobal,Zero.values]
  have first:=zero_frame source zeroed stp pad pad query 136 environment _ zeroArgs environment.padArena environment.padAligned (by decide)
    (by intro offset inside; exact (padAway offset inside).1) zeroRun
  have cells1:=cells.after first
  obtain ⟨copied,copyRun,afterCopy⟩:=Input.sequence_returned zeroed post copyPad _ value
    ((LocalPrefix.call (key:=ofString "p") none _ _ (by intro name impossible; cases impossible)).summary_full zeroed).2.1 afterZero
  have copyArgs : evalListHOLFinite zeroed (h:=fun address=>Classical.propDecidable (zeroed.memaddrs address))
      [Hash.pad,.op .add [localVar "p",localVar "i"],localVar "rem"]=some (CopyGeneral.values pad (pointer+index) rem) := by
    simp [Hash.pad,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,first.environment.padGlobal,cells1.pointer,cells1.index,cells1.remainder,
      localVar,CopyGeneral.values,valueIsWord,valueWord,wordOpHOL,wordOp]
  have padRem : AllocatedBytes.Arena pad rem := ⟨environment.padArena.lower,by have h:=environment.padArena.upper; omega⟩
  have second:=copy_frame zeroed copied stp pad (pointer+index) pad query rem first.environment _ copyArgs inputArena padRem
    (by intro offset inside; exact padAway offset (by omega)) copyRun
  have cells2:=cells1.after second
  obtain ⟨marked,markRun,afterMark⟩:=Input.sequence_returned copied post padFirst _ value
    ((LocalPrefix.storeByte (key:=ofString "p") _ _).summary_full copied).2.1 afterCopy
  have markAddress : eval copied (.op .add [Hash.pad,localVar "rem"])=some (.val (.word (pad+BitVec.ofNat 64 rem))) := by
    simp [eval,Hash.pad,evalHOLExact,evalListHOLExact,toExact,second.environment.padGlobal,cells2.remainder,
      localVar,valueIsWord,valueWord,wordOpHOL,wordOp]
  have third:=byte_frame copied marked stp pad (pad+BitVec.ofNat 64 rem) query second.environment _ _ markAddress
    (padAway rem short).2 markRun
  have cells3:=cells2.after third
  obtain ⟨padded,lastRun,afterLast⟩:=Input.sequence_returned marked post padLast _ value
    ((LocalPrefix.storeByte (key:=ofString "p") _ _).summary_full marked).2.1 afterMark
  have lastAddress : eval marked padLastAddress=some (.val (.word (pad+135#64))) := by
    simp [eval,padLastAddress,Hash.pad,evalHOLExact,evalListHOLExact,toExact,third.environment.padGlobal,
      valueIsWord,valueWord,wordOpHOL,wordOp]
  have fourth:=byte_frame marked padded stp pad (pad+135#64) query third.environment _ _ lastAddress (padAway 135 (by decide)).2 lastRun
  have cells4:=cells3.after fourth
  obtain ⟨absorbed,absorbRun,afterAbsorb⟩:=Input.sequence_returned padded post absorbPad _ value
    ((LocalPrefix.call (key:=ofString "p") none _ _ (by intro name impossible; cases impossible)).summary_full padded).2.1 afterLast
  have absorbArgs : evalListHOLFinite padded (h:=fun address=>Classical.propDecidable (padded.memaddrs address)) [localVar "stp",Hash.pad]=some (Absorb.values stp pad) := by
    simp [Hash.pad,Absorb.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,cells4.state,fourth.environment.padGlobal]
  have fifth:=absorb_frame padded absorbed stp pad pad query fourth.environment _ absorbArgs stateAway absorbRun
  have cells5:=cells4.after fifth
  have safe : LocalPrefix (ofString "p") outProgram := .ite _
    (.seq (.store _ _) (.seq (.store _ _) (.seq (.store _ _) (.store _ _))))
    (.call none _ _ (by intro name impossible; cases impossible))
  obtain ⟨finished,outputRun,returned⟩:=Input.sequence_returned absorbed post outProgram _ value (safe.summary_full absorbed).2.1 afterAbsorb
  have sixth:=output_frame absorbed finished stp pad out query fifth.environment cells5.state cells5.out outArena outAway outputRun
  have final:=LocalEffects.returned finished.code (.const 0#64) finished rfl
  rw [returned] at final
  exact (congrFun (LocalEffects.memory_of_erase finished post final) query).trans
    (sixth.memory.trans (fifth.memory.trans (fourth.memory.trans (third.memory.trans (second.memory.trans first.memory)))))

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.padding_memory
