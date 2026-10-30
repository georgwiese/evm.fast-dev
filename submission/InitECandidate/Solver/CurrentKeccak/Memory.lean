import InitECandidate.Solver.CurrentKeccak.BlocksMemory
import InitECandidate.Solver.CurrentKeccak.PaddingMemory

namespace InitECandidate.Solver.CurrentKeccak.Hash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input Input.CounterFlow WitnessRadix WitnessRadix.QueryBranch

set_option maxRecDepth 10000

/-- The complete unchanged software hash protects every word outside its
actual state/padding buffers and digest output. Every prefix is exposed from
this real return; the input remainder is derived from its actual block exit.
Only the numerical count bound is required, independently of input ownership. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad pointer out query : BitVec 64) (length : Nat)
    (environment : Environment source stp pad)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))))
    (outCell : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (small : length+136<2^64) (outArena : AllocatedBytes.Arena out 32)
    (stateAway : CopyGeneral.Away stp query 200) (padAway : CopyGeneral.Away pad query 136) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [body_shape] at run
  have stateRead : eval source (.var .global (ofString "keccak_st"))=some (.val (.word stp)) := by
    simp [eval,evalHOLExact,toExact,environment.stateGlobal]
  obtain ⟨inner,continued,endpoint⟩:=Input.declaration_return_word source post "stp" _ stp _ value stateRead run
  let entry:=bind source "stp" stp
  have entryEnvironment : Environment entry stp pad := environment.of_frame rfl
  have entryState : entry.locals.lookup (ofString "stp")=some (.val (.word stp)) := bind_lookup_same _ _ _
  have entryPointer : entry.locals.lookup (ofString "p")=some (.val (.word pointer)) := (bind_lookup_other source "stp" "p" stp (by decide)).trans pointerCell
  have entryCount : entry.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 length))) := (bind_lookup_other source "stp" "n" stp (by decide)).trans countCell
  have entryOut : entry.locals.lookup (ofString "out")=some (.val (.word out)) := (bind_lookup_other source "stp" "out" stp (by decide)).trans outCell
  obtain ⟨zeroed,zeroRun,afterZero⟩:=Input.sequence_returned entry inner _ _ value
    ((LocalPrefix.call (key:=ofString "p") none _ _ (by intro name impossible; cases impossible)).summary_full entry).2.1 continued
  have zeroArgs : evalListHOLFinite entry (h:=fun address=>Classical.propDecidable (entry.memaddrs address)) [localVar "stp",.const 200#64]=some (Zero.values stp 200) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,entryState,Zero.values]
  have first:=zero_frame entry zeroed stp pad stp query 200 entryEnvironment _ zeroArgs environment.stateArena environment.stateAligned (by decide)
    (by intro offset inside; exact (stateAway offset inside).1) zeroRun
  obtain ⟨loopPost,loopReturned,iRestored⟩:=Input.declaration_return_word zeroed inner "i" (.const 0#64) 0#64 _ value rfl afterZero
  let loopEntry:=bind zeroed "i" 0#64
  have loopEnvironment : Environment loopEntry stp pad := first.environment.of_frame rfl
  have initial : StrideInvariant length loopEntry := ⟨0#64,bind_lookup_same _ _ _,
    (bind_lookup_other zeroed "i" "n" 0#64 (by decide)).trans (first.cell _ _ entryCount),by simp⟩
  have loopPointer : loopEntry.locals.lookup (ofString "p")=some (.val (.word pointer)) :=
    (bind_lookup_other zeroed "i" "p" 0#64 (by decide)).trans (first.cell _ _ entryPointer)
  have loopState : loopEntry.locals.lookup (ofString "stp")=some (.val (.word stp)) :=
    (bind_lookup_other zeroed "i" "stp" 0#64 (by decide)).trans (first.cell _ _ entryState)
  have loopOut : loopEntry.locals.lookup (ofString "out")=some (.val (.word out)) :=
    (bind_lookup_other zeroed "i" "out" 0#64 (by decide)).trans (first.cell _ _ entryOut)
  have safe : LocalPrefix (ofString "n") blocks := .loop condition block_safe
  obtain ⟨middle,blocksRun,afterRun⟩:=Input.sequence_returned loopEntry loopPost blocks afterBlocks value (safe.summary_full loopEntry).2.1 loopReturned
  have second:=blocks_memory loopEntry middle stp pointer query length small loopEnvironment.installed initial loopPointer loopState
    (by intro offset inside aligned; exact (stateAway offset inside).1) blocksRun
  have middleEnvironment:=loopEnvironment.after blocks none (fun key=>blocks_globals key loopEntry.code loopEnvironment.installed) blocksRun
  obtain ⟨index,indexCell,nCell,bounded,short⟩:=blocks_normal loopEntry middle length small initial blocksRun
  have middlePointer := (blocks_local loopEntry middle (ofString "p") (by decide) blocksRun).trans loopPointer
  have middleState := (blocks_local loopEntry middle (ofString "stp") (by decide) blocksRun).trans loopState
  have middleOut := (blocks_local loopEntry middle (ofString "out") (by decide) blocksRun).trans loopOut
  have number : (BitVec.ofNat 64 length).toNat=length := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have difference : BitVec.ofNat 64 length-index=BitVec.ofNat 64 (length-index.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by change index.toNat≤(BitVec.ofNat 64 length).toNat; rw [number]; exact bounded),number,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have remRead : eval middle remainder=some (.val (.word (BitVec.ofNat 64 (length-index.toNat)))) := by
    simp [eval,remainder,evalHOLExact,evalListHOLExact,toExact,localVar,indexCell,nCell,valueIsWord,valueWord,wordOpHOL,wordOp,difference]
  rw [afterBlocks_shape] at afterRun
  obtain ⟨final,paddingRun,remRestored⟩:=Input.declaration_return_word middle loopPost "rem" remainder (BitVec.ofNat 64 (length-index.toNat)) paddingTail value remRead afterRun
  let paddingEntry:=bind middle "rem" (BitVec.ofNat 64 (length-index.toNat))
  have paddingEnvironment : Environment paddingEntry stp pad := middleEnvironment.of_frame rfl
  have cells : PaddingLocals paddingEntry stp pointer index out (length-index.toNat) :=
    ⟨(bind_lookup_other middle "rem" "stp" _ (by decide)).trans middleState,
     (bind_lookup_other middle "rem" "p" _ (by decide)).trans middlePointer,
     (bind_lookup_other middle "rem" "i" _ (by decide)).trans indexCell,
     (bind_lookup_other middle "rem" "out" _ (by decide)).trans middleOut,bind_lookup_same _ _ _⟩
  have third:=padding_memory paddingEntry final stp pad pointer index out query (length-index.toNat) paddingEnvironment cells short outArena
    (by intro offset inside aligned; exact (stateAway offset inside).1) padAway outAway value paddingRun
  rw [endpoint,iRestored,remRestored]
  exact third.trans (second.trans first.memory)

end InitECandidate.Solver.CurrentKeccak.Hash

#print axioms InitECandidate.Solver.CurrentKeccak.Hash.body_memory
