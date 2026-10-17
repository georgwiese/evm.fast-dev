import InitECandidate.Solver.Input.RlpWrite.U256MinProgram

namespace InitECandidate.Solver.Input.RlpWrite.U256Min
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual position declaration, limb call, masked shifted-byte store and
increment. Both temporary scopes restore; exactly one call clock is consumed. -/
theorem step_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (words : U256Value.Words) (dst : BitVec 64) (index length : Nat)
    (active : index<length) (small : length≤32)
    (a : source.locals.lookup (ofString "a")=some (U256Value.tuple words))
    (outLocal : source.locals.lookup (ofString "out")=some (.val (.word dst)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (code : source.code.lookup (ofString "u256_limb")=some (U256Limb.formals,U256Limb.body,.one))
    (mapped : source.memaddrs (panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index))) (enough : 1≤source.clock) :
    ∃ memory,evaluateHOLFiniteState source loopBody=
      (none,bind {source with memory:=memory,clock:=source.clock-1} "i" (BitVec.ofNat 64 (index+1))) ∧
      (∀ query,query≠panByteAlignHOL (width:=64) (dst+BitVec.ofNat 64 index)→memory query=source.memory query) := by
  classical
  let pos:=BitVec.ofNat 64 (length-1-index)
  let sp:=bind source "pos" pos
  have posLocal : sp.locals.lookup (ofString "pos")=some (.val (.word pos)):=bind_lookup_same _ _ _
  have aPos : sp.locals.lookup (ofString "a")=some (U256Value.tuple words):=
    (bind_lookup_other _ "pos" "a" _ (by decide)).trans a
  have args : evalListHOLFinite sp (h:=fun address=>Classical.propDecidable (sp.memaddrs address)) [localVar "a",limbIndex]=
      some [U256Value.tuple words,.val (.word (pos >>> (3:Nat)))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,aPos,limbIndex,posLocal,wordShiftHOL]
  obtain ⟨word,called⟩:=U256Limb.call_execute sp words (pos >>> (3:Nat)) "l" [localVar "a",limbIndex] afterLimb args code enough
  let sl:=bind {sp with clock:=sp.clock-1} "l" word
  have lLocal : sl.locals.lookup (ofString "l")=some (.val (.word word)):=bind_lookup_same _ _ _
  have posL : sl.locals.lookup (ofString "pos")=some (.val (.word pos)):=
    (bind_lookup_other _ "l" "pos" _ (by decide)).trans posLocal
  have outL : sl.locals.lookup (ofString "out")=some (.val (.word dst)):=
    (bind_lookup_other _ "l" "out" _ (by decide)).trans ((bind_lookup_other _ "pos" "out" _ (by decide)).trans outLocal)
  have iL : sl.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=
    (bind_lookup_other _ "l" "i" _ (by decide)).trans ((bind_lookup_other _ "pos" "i" _ (by decide)).trans i)
  have dstRead : eval sl destination=some (.val (.word (dst+BitVec.ofNat 64 index))) := by
    simp [eval,destination,localVar,evalHOLExact,evalListHOLExact,toExact,outL,iL,valueIsWord,valueWord,wordOpHOL,wordOp]
  let byteWord:=(word >>> (((pos &&& 7#64)*8#64).toNat)) &&& 255#64
  have valueRead : eval sl byteValue=some (.val (.word byteWord)):=byte_read sl pos word posL lLocal
  have storeRun:=WitnessRadix.ByteStore.execute_word sl destination byteValue (dst+BitVec.ofNat 64 index) byteWord dstRead valueRead mapped
  let memory:=WitnessRadix.ByteStore.put source.memory source.be (dst+BitVec.ofNat 64 index) (BitVec.ofNat 8 byteWord.toNat)
  let sw:={sl with memory:=memory}
  have iW : sw.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))):=iL
  have incrementRead : eval sw increment=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,increment,localVar,evalHOLExact,evalListHOLExact,toExact,iW,valueIsWord,valueWord,wordOpHOL,wordOp,←BitVec.ofNat_add]
  have incrementRun:=WitnessRadix.StateSteps.assign_execute sw "i" increment _ _ iW incrementRead
  have afterRun : evaluateHOLFiniteState sl afterLimb=(none,bind sw "i" (BitVec.ofNat 64 (index+1))) := by
    rw [afterLimb,WitnessRadix.StateSteps.next_sequence sl sw _ _ storeRun (Nat.le_refl _)]
    exact incrementRun
  have calledRun : evaluateHOLFiniteState sp afterPosition=(none,restore sp "l" (bind sw "i" (BitVec.ofNat 64 (index+1)))) := by
    rw [afterPosition,called,afterRun]
  have declared:=ScalarScope.declare_execute source _ "pos" position pos afterPosition none (position_read source index length active small i n) calledRun
  have restoredL : restore sp "l" (bind sw "i" (BitVec.ofNat 64 (index+1)))=
      bind {sp with memory:=memory,clock:=sp.clock-1} "i" (BitVec.ofNat 64 (index+1)) := by
    rw [restore_bind_other sp sw "l" "i" _ (by decide)]
    have saved : restore sp "l" sl={sp with clock:=sp.clock-1}:=restore_bound {sp with clock:=sp.clock-1} "l" word
    have written:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with memory:=memory}) saved
    change restore sp "l" sw={sp with memory:=memory,clock:=sp.clock-1} at written
    rw [written]
  have restoredPos : restore source "pos" (bind {sp with memory:=memory,clock:=sp.clock-1} "i" (BitVec.ofNat 64 (index+1)))=
      bind {source with memory:=memory,clock:=source.clock-1} "i" (BitVec.ofNat 64 (index+1)) := by
    rw [restore_bind_other source _ "pos" "i" _ (by decide)]
    have saved : restore source "pos" {sp with memory:=memory,clock:=sp.clock-1}={source with memory:=memory,clock:=source.clock-1}:=
      restore_bound {source with memory:=memory,clock:=source.clock-1} "pos" pos
    rw [saved]
  refine ⟨memory,?_,?_⟩
  · rw [loopBody,declared,restoredL,restoredPos]
  · intro query away
    exact WitnessRadix.ByteStore.away source.memory source.be (dst+BitVec.ofNat 64 index) query (BitVec.ofNat 8 byteWord.toNat) away

end InitECandidate.Solver.Input.RlpWrite.U256Min

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Min.step_execute
