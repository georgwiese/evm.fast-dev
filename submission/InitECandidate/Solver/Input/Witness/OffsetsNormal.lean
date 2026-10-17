import InitECandidate.Solver.Input.Witness.OffsetLoop
import InitECandidate.Solver.Input.OffsetsCall

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch
set_option maxRecDepth 10000
set_option maxHeartbeats 400000

/-- A normal return through the actual offset loop and validator proves all
three real offsets are valid. Rejected offsets cannot reach loadedBody. -/
theorem offsets_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array total : BitVec 64) (start : Nat)
    (heap : Blob.HeapInput source input pointer) (extent : start+12≤input.length%2^64)
    (wp : source.locals.lookup (ofString "wp")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (wlen : source.locals.lookup (ofString "wlen")=some (.val (.word total)))
    (offsets : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (pointerAligned : pointer.toNat%8=0)
    (arrayAligned : array.toNat%8=0) (arrayLower : 2701131776≤array.toNat)
    (before : array.toNat+24≤pointer.toNat) (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (code : source.code.lookup (ofString "ssz_check_offsets")=some (Offsets.formals,Offsets.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (enough : 8≤source.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState source offsetBody=(some (.returned value),post)) :
    offsetWord input start 0=12#64 ∧ (∀ position<3,Offsets.ValidAt 12#64 total (offsetWord input start) position) ∧
      ∃ ready innerPost paid,paid≤8 ∧ ready.clock=source.clock-paid ∧
        BackingLayout.control ready=BackingLayout.control source ∧ Blob.HeapInput ready input pointer ∧
        (∀ name,name≠ofString "i" → ready.locals.lookup name=source.locals.lookup name) ∧
        (∀ position<3,ready.memory (byteAddress array (8*position))=.word (offsetWord input start position)) ∧
        evaluateHOLFiniteState ready loadedBody=(some (.returned value),innerPost) ∧ post=restore source "i" innerPost ∧
        (∀ query,query.toNat<array.toNat ∨ array.toNat+24≤query.toNat → ready.memory query=source.memory query) := by
  classical
  let entry:=bind source "i" 0#64
  let innerPost:=(evaluateHOLFiniteState entry (.seq offsetLoop offsetTail)).2
  have declared:=ScalarScope.declare_execute source innerPost "i" (.const 0#64) 0#64 (.seq offsetLoop offsetTail)
    (evaluateHOLFiniteState entry (.seq offsetLoop offsetTail)).1 rfl rfl
  rw [←offset_shapes.2.1] at declared
  have normal:=declared.symm.trans run
  have entryResult:=congrArg Prod.fst normal
  have entryRun : evaluateHOLFiniteState entry (.seq offsetLoop offsetTail)=(some (.returned value),innerPost):=
    Prod.ext entryResult rfl
  have postEq : post=restore source "i" innerPost:=(congrArg Prod.snd normal).symm
  obtain ⟨loopTarget,loopRun,loopClock,loopControl,loopHeap,loopI,loopOther,loopCells,loopFrame⟩:=offset_loop_execute entry input pointer array start 0 3 rfl
    heap extent ((bind_lookup_other source "i" "wp" _ (by decide)).trans wp) (bind_lookup_same _ _ _) offsets domain
    pointerAligned arrayAligned arrayLower before upper (by intro position impossible;omega) (by change 4≤source.clock;omega)
  have clock : loopTarget.clock=source.clock-3:=loopClock
  have globals : loopTarget.globals=source.globals:=congrArg (fun state=>state.globals) loopControl
  have codes : loopTarget.code=source.code:=congrArg (fun state=>state.code) loopControl
  have shapes : loopTarget.eshapes=source.eshapes:=congrArg (fun state=>state.eshapes) loopControl
  have domains : loopTarget.memaddrs=source.memaddrs:=congrArg (fun state=>state.memaddrs) loopControl
  have loopWlen : loopTarget.locals.lookup (ofString "wlen")=some (.val (.word total)) :=
    (loopOther _ (by decide)).trans ((bind_lookup_other source "i" "wlen" _ (by decide)).trans wlen)
  have loopOffsets : loopTarget.globals.lookup (ofString "ssz_offs")=some (.val (.word array)) := by rw [globals];exact offsets
  have args : evalListHOLFinite loopTarget (h:=fun q=>Classical.propDecidable (loopTarget.memaddrs q)) offsetArguments=
      some (Offsets.arguments array 12#64 total 3) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,offsetArguments,Offsets.arguments,Header.offsets,localVar,loopOffsets,loopWlen]
  have mapped : ∀ position<3,loopTarget.memaddrs (array+BitVec.ofNat 64 (8*position)) := by
    intro position inside
    exact word_mapped loopTarget array 24 (8*position) (domains.trans domain) ⟨arrayLower,by omega⟩ (by omega) arrayAligned (by omega)
  obtain ⟨result,target,paid,guardRun,bound,frame,outcome⟩:=Offsets.call_execute loopTarget offsetArguments array 12#64 total (offsetWord input start) 3
    (by decide) (by decide) args (by rw [codes];exact code) (by rw [codes];exact failCode) (by rw [shapes];exact exceptionShape)
    mapped loopCells (by rw [clock];omega)
  have targetClock : target.clock=loopTarget.clock-paid:=congrArg (fun state=>state.clock) frame
  have restRun : evaluateHOLFiniteState loopTarget offsetTail=(some (.returned value),innerPost) := by
    rw [StateSteps.next_sequence entry loopTarget _ _ loopRun (by change loopTarget.clock≤source.clock;rw [clock];omega)] at entryRun
    exact entryRun
  rw [offset_shapes.2.2.1] at restRun
  rcases outcome with passed|fault
  · have guardNone : evaluateHOLFiniteState loopTarget offsetGuard=(none,target):=by simpa only [offsetGuard,passed.1] using guardRun
    have targetEq:=Request.state_from_frame loopTarget target paid frame passed.2.2.1
    have continued:=StateSteps.next_sequence loopTarget target offsetGuard loadedBody guardNone (by rw [targetClock];omega)
    rw [continued] at restRun
    have targetControl : BackingLayout.control target=BackingLayout.control source := by rw [targetEq];exact loopControl
    have targetHeap : Blob.HeapInput target input pointer := by rw [targetEq];exact loopHeap
    refine ⟨passed.2.1,passed.2.2.2,target,innerPost,paid+3,by omega,?_,targetControl,targetHeap,?_,?_,restRun,postEq,?_⟩
    · rw [targetClock,clock];omega
    · intro name different
      rw [targetEq]
      have entryOther : entry.locals.lookup name=source.locals.lookup name := by
        change (source.locals.update (ofString "i",.val (.word 0#64))).lookup name=_
        simp [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "i"==name)=false from beq_eq_false_iff_ne.mpr (Ne.symm different)]
      exact (loopOther name different).trans entryOther
    · rw [targetEq];exact loopCells
    · intro query outside
      rw [targetEq]
      exact loopFrame query outside
  · obtain ⟨error,allowed,resultEq⟩:=fault
    have guardFault : evaluateHOLFiniteState loopTarget offsetGuard=(some (.exception (ofString "SszErr") (.val (.word error))),target) := by
      simpa only [offsetGuard,resultEq] using guardRun
    have stopped:=StateSteps.stopped_sequence loopTarget target offsetGuard loadedBody (.exception (ofString "SszErr") (.val (.word error)))
      guardFault (by rw [targetClock];omega)
    rw [stopped] at restRun
    have impossible:=congrArg Prod.fst restRun
    cases impossible

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.offsets_normal
