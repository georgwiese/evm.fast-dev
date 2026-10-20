import InitECandidate.Solver.Input.Witness.OffsetLoop
import InitECandidate.Solver.Input.TerminatingPaddedSequence

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

theorem offset_body_shape : offsetBody = .dec (ofString "i") .one (.const 0#64) (.seq offsetLoop offsetTail) := offset_shapes.2.1

/-- The actual three-iteration witness-offset loop is funded by its enclosing
non-timeout body. Every copied byte and the complete control/FFI frame survive;
the unchanged later validator/list result is left arbitrary. -/
theorem loop_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start : Nat)
    (heap : Blob.HeapInput source input pointer) (extent : start + 12 ≤ input.length % 2^64)
    (wp : source.locals.lookup (ofString "wp") = some (.val (.word (pointer + BitVec.ofNat 64 start))))
    (offsets : source.globals.lookup (ofString "ssz_offs") = some (.val (.word array)))
    (domain : source.memaddrs = InitE.ordinaryDomain) (pointerAligned : pointer.toNat % 8 = 0)
    (arrayAligned : array.toNat % 8 = 0) (arrayLower : 2701131776 ≤ array.toNat)
    (before : array.toNat + 24 ≤ pointer.toNat) (upper : pointer.toNat + input.length % 2^64 + 8 ≤ 33806089496)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source offsetBody = (result,post)) (notTimeout : result ≠ some .timeOut) :
    3 ≤ source.clock ∧ ∃ next innerPost,next.clock = source.clock - 3 ∧ BackingLayout.control next = BackingLayout.control source ∧
      Blob.HeapInput next input pointer ∧
      (∀ name,name ≠ ofString "i" → next.locals.lookup name = source.locals.lookup name) ∧
      (∀ position < 3,next.memory (byteAddress array (8*position)) = .word (offsetWord input start position)) ∧
      evaluateHOLFiniteState next offsetTail = (result,innerPost) ∧ post = restore source "i" innerPost ∧
      (∀ query,query.toNat < array.toNat ∨ array.toNat + 24 ≤ query.toNat → next.memory query = source.memory query) := by
  let entry := bind source "i" 0#64
  let innerPost := (evaluateHOLFiniteState entry (.seq offsetLoop offsetTail)).2
  have declared := ScalarScope.declare_execute source innerPost "i" (.const 0#64) 0#64 (.seq offsetLoop offsetTail)
    (evaluateHOLFiniteState entry (.seq offsetLoop offsetTail)).1 rfl rfl
  rw [← offset_body_shape] at declared
  have actual := declared.symm.trans run
  have observed := congrArg Prod.fst actual
  have innerRun : evaluateHOLFiniteState entry (.seq offsetLoop offsetTail) = (result,innerPost) := Prod.ext observed rfl
  have postEq : post = restore source "i" innerPost := (congrArg Prod.snd actual).symm
  let padded := {entry with clock := entry.clock + 4}
  have pLocal : padded.locals.lookup (ofString "wp") = some (.val (.word (pointer + BitVec.ofNat 64 start))) :=
    (bind_lookup_other source "i" "wp" _ (by decide)).trans wp
  obtain ⟨paddedPost,paddedRun,paddedClock,control,paddedHeap,index,other,cells,memoryFrame⟩ := offset_loop_execute padded input pointer array start 0 3 rfl heap extent pLocal
    (bind_lookup_same _ _ _) offsets domain pointerAligned arrayAligned arrayLower before upper (by intro position bad; omega) (by change 4 ≤ source.clock + 4; omega)
  obtain ⟨funded,loopRun⟩ := terminating_padded_sequence entry innerPost paddedPost offsetLoop offsetTail 4 none result paddedRun innerRun notTimeout
  let next := {paddedPost with clock := paddedPost.clock - 4}
  have paddedClockEq : paddedPost.clock = source.clock + 4 - 3 := paddedClock
  have enough : 3 ≤ source.clock := by omega
  have nextClock : next.clock = source.clock - 3 := by change paddedPost.clock - 4 = _; omega
  have restRun : evaluateHOLFiniteState next offsetTail = (result,innerPost) := by
    rw [StateSteps.next_sequence entry next _ _ loopRun (by change next.clock ≤ source.clock; rw [nextClock]; omega)] at innerRun
    exact innerRun
  have nextHeap := Blob.HeapInput.of_fields paddedPost next input pointer rfl rfl rfl paddedHeap
  have otherLocal (name : MlS) (different : name ≠ ofString "i") : next.locals.lookup name = source.locals.lookup name := by
    have initial : entry.locals.lookup name = source.locals.lookup name := by
      change (source.locals.update (ofString "i",.val (.word 0#64))).lookup name = _
      simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    exact (other name different).trans initial
  exact ⟨enough,next,innerPost,nextClock,control,nextHeap,otherLocal,cells,restRun,postEq,memoryFrame⟩

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.offset_body_shape
#print axioms InitECandidate.Solver.Input.Witness.loop_trace
