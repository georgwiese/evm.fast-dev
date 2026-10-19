import InitECandidate.Solver.Rlp.ValidationPush
import InitECandidate.Solver.Rlp.ValidationView

namespace InitECandidate.Solver.Rlp.Validation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem choose_evaluate (source : PanSemStateFiniteExact 64 Guest.HostMemory) (header payload flag : BitVec 64)
    (cell : source.locals.lookup (ofString "h")=some (Header.result header payload flag)) :
    evaluateHOLFiniteState source choose=
      if flag≠0#64 then evaluateHOLFiniteState source push else evaluateHOLFiniteState source move := by
  simp [choose,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,cell,Header.result,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-- Both actual branches preserve a physical pending-record view and
decrease the rank. The new header's size facts come from the real header
decoder; the list branch obtains room from the actual scratch allocator. -/
theorem choose_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rootEnd cursor limit position ending header payload flag : BitVec 64) (frames : List Frame)
    (view : View source rootEnd cursor limit position ending 1#64 frames)
    (hCell : source.locals.lookup (ofString "h")=some (Header.result header payload flag))
    (payloadCell : source.locals.lookup (ofString "payload")=some (.val (.word (position+header))))
    (afterCell : source.locals.lookup (ofString "after")=some (.val (.word (position+header+payload))))
    (positive : 1≤header.toNat+payload.toNat) (extent : header.toNat+payload.toNat≤(ending-position).toNat)
    (binary : flag=0#64 ∨ flag=1#64) (listHeader : flag=1#64 → 1≤header.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source choose=(none,target)) :
    ∃ nextCursor nextPosition nextEnding nextFrames,
      View target rootEnd nextCursor limit nextPosition nextEnding 1#64 nextFrames ∧
      rank rootEnd nextPosition nextFrames.length true<rank rootEnd position frames.length true := by
  have arithmetic := parse_progress rootEnd position ending header payload flag frames.length view.ordered
    (Pending.end_le source.memory source.memaddrs cursor.toNat rootEnd frames ending view.pending) positive extent binary listHeader
  obtain ⟨headerNumber,afterNumber,ordered,within,advances,smaller⟩ := arithmetic
  rw [choose_evaluate source header payload flag hCell] at normal
  by_cases zero : flag=0#64
  · rw [if_neg (not_not_intro zero)] at normal
    have readAfter : eval source (localVar "after")=some (.val (.word (position+header+payload))) := by
      simp [eval,evalHOLExact,localVar,toExact,afterCell]
    have assigned := WitnessRadix.StateSteps.assign_execute source "pos" (localVar "after") position (position+header+payload) view.positionCell readAfter
    change evaluateHOLFiniteState source move=(none,bind source "pos" (position+header+payload)) at assigned
    have same : target=bind source "pos" (position+header+payload) := (Prod.mk.inj (normal.symm.trans assigned)).2
    rw [same]
    refine ⟨cursor,position+header+payload,ending,frames,?_,?_⟩
    · refine ⟨Arena.of_fields source _ cursor limit view.arena rfl rfl,bind_lookup_same _ _ _,
        (bind_lookup_other _ "pos" "end" _ (by decide)).trans view.endCell,
        (bind_lookup_other _ "pos" "top" _ (by decide)).trans view.topCell,
        (bind_lookup_other _ "pos" "go" _ (by decide)).trans view.goCell,?_,Or.inr rfl,view.pending⟩
      simpa only [nextPosition,nextEnd,if_pos zero] using ordered
    · simpa only [nextPosition,nextDepth,if_pos zero] using smaller
  · rw [if_pos zero] at normal
    obtain ⟨room,funded,same⟩ := push_none source target cursor limit position ending (topOf frames) (position+header) (position+header+payload)
      view.arena view.positionCell view.endCell view.topCell payloadCell afterCell installed normal
    rw [same]
    let pointer := Arenas.rounded .down cursor 24#64
    let nextFrames : List Frame := {pointer:=pointer,resume:=position+header+payload,parentEnd:=ending}::frames
    have locals := push_post_locals source cursor position ending (topOf frames) (position+header) (position+header+payload)
    refine ⟨pointer,position+header,position+header+payload,nextFrames,?_,?_⟩
    · refine ⟨push_post_arena source cursor limit position ending (topOf frames) (position+header) (position+header+payload) view.arena room,
        locals.1,locals.2.1,locals.2.2.1,locals.2.2.2.trans view.goCell,?_,Or.inr rfl,?_⟩
      · simpa only [nextPosition,nextEnd,if_neg zero] using ordered
      · have afterWithin : (position+header+payload).toNat≤ending.toNat := by
          rw [afterNumber]
          rw [BitVec.toNat_sub_of_le view.ordered] at extent
          omega
        exact push_post_pending source cursor limit rootEnd position ending (position+header) (position+header+payload) frames view.arena room view.pending afterWithin
    · simpa only [nextPosition,nextDepth,if_neg zero,nextFrames,List.length_cons] using smaller

end InitECandidate.Solver.Rlp.Validation

#print axioms InitECandidate.Solver.Rlp.Validation.choose_evaluate
#print axioms InitECandidate.Solver.Rlp.Validation.choose_none
