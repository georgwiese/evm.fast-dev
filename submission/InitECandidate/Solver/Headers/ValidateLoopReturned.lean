import InitECandidate.Solver.Headers.ValidateLinkSuffix
import InitECandidate.Solver.Input.SequenceReturned
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def result (hs hashes : BitVec 64) : ValueHOL 64 := .rStruct [.val (.word hs),.val (.word hashes)]

theorem decode_loop_never (source : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64) :
    (evaluateHOLFiniteState source (.while test decodeStep)).1≠some (.returned value) := by
  intro returned
  have facts:=Input.ReturnFacts.loop source.code test decodeStep (fun _=>True) (fun _=>False)
    (by intro current codeEq valid word read nonzero funded post value run
        exact (decode_step_local.summary (decClockHOLFinite current)).2 value (congrArg Prod.fst run))
    (by intros; trivial) source rfl True.intro
  exact facts _ value (Prod.ext returned rfl)

/-- A genuine returning link tail derives the real final loop state and
its original tuple value. No successful comparison is assumed in advance. -/
theorem link_tail_returned (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (state : RoundState data origin source 1) (layout : RoundLayout data)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source linkTail=(some (.returned value),post)) :
    value=result data.hs data.hashes ∧ ∃ finish index,index≤data.count+1 ∧ RoundState data origin finish index ∧ post=emptyLocalsHOLFinite finish := by
  obtain ⟨_,_,_,_,_,_,tailShape,_,_,_,_⟩ := shapes
  rw [tailShape] at normal
  obtain ⟨finish,loopRun,returned⟩ := Input.sequence_returned source post _ _ value (link_loop_never source) normal
  obtain ⟨index,bounded,finalState⟩ := link_loop_normal data origin source finish 1 state layout (by omega) loopRun
  obtain ⟨actual,endpoint⟩ := Input.return_normal finish post _ value returned
  have read : eval finish (.rstruct [localVar "hs",localVar "hashes"])=some (result data.hs data.hashes) := by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,finalState.hsCell,finalState.hashesCell,result]
  exact ⟨Option.some.inj (actual.symm.trans read),finish,index,bounded,finalState,endpoint⟩

theorem after_decode_returned (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Nat)
    (state : RoundState data origin source index) (layout : RoundLayout data)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source afterDecode=(some (.returned value),post)) :
    value=result data.hs data.hashes ∧ ∃ finish nextIndex,nextIndex≤data.count+1 ∧ RoundState data origin finish nextIndex ∧ post=emptyLocalsHOLFinite finish := by
  obtain ⟨_,_,_,_,_,resetShape,_,_,_,_,_⟩ := shapes
  rw [resetShape] at normal
  obtain ⟨actual,next⟩ := reset_round data origin source index state
  rw [evaluateHOLFiniteState_seq_line780,actual] at normal
  exact link_tail_returned data origin (resetIndex source) post next layout value normal

/-- Both original loops preserve the complete current physical invariant
up to the actual return leaf. In particular all nonheap globals are retained. -/
theorem loops_returned (data : Data) (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (state : RoundState data origin source 0) (layout : RoundLayout data)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source loops=(some (.returned value),post)) :
    value=result data.hs data.hashes ∧ ∃ finish index,index≤data.count+1 ∧ RoundState data origin finish index ∧ post=emptyLocalsHOLFinite finish := by
  obtain ⟨_,_,_,_,loopsShape,_,_,_,_,_,_⟩ := shapes
  rw [loopsShape] at normal
  obtain ⟨middle,loopRun,continued⟩ := Input.sequence_returned source post _ _ value (decode_loop_never source) normal
  obtain ⟨index,bounded,next⟩ := decode_loop_normal data origin source middle 0 state layout (by omega) loopRun
  exact after_decode_returned data origin middle post index next layout value continued

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.decode_loop_never
#print axioms InitECandidate.Solver.Headers.Validate.link_tail_returned
#print axioms InitECandidate.Solver.Headers.Validate.after_decode_returned
#print axioms InitECandidate.Solver.Headers.Validate.loops_returned
