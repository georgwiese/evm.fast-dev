import InitECandidate.Solver.Input.CurrentHash.RootCallMemory
import InitECandidate.Solver.Input.CurrentHash.InvocationFrame

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- A genuine normal root child call supplies the next complete same-decoder
state. Earlier SI, PL and RQ metadata survive its real memory frame before
later argument loads; caller locals and current heap are actually restored. -/
theorem State.after_call {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob si record rq root array ch cursor : BitVec 64} {length start size : Nat}
    (state : State input source blob si record rq root array ch cursor length start size) (step : Step)
    (actual : evaluateHOLFiniteState source step.call=(none,post)) : State input post blob si record rq root array ch cursor length start size := by
  have frame := state.call_frame step record state.record_before_chunks (metadata_chunk_away record state.record_lower) actual
  have workspace := state.data.workspace.after_call step.routine (some none) step.arguments none actual
  have global (cursorKey : Cursor) := Effects.call_preserves cursorKey source.code state.data.workspace.code step.routine (some none) step.arguments source rfl
  have scratch := global .scratch
  change GlobalEffects.erase (key .scratch) (evaluateHOLFiniteState source step.call).2=_ at scratch
  rw [actual] at scratch
  have frameGlobal := global .frame
  change GlobalEffects.erase (key .frame) (evaluateHOLFiniteState source step.call).2=_ at frameGlobal
  rw [actual] at frameGlobal
  have arena : CurrentStartup.ArenaState post := ⟨(congrArg Prod.snd scratch).trans state.data.arena.scratch,
    (congrArg Prod.snd frameGlobal).trans state.data.arena.frame,workspace.domain,workspace.code⟩
  have heap : NormalHeapEffects.AtLeast (root.toNat+32) post := ⟨cursor,frame.2,by have a:=state.chunksAfter; have b:=state.heapAfter; omega,state.heapBound,state.heapAligned⟩
  have kept (name : String) := CallNormal.ignored_lookup source post (ofString name) (Code.name step.routine) step.arguments actual
  have next := state.data.of_interval workspace arena heap ((kept "si").trans state.data.si) ((kept "out").trans state.data.out) ch.toNat state.chunksAfter
    (by intro query lower before; exact (state.call_frame step query before (metadata_chunk_away query lower) actual).1)
  exact ⟨next,(kept "ch").trans state.chunks,state.chunksArena,state.chunksAligned,state.chunksAfter,frame.2,state.heapBound,state.heapAligned,state.heapAfter⟩

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.State.after_call
