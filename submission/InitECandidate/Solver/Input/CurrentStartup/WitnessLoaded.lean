import InitECandidate.Solver.Input.CurrentStartup.WitnessValidated
import InitECandidate.Solver.Input.Witness.LoadedOffsets

namespace InitECandidate.Solver.Input.CurrentStartup.WitnessLoaded
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

structure Result (input : Guest.InputBlob) (source current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer statelessRecord record gasWord requestRecord : BitVec 64) (payloadLength : Nat) (value : ValueHOL 64) : Prop where
  context : PayloadCallerReturn.Context input current pointer statelessRecord record gasWord payloadLength
  heap : NormalHeapEffects.AtLeast (requestRecord.toNat + 80) current
  wp : current.locals.lookup (ofString "wp") = some (.val (.word (pointer + BitVec.ofNat 64 (2 + Guest.GasLimit.le32 input 6))))
  wlen : current.locals.lookup (ofString "wlen") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6))))
  w0 : current.locals.lookup (ofString "w0") = some (.val (.word (Witness.offsetWord input (2 + Guest.GasLimit.le32 input 6) 0)))
  w1 : current.locals.lookup (ofString "w1") = some (.val (.word (Witness.offsetWord input (2 + Guest.GasLimit.le32 input 6) 1)))
  w2 : current.locals.lookup (ofString "w2") = some (.val (.word (Witness.offsetWord input (2 + Guest.GasLimit.le32 input 6) 2)))
  first : Witness.offsetWord input (2 + Guest.GasLimit.le32 input 6) 0 = 12#64
  valid : ∀ index < 3, Offsets.ValidAt 12#64 (BitVec.ofNat 64 (input.length % 2^64 - 2 - Guest.GasLimit.le32 input 6))
    (Witness.offsetWord input (2 + Guest.GasLimit.le32 input 6)) index
  requestCell : current.memory (statelessRecord + 32#64) = .word requestRecord
  returned : evaluateHOLFiniteState current Witness.nodeCall = (some (.returned value), post)
  endpoint : ∃ origin originalPost, WitnessValidated.Result input origin source originalPost
      pointer statelessRecord record gasWord requestRecord payloadLength value ∧
    LocalEffects.erase originalPost = LocalEffects.erase post ∧ originalPost.clock = post.clock

def Reached (input : Guest.InputBlob) : Prop :=
  ∃ source current post, ∃ pointer statelessRecord record gasWord requestRecord : BitVec 64,
    ∃ payloadLength : Nat, ∃ value : ValueHOL 64,
      Result input source current post pointer statelessRecord record gasWord requestRecord payloadLength value

/-- The real three readonly offset declarations resume the actual node-list
call without spending a source tick or changing memory, heap, request or gas. -/
theorem validated (input : Guest.InputBlob) (actual : WitnessValidated.Reached input) : Reached input := by
  obtain ⟨origin, source, post, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, value, data⟩ := actual
  have context := data.context
  have mapped : ∀ position < 3, source.memaddrs (WitnessRadix.byteAddress 2701132528#64 (8 * position)) := by
    intro position small
    exact WitnessRadix.AllocatedBytes.word_mapped source 2701132528#64 24 (8 * position) context.domain
      ⟨by decide, by decide⟩ (by omega) (by decide) (by omega)
  have actualLoads := Witness.loaded_offsets_execute source input 2701132528#64 (2 + Guest.GasLimit.le32 input 6)
    context.workspace mapped data.cells
  have observed := actualLoads.symm.trans data.returned
  let current := Witness.loadedState source input (2 + Guest.GasLimit.le32 input 6)
  let inner := (evaluateHOLFiniteState current Witness.nodeCall).2
  have result : (evaluateHOLFiniteState current Witness.nodeCall).1 = some (.returned value) := congrArg Prod.fst observed
  have endpoint : post = Witness.restoreLoaded source input (2 + Guest.GasLimit.le32 input 6) inner := (congrArg Prod.snd observed).symm
  have locals (name : String) (different : ofString name ≠ ofString "w0" ∧ ofString name ≠ ofString "w1" ∧ ofString name ≠ ofString "w2") :
      current.locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
    Witness.loaded_other_local source input (2 + Guest.GasLimit.le32 input 6) (ofString name) different
  have currentContext := PayloadCallerReturn.Context.of_control input source current pointer statelessRecord record gasWord payloadLength
    context rfl data.context.image data.context.gasCell (by
      intro name member
      apply locals
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨w0, w1, w2⟩ := Witness.loaded_offset_locals source input (2 + Guest.GasLimit.le32 input 6)
  refine ⟨source, current, inner, pointer, statelessRecord, record, gasWord, requestRecord, payloadLength, value,
    ⟨currentContext, data.heap, (locals "wp" (by decide)).trans data.wp,
      (locals "wlen" (by decide)).trans data.wlen, w0, w1, w2, data.first, data.valid, data.requestCell,
      Prod.ext result rfl, ?_⟩⟩
  refine ⟨origin, post, data, ?_, ?_⟩
  · rw [endpoint]
    rfl
  · rw [endpoint]
    rfl

theorem separated (input : Guest.InputBlob) (word : BitVec 64)
    (actual : MainSeparatedInput.StatelessRun input word)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) : Reached input :=
  validated input (WitnessValidated.separated input word actual gas)

end InitECandidate.Solver.Input.CurrentStartup.WitnessLoaded

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessLoaded.validated

#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessLoaded.separated
