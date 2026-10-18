import InitECandidate.Solver.GasBudget.Halt
import InitECandidate.Solver.GasBudget.RegularChargeNormalCall

namespace InitECandidate.Solver.GasBudget.Halt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- Actual frame_halt call, with its call clock and non-wrap derived from
normal execution and the capped current regular ledger. Exact writes retain
the error marker while moving all liquid gas into the used counter. -/
theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas used err : BitVec 64)
    (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word err)])
    (code : source.code.lookup (ofString "frame_halt") = some (formals, body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : ∀ offset ∈ ([64, 160, 184] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset))
    (gasCell : source.memory (frame + 64#64) = .word gas) (usedCell : source.memory (frame + 184#64) = .word used)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "frame_halt") expressions) = (none, target)) :
    1 ≤ source.clock ∧ target.clock = source.clock - 1 ∧
      target = {source with memory := WordWrites.write source.memory (writes frame gas used err), clock := source.clock - 1} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧
      target.memory (frame + 64#64) = .word 0#64 ∧ target.memory (frame + 160#64) = .word err := by
  obtain ⟨callee, called, errLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "frame_halt") "err" body err code
  obtain ⟨positive, _, _, _⟩ := Input.CallNormal.ignored_callee_return source target (ofString "frame_halt") expressions [.val (.word err)] body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  let memory := WordWrites.write source.memory (writes frame gas used err)
  have bodyRun := execute entry frame gas used err ev errLocal mapped gasCell usedCell
  have bodyFrame : emptyLocalsHOLFinite (emptyLocalsHOLFinite {entry with memory := memory}) =
      emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - 1} := rfl
  have actual := ignored_return source _ (ofString "frame_halt") expressions [.val (.word err)] body callee 1 args called positive bodyRun bodyFrame
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := memory, clock := source.clock - 1} at same
  have fits := RegularCharge.ledger_fits source frame gas used gasCell usedCell cap
  have distinct : ((writes frame gas used err).map Prod.fst).Nodup := by
    simp [writes, offsets_ne frame 184#64 64#64 (by decide), offsets_ne frame 184#64 160#64 (by decide), offsets_ne frame 64#64 160#64 (by decide)]
  refine ⟨positive, by rw [same], same, ?_, ?_, ?_⟩
  · rw [same]
    exact preserves_regular_budget source frame gas used err gasCell usedCell fits
  · rw [same]
    exact WordWrites.write_unique source.memory (writes frame gas used err) (frame + 64#64, 0#64) distinct (by simp [writes])
  · rw [same]
    exact WordWrites.write_unique source.memory (writes frame gas used err) (frame + 160#64, err) distinct (by simp [writes])

end InitECandidate.Solver.GasBudget.Halt

#print axioms InitECandidate.Solver.GasBudget.Halt.call_normal
