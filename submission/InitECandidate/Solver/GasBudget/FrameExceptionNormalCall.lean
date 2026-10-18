import InitECandidate.Solver.GasBudget.FrameExceptionNormal

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual frame_exception caller. It derives two clocks for EvmErr1 and
three for every other error, preserves the actual regular ledger and marks
the real continuation done. No caller funding or successful helper is assumed. -/
theorem call_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame message continuation err empty gas spill reservoir : BitVec 64) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) expressions = some [.val (.word err)])
    (code : source.code.lookup (ofString "frame_exception") = some (formals, body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (continuationGlobal : source.globals.lookup (ofString "cur_cont") = some (.val (.word continuation)))
    (emptyGlobal : source.globals.lookup (ofString "evm_empty") = some (.val (.word empty)))
    (refillCode : source.code.lookup (ofString "refill_frame_state_gas") = some ([], Refill.body, .one))
    (haltCode : source.code.lookup (ofString "frame_halt") = some (Halt.formals, Halt.body, .one))
    (refillMapped : ∀ offset ∈ ([64, 72, 112, 192] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset))
    (haltMapped : ∀ offset ∈ ([64, 160, 184] : List Nat), source.memaddrs (frame + BitVec.ofNat 64 offset))
    (messageCell : source.memory (frame + 112#64) = .word message)
    (gasCell : source.memory (frame + 64#64) = .word gas) (spillCell : source.memory (frame + 192#64) = .word spill)
    (reservoirMapped : source.memaddrs (message + 48#64)) (reservoirCell : source.memory (message + 48#64) = .word reservoir)
    (reservoirAway : message + 48#64 ≠ frame + 64#64)
    (continuationAway : ∀ offset ∈ ([64, 184, 192] : List Nat), frame + BitVec.ofNat 64 offset ≠ continuation + 32#64)
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "frame_exception") expressions) = (none, target)) :
    2 + choicePrice err ≤ source.clock ∧ 2 + choicePrice err ≤ 3 ∧ target.clock = source.clock - (2 + choicePrice err) ∧
      target = {source with memory := target.memory, clock := source.clock - (2 + choicePrice err)} ∧
      regularBudget target.memory frame = regularBudget source.memory frame ∧ target.memory (continuation + 32#64) = .word 1#64 := by
  obtain ⟨callee, called, errLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "frame_exception") "err" body err code
  obtain ⟨positive, post, returned, bodyRun⟩ := Input.CallNormal.ignored_callee_return source target (ofString "frame_exception") expressions [.val (.word err)] body callee .one args called normal
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨funded, priced, returnedEq, clock, bodyFrame, budget, done⟩ := body_normal entry post frame message continuation err empty gas spill reservoir errLocal ev continuationGlobal emptyGlobal
    refillCode haltCode refillMapped haltMapped messageCell gasCell spillCell reservoirMapped reservoirCell reservoirAway continuationAway cap returned bodyRun
  rw [returnedEq] at bodyRun
  have callerFrame : emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - (2 + choicePrice err)} := by
    change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with memory := post.memory, clock := source.clock - 1 - (1 + choicePrice err)} at bodyFrame
    have subtract : source.clock - 1 - (1 + choicePrice err) = source.clock - (2 + choicePrice err) := by omega
    simpa only [subtract] using bodyFrame
  have actual := ignored_return source post (ofString "frame_exception") expressions [.val (.word err)] body callee (2 + choicePrice err) args called positive bodyRun callerFrame
  have same := congrArg Prod.snd (normal.symm.trans actual)
  change target = {source with memory := post.memory, clock := source.clock - (2 + choicePrice err)} at same
  refine ⟨?_, by omega, by rw [same], by rw [same], ?_, ?_⟩
  · change 1 + choicePrice err ≤ source.clock - 1 at funded
    omega
  · rw [same]; exact budget
  · rw [same]; exact done

end InitECandidate.Solver.GasBudget.FrameException

#print axioms InitECandidate.Solver.GasBudget.FrameException.call_normal
