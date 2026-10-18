import InitECandidate.Solver.GasBudget.RegularChargeNormalCall

namespace InitECandidate.Solver.GasBudget.RegularCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

/-- The actual normal charge's only writes are its liquid/used words. This
retains unrelated stack/frame metadata through an opcode's charged prefix. -/
theorem call_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame amount : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some [.val (.word amount)])
    (code : source.code.lookup (ofString "charge_gas") = some (formals, body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_gas") arguments) = (none, target)) :
    ∃ gas used : BitVec 64, source.memory (frame + 64#64) = .word gas ∧ source.memory (frame + 184#64) = .word used ∧
      target.memory = WordWrites.write source.memory (writes frame gas used amount) := by
  obtain ⟨gas, used, positive, clock, gasMapped, usedMapped, gasCell, usedCell, affordable, postFrame, budget, debit, credit⟩ :=
    call_normal source target frame amount arguments args code ev cap normal
  obtain ⟨callee, called, amountLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "charge_gas") "amount" body amount code
  let entry := callEntryStateHOLFinite source callee
  obtain ⟨post, bodyRun, memoryEq, frameEq⟩ := execute entry frame gas used amount ev amountLocal gasMapped usedMapped gasCell usedCell affordable
  have actual := ignored_return source post (ofString "charge_gas") arguments [.val (.word amount)] body callee 1 args called positive bodyRun frameEq
  have same := congrArg Prod.snd (normal.symm.trans actual)
  have memorySame := congrArg PanSemStateFiniteExact.memory same
  change target.memory = post.memory at memorySame
  exact ⟨gas, used, gasCell, usedCell, memorySame.trans memoryEq⟩

theorem call_other_word (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame amount address : BitVec 64)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun current => Classical.propDecidable (source.memaddrs current)) arguments = some [.val (.word amount)])
    (code : source.code.lookup (ofString "charge_gas") = some (formals, body, .one))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (cap : regularBudget source.memory frame ≤ 16777216)
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) (ofString "charge_gas") arguments) = (none, target))
    (notGas : address ≠ frame + 64#64) (notUsed : address ≠ frame + 184#64) : target.memory address = source.memory address := by
  obtain ⟨gas, used, gasCell, usedCell, memoryEq⟩ := call_memory source target frame amount arguments args code ev cap normal
  rw [memoryEq]
  exact WordWrites.write_away source.memory (writes frame gas used amount) address (by simp [writes, notGas, notUsed])

end InitECandidate.Solver.GasBudget.RegularCharge

#print axioms InitECandidate.Solver.GasBudget.RegularCharge.call_memory
#print axioms InitECandidate.Solver.GasBudget.RegularCharge.call_other_word
