import InitECandidate.Solver.Mpt.AccountIsEmptyReads
import InitECandidate.Solver.Mpt.TrieWalkEffects

namespace InitECandidate.Solver.Mpt.AccountIsEmpty
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem balance_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (account : BitVec 64)
    (image : AccountDecode.Image source account)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word account)))
    (installed : Input.OriginalCode.Installed source.code) (enough : 1 ≤ source.clock) :
    ∃ answer post, (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source balanceTail = (some (.returned (.val (.word answer))), post) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - 1} := by
  classical
  let words := Input.RlpWrite.U256Value.memoryWords source (account + 8#64)
  have read := balance_read source account image aLocal
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query))
      [field 8#64 Input.RlpWrite.U256Value.tupleShape] = some [Input.RlpWrite.U256Value.tuple words] := by
    simp [evalListHOLFinite,evalListHOLExact,show evalHOLExact (toExact source) (field 8#64 Input.RlpWrite.U256Value.tupleShape) =
      some (Input.RlpWrite.U256Value.tuple words) from read]
  have actual := GasBudget.U256Zero.call_execute source words "z" _ (.return (localVar "z")) args
    (GasBudget.U256Zero.original_code source.code installed) enough
  have returned : evaluateHOLFiniteState (bind {source with clock := source.clock - 1} "z" (GasBudget.U256Zero.resultWord words))
      (.return (localVar "z")) =
      (some (.returned (.val (.word (GasBudget.U256Zero.resultWord words)))),
        emptyLocalsHOLFinite (bind {source with clock := source.clock - 1} "z" (GasBudget.U256Zero.resultWord words))) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,localVar,toExact,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      shapeOfHOLExact,sizeOfShapeWithContextHOL]
  rw [returned] at actual
  refine ⟨GasBudget.U256Zero.resultWord words, _, ?_, actual, rfl⟩
  simp only [GasBudget.U256Zero.resultWord]
  split <;> simp

theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (account emptyHash : BitVec 64)
    (image : AccountDecode.Image source account)
    (aLocal : source.locals.lookup (ofString "a") = some (.val (.word account)))
    (emptyGlobal : source.globals.lookup (ofString "empty_code_hash") = some (.val (.word emptyHash)))
    (emptyArena : AllocatedBytes.Arena emptyHash 32)
    (installed : Input.OriginalCode.Installed source.code) (enough : 6 ≤ source.clock) :
    ∃ (paid : Nat) (answer : BitVec 64) (post : PanSemStateFiniteExact 64 Guest.HostMemory),
      paid ≤ 6 ∧ paid ≤ source.clock ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState source body = (some (.returned (.val (.word answer))), post) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - paid} := by
  classical
  let nonce := MemoryBytes.wordBits (source.memory account)
  have nonceRead : eval source (field 0#64) = some (.val (.word nonce)) := by
    simpa [nonce] using scalar_read source account image 0 (by decide) (by decide) aLocal
  rw [nonce_dispatch source nonce nonceRead]
  by_cases zeroNonce : nonce = 0#64
  · rw [if_pos zeroNonce]
    obtain ⟨paid, answer, positive, bound, funded, binary, compared⟩ := MutableTable.MemeqSmall.call_execute source image.hash emptyHash 32
      "eq" _ afterCompare (compare_arguments source account emptyHash image aLocal emptyGlobal)
      (TrieWalk.memeq_code source.code installed) (by decide)
      (by have := image.hashArena.upper; omega) (by have := emptyArena.upper; omega)
      (fun offset inside => AllocatedBytes.byte_mapped source image.hash 32 offset image.domain image.hashArena inside)
      (fun offset inside => AllocatedBytes.byte_mapped source emptyHash 32 offset image.domain emptyArena inside)
      (by change 5 ≤ source.clock; omega)
    change paid ≤ 5 at bound
    let middle := bind {source with clock := source.clock - paid} "eq" answer
    have eqLocal : middle.locals.lookup (ofString "eq") = some (.val (.word answer)) := by
      simp [middle,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
    have dispatched := compare_dispatch middle answer eqLocal
    by_cases zeroAnswer : answer = 0#64
    · rw [if_pos zeroAnswer] at dispatched
      rw [show compare = .decCall (ofString "eq") .one (ofString "memeq")
        [field 48#64, .var .global (ofString "empty_code_hash"), .const 32#64] afterCompare from rfl,
        compared,dispatched]
      exact ⟨paid,0#64,_,by omega,funded,Or.inl rfl,rfl,rfl⟩
    · rw [if_neg zeroAnswer] at dispatched
      have middleA : middle.locals.lookup (ofString "a") = some (.val (.word account)) := by
        simpa [middle,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,show ofString "eq" ≠ ofString "a" from by decide] using aLocal
      let middleImage := image.of_agreement source middle account rfl rfl rfl
      obtain ⟨lastAnswer, post, lastBinary, lastRun, lastFrame⟩ := balance_execute middle account middleImage middleA installed
        (by change 1 ≤ source.clock - paid; omega)
      rw [show compare = .decCall (ofString "eq") .one (ofString "memeq")
        [field 48#64, .var .global (ofString "empty_code_hash"), .const 32#64] afterCompare from rfl,
        compared,dispatched,lastRun]
      refine ⟨paid + 1,lastAnswer,_,by omega,by omega,lastBinary,rfl,?_⟩
      have frame := lastFrame
      change emptyLocalsHOLFinite post = emptyLocalsHOLFinite {source with clock := source.clock - paid - 1} at frame
      change emptyLocalsHOLFinite post = _
      simpa only [Nat.sub_sub] using frame
  · rw [if_neg zeroNonce]
    exact ⟨0,0#64,_,by omega,by omega,Or.inl rfl,rfl,by simp [emptyLocalsHOLFinite]⟩

end InitECandidate.Solver.Mpt.AccountIsEmpty

#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.balance_execute
#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.execute
