import InitECandidate.Solver.Mpt.AccountIsEmptyNormal
import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.ScopedCallSuccess

namespace InitECandidate.Solver.Mpt.AccountIsEmpty
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (account emptyHash : BitVec 64)
    (image : AccountDecode.Image source account)
    (emptyGlobal : source.globals.lookup (ofString "empty_code_hash") = some (.val (.word emptyHash)))
    (emptyArena : AllocatedBytes.Arena emptyHash 32) (installed : Input.OriginalCode.Installed source.code)
    (name : MlS) (expression : ExpHOL 64) (continuation : ProgHOL 64) (tailPrice : Nat)
    (read : eval source expression = some (.val (.word account)))
    (tailBound : Input.ClockCost.Bound source.code continuation tailPrice) :
    source.clock - (evaluateHOLFiniteState source (.decCall name .one (ofString "acct_is_empty") [expression] continuation)).2.clock ≤ 7 + tailPrice := by
  classical
  obtain ⟨callee,called,aLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "acct_is_empty") "a" body account
    (original_code source.code installed)
  let entry := callEntryStateHOLFinite source callee
  let entryImage := image.of_agreement source entry account rfl rfl rfl
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [expression] = some [.val (.word account)] := by
    simp [evalListHOLFinite,evalListHOLExact,show evalHOLExact (toExact source) expression = some (.val (.word account)) from read]
  have price := body_cost entry account emptyHash entryImage aLocal emptyGlobal emptyArena installed
  have result := Input.ClockCost.scoped_current source name .one (ofString "acct_is_empty") [expression] _ body continuation callee .one
    6 tailPrice args called price tailBound
  omega

theorem success_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (account emptyHash : BitVec 64)
    (image : AccountDecode.Image source account)
    (emptyGlobal : source.globals.lookup (ofString "empty_code_hash") = some (.val (.word emptyHash)))
    (emptyArena : AllocatedBytes.Arena emptyHash 32) (installed : Input.OriginalCode.Installed source.code)
    (name : String) (expression : ExpHOL 64) (continuation : ProgHOL 64)
    (read : eval source expression = some (.val (.word account)))
    (result : Option (PanSemResultExact 64)) (success : result = none ∨ ∃ value, result = some (.returned value))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "acct_is_empty") [expression] continuation) = (result,post)) :
    ∃ (paid : Nat) (answer : BitVec 64) (inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ 7 ∧ paid ≤ source.clock ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - paid} name answer) continuation = (result,inner) ∧
      post = restore source name inner := by
  classical
  obtain ⟨callee,called,aLocal⟩ := Input.CallNormal.unary_environment source.code.lookup (ofString "acct_is_empty") "a" body account
    (original_code source.code installed)
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [expression] = some [.val (.word account)] := by
    simp [evalListHOLFinite,evalListHOLExact,show evalHOLExact (toExact source) expression = some (.val (.word account)) from read]
  obtain ⟨positive,target,returned,inner,bodyRun,checked,tailRun,scope⟩ := Input.CallNormal.scoped_success source post name .one
    (ofString "acct_is_empty") [expression] _ body continuation callee .one args called result success normal
  let entry := callEntryStateHOLFinite source callee
  let entryImage := image.of_agreement source entry account rfl rfl rfl
  obtain ⟨spent,answer,bounded,funded,binary,resultEq,fields⟩ := body_normal entry target account emptyHash entryImage aLocal emptyGlobal emptyArena installed returned bodyRun
  have restored := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) fields
  change {target with locals := source.locals} = {source with clock := source.clock - 1 - spent} at restored
  have subtract : source.clock - 1 - spent = source.clock - (spent + 1) := by omega
  rw [subtract] at restored
  have canonical : Input.CallNormal.continuationEntry source target name returned = bind {source with clock := source.clock - (spent + 1)} name answer := by
    rw [resultEq]
    exact congrArg (setVarHOLFinite (ofString name) (.val (.word answer))) restored
  change spent ≤ source.clock - 1 at funded
  refine ⟨spent + 1,answer,inner,by omega,by omega,by omega,binary,?_,scope⟩
  rw [canonical] at tailRun
  exact tailRun

theorem none_prefix (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (account emptyHash : BitVec 64)
    (image : AccountDecode.Image source account)
    (emptyGlobal : source.globals.lookup (ofString "empty_code_hash") = some (.val (.word emptyHash)))
    (emptyArena : AllocatedBytes.Arena emptyHash 32) (installed : Input.OriginalCode.Installed source.code)
    (name : String) (expression : ExpHOL 64) (continuation : ProgHOL 64)
    (read : eval source expression = some (.val (.word account)))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "acct_is_empty") [expression] continuation) = (none,post)) :
    ∃ (paid : Nat) (answer : BitVec 64) (inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ 7 ∧ paid ≤ source.clock ∧ (answer = 0#64 ∨ answer = 1#64) ∧
      evaluateHOLFiniteState (bind {source with clock := source.clock - paid} name answer) continuation = (none,inner) ∧
      post = restore source name inner := by
  exact success_prefix source post account emptyHash image emptyGlobal emptyArena installed name expression continuation read none (Or.inl rfl) normal

end InitECandidate.Solver.Mpt.AccountIsEmpty

#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.call_cost
#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.success_prefix
#print axioms InitECandidate.Solver.Mpt.AccountIsEmpty.none_prefix
