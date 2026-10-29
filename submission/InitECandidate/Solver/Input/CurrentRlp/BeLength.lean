import InitECandidate.Solver.Input.CurrentRlp.Code
import InitECandidate.Solver.Input.RlpLength.BeBuilt
import InitECandidate.Solver.Input.LocalEffects
import InitECandidate.Solver.Input.ClockCostCurrentCall
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.CurrentRlp.BeLength
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

abbrev body := Code.body .beLength

/-- The reused shift-loop syntax is literally the current software body. -/
theorem current_body : body=RlpLength.Be.body:=rfl

theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "rlp_be_len")=some ([(ofString "v",.one)],body,.one) := by
    have known:=Code.installed code installed .beLength
    simpa only [Code.name,Code.formals,Code.shape,Code.entry,Code.declaration,GasBudget.OriginalCodeEnvironment.originalEntry,
      declToHOL,funDeclToHOL,Guest.Software.guestFn_rlp_be_len,paramToHOL,shapeToHOL,List.map_cons,List.map_nil] using known

/-- Every current byte-length outcome needs at most eight loop ticks,
including a short entry clock. No memory or later success is required. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (cell : source.locals.lookup (ofString "v")=some (.val (.word word))) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤8 := by
  rw [current_body]
  by_cases funded : 8≤source.clock
  · obtain ⟨target,count,bound,run,frame⟩:=RlpLength.Be.execute source word cell funded
    have clock:=congrArg PanSemStateFiniteExact.clock frame
    change target.clock=source.clock-count at clock
    rw [run]
    change source.clock-target.clock≤8
    omega
  · omega

/-- An actual returned value is its true byte count, bounded by eight.
Clock padding identifies that same value even below the conservative cost. -/
theorem body_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (cell : source.locals.lookup (ofString "v")=some (.val (.word word)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    ∃ count : Nat,count≤8 ∧ value=.val (.word (BitVec.ofNat 64 count)) ∧
      source.clock-target.clock≤8 ∧ LocalEffects.erase target=LocalEffects.erase source := by
  let padded:={source with clock:=source.clock+8}
  obtain ⟨post,count,bounded,run,frame⟩:=RlpLength.Be.execute padded word cell (by change 8≤source.clock+8; omega)
  rw [←current_body] at run
  have lifted:=panPropsEvaluateAddClockEq body source (some (.returned value)) target 8 ⟨normal,by intro impossible; cases impossible⟩
  have same:=lifted.symm.trans run
  have answer:=PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst same))
  have endpoint:=congrArg Prod.snd same
  change {target with clock:=target.clock+8}=post at endpoint
  rw [←endpoint] at frame
  have metadata:=congrArg LocalEffects.erase frame
  have price:=body_cost source word cell
  rw [normal] at price
  exact ⟨count,bounded,answer,price,metadata⟩

/-- The actual current caller entry comes from the installed software map. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (expression : ExpHOL 64) (word : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (read : WitnessRadix.QueryBranch.eval source expression=some (.val (.word word))) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,none)) (ofString "rlp_be_len") [expression])).2.clock≤9 := by
  have code:=original_code source.code installed
  obtain ⟨callee,called,cell⟩:=CallNormal.unary_environment source.code.lookup (ofString "rlp_be_len") "v" body word code
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [expression]=some [.val (.word word)]:=by
    simp only [WitnessRadix.QueryBranch.eval] at read
    simp [evalListHOLFinite,evalListHOLExact,read]
  exact ClockCost.call_current source (some none) (ofString "rlp_be_len") [expression] [.val (.word word)] body callee .one 8 args called
    (body_cost (callEntryStateHOLFinite source callee) word cell)

end InitECandidate.Solver.Input.CurrentRlp.BeLength

#print axioms InitECandidate.Solver.Input.CurrentRlp.BeLength.current_body
#print axioms InitECandidate.Solver.Input.CurrentRlp.BeLength.body_cost
#print axioms InitECandidate.Solver.Input.CurrentRlp.BeLength.body_normal
#print axioms InitECandidate.Solver.Input.CurrentRlp.BeLength.call_cost

#print axioms InitECandidate.Solver.Input.CurrentRlp.BeLength.original_code
