import InitECandidate.Solver.Mpt.WitnessDecodeProgram
import InitECandidate.Solver.Mpt.FailGuard
import InitECandidate.Solver.Input.PureDecision
import InitECandidate.Solver.Input.SequenceChoice

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem string_body_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code stringBody 1 :=
  Input.ClockCost.sequence code _ _ 0 1
    (Input.ClockCost.of_quiet code _ ((Input.PureDecision.ite _ (.returned _) .skip).quiet code)) (Fail.call_price code installed [.const 4#64])

theorem string_body_no_pass (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : Input.OriginalCode.Installed source.code) :
    (evaluateHOLFiniteState source stringBody).1≠none := by
  intro passed
  have normal : evaluateHOLFiniteState source stringBody=(none,(evaluateHOLFiniteState source stringBody).2):=Prod.ext passed rfl
  obtain ⟨middle,guardRun,failRun⟩:=Input.sequence_none source _ _ _ normal
  have codeEq:=(Input.evaluation_fields source middle _ none guardRun).2.2.2
  have currentInstalled : Input.OriginalCode.Installed middle.code:=by rw [codeEq]; exact installed
  exact Fail.call_not_normal middle _ currentInstalled [.const 4#64] failRun

theorem string_guard_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer header payload flag : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag)) :
    evaluateHOLFiniteState source stringGuard=if flag=0#64 then evaluateHOLFiniteState source stringBody else (none,source) := by
  by_cases zero : flag=0#64
  · simp [stringGuard,field,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · simp [stringGuard,field,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]

/-- Original237 reaches the real list-to-slices call only for an actual
parsed list. Empty-string return and all MPT failures keep their one-tick
allowance; no successful list conversion is an entry assumption. -/
theorem slices_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer header payload flag : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (binary : flag=0#64 ∨ flag=1#64) (installed : Input.OriginalCode.Installed source.code)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (WitnessStep.afterRlp .decode)=(outcome,post)) :
    source.clock-post.clock≤1 ∨ flag=1#64 ∧ evaluateHOLFiniteState source slicesCall=(outcome,post) := by
  have guardRun:=string_guard_execute source pointer header payload flag itemCell
  by_cases zero : flag=0#64
  · have stops : (evaluateHOLFiniteState source stringGuard).1≠none:=by rw [guardRun,if_pos zero]; exact string_body_no_pass source installed
    rw [suffix_shape,Input.sequence_stopped source stringGuard slicesCall stops,guardRun,if_pos zero] at run
    have price:=string_body_price source.code installed source rfl
    rw [run] at price
    exact Or.inl price
  · rw [if_neg zero] at guardRun
    rw [suffix_shape,evaluateHOLFiniteState_seq_line780,guardRun] at run
    exact Or.inr ⟨binary.resolve_left zero,run⟩

/-- A real normal string branch can only be the literal empty-node result,
and returns at its unchanged memory/global state with locals cleared. -/
theorem string_body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer header payload flag : BitVec 64)
    (itemCell : source.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source stringBody=(some (.returned value),post)) :
    payload=0#64 ∧ value=.rStruct [.val (.word 0#64),.val (.word 0#64)] ∧ post=emptyLocalsHOLFinite source := by
  have selected : evaluateHOLFiniteState source (.ite (.cmp .equal (field "it" 2) (.const 0#64)) emptyReturn .skip)=
      if payload=0#64 then evaluateHOLFiniteState source emptyReturn else (none,source):=by
    by_cases zero : payload=0#64
    · simp [field,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    · simp [field,evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,itemCell,Rlp.Item.result,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  have choice:=Input.sequence_choice source _ emptyReturn (fail 4#64) (payload=0#64) selected (Input.NoFallthrough.returned _)
  change evaluateHOLFiniteState source stringBody=if payload=0#64 then evaluateHOLFiniteState source emptyReturn else evaluateHOLFiniteState source (fail 4#64) at choice
  rw [choice] at normal
  by_cases zero : payload=0#64
  · rw [if_pos zero] at normal
    obtain ⟨read,postEq⟩:=Input.return_normal source post (.rstruct [.const 0#64,.const 0#64]) value normal
    exact ⟨zero,Option.some.inj read.symm,postEq⟩
  · rw [if_neg zero] at normal
    exact (Input.NoReturn.ignored_call (ofString "mpt_fail") [.const 4#64] source value (congrArg Prod.fst normal)).elim

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.string_body_price
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.string_body_no_pass
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.string_guard_execute
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.slices_trace
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.string_body_normal
