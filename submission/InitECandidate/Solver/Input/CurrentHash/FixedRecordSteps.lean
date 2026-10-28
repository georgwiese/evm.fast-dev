import InitECandidate.Solver.Input.CurrentHash.FixedRecordProgram
import InitECandidate.Solver.Input.CurrentHash.FixedHashCost
import InitECandidate.Solver.Input.CurrentHash.BytesCallCost
import InitECandidate.Solver.Input.ClockCostTerminatingSequence
import InitECandidate.Solver.Input.IgnoredCallLookup

namespace InitECandidate.Solver.Input.CurrentHash.FixedRecord
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def Step.Valid : Step → Prop
  | .vector _ length _ depth => length+64<2^64 ∧ depth<58 ∧ PackBytes.chunks length≤2^depth
  | _ => True

theorem steps_valid (kind : Kind) : ∀ step ∈ kind.steps, step.Valid := by
  cases kind <;> simp [Kind.steps, Step.Valid, PackBytes.chunks]

def scalarValues (p out : BitVec 64) : List (ValueHOL 64) := [.val (.word p), .val (.word out)]
def Step.values (step : Step) (p ch : BitVec 64) : List (ValueHOL 64) :=
  let input := p+BitVec.ofNat 64 step.inputOffset
  let output := ch+BitVec.ofNat 64 (32*step.field)
  match step with
  | .scalar _ _ => scalarValues input output
  | .copy _ _ => CopyGeneral.values output input 32
  | .vector _ length _ _ => BytesCallCost.values .vector input 0#64 output length

private theorem offset_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (offset : Nat) (p : BitVec 64)
    (pointer : source.locals.lookup (ofString name)=some (.val (.word p))) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (offsetExpression name offset)=some (.val (.word (p+BitVec.ofNat 64 offset))) := by
  by_cases zero : offset=0
  · subst offset; simp [offsetExpression,localVar,evalHOLFinite,evalHOLExact,toExact,pointer]
  · simp [offsetExpression,zero,localVar,evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,pointer,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem Step.arguments_read (step : Step) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (inputName : String) (p ch : BitVec 64)
    (pointer : source.locals.lookup (ofString inputName)=some (.val (.word p)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (step.arguments inputName)=some (step.values p ch) := by
  have inputRead := offset_read source inputName step.inputOffset p pointer
  have outputRead := offset_read source "ch" (32*step.field) ch chunks
  simp only [evalHOLFinite] at inputRead outputRead
  cases step <;> simp only [Step.arguments,Step.values,Step.inputOffset,Step.field] at inputRead outputRead ⊢
  all_goals simp only [evalListHOLFinite,evalListHOLExact,inputRead,outputRead,scalarValues,CopyGeneral.values,BytesCallCost.values,evalHOLExact]


/-- Each field call uses the same actual input/ch locals; all failed reads,
stores and allocator paths remain in its observed non-timeout outcome. -/
theorem Step.cost (step : Step) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (inputName : String) (p ch : BitVec 64) (valid : step.Valid)
    (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString inputName) = some (.val (.word p)))
    (chunks : source.locals.lookup (ofString "ch") = some (.val (.word ch)))
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (step.program inputName) = (result, post)) (notTimeout : result ≠ some .timeOut) :
    source.clock-post.clock ≤ step.price := by
  have args := step.arguments_read source inputName p ch pointer chunks
  cases step with
  | scalar offset field =>
    have paid := FixedHashCost.u64_call source.code installed (some none) ((Step.scalar offset field).arguments inputName) source rfl
    change source.clock - (evaluateHOLFiniteState source ((Step.scalar offset field).program inputName)).2.clock ≤ 54 at paid
    rw [actual] at paid
    exact paid
  | copy offset field =>
    have paid := FixedMemoryCost.copy source.code installed (some none)
      (offsetExpression "ch" (32*field)) (offsetExpression inputName offset) 32 (by decide) source rfl
    change source.clock - (evaluateHOLFiniteState source ((Step.copy offset field).program inputName)).2.clock ≤ 42 at paid
    rw [actual] at paid
    exact paid
  | vector offset length field depth =>
    exact BytesCallCost.cost .vector source post (p+BitVec.ofNat 64 offset) 0#64 (ch+BitVec.ofNat 64 (32*field)) length depth
      installed valid.1 valid.2.1 valid.2.2 (by intro impossible; cases impossible)
      (some none) ((Step.vector offset length field depth).arguments inputName) args result actual notTimeout

/-- Finite field pipeline composition only needs caller word bindings. It
assumes no physical input mapping, temporary room or successful future hash. -/
theorem pipeline_cost (steps : List Step) (inputName : String) (tail : ProgHOL 64) (tailPrice : Nat)
    (valid : ∀ step ∈ steps, step.Valid)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p ch : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString inputName) = some (.val (.word p)))
    (chunks : source.locals.lookup (ofString "ch") = some (.val (.word ch)))
    (tailCost : ∀ middle, evaluateHOLFiniteState source (pipeline inputName steps .skip) = (none,middle) →
      ∀ result target, evaluateHOLFiniteState middle tail = (result,target) → result ≠ some .timeOut → middle.clock-target.clock≤tailPrice)
    (result : Option (PanSemResultExact 64))
    (actual : evaluateHOLFiniteState source (pipeline inputName steps tail) = (result,post)) (notTimeout : result ≠ some .timeOut) :
    source.clock-post.clock ≤ (steps.map Step.price).sum+tailPrice := by
  induction steps generalizing source post result with
  | nil =>
    simpa only [List.map_nil,List.sum_nil,Nat.zero_add] using tailCost source (evaluateHOLFiniteState_skip source) result post actual notTimeout
  | cons step rest ih =>
    change evaluateHOLFiniteState source (.seq (step.program inputName) (pipeline inputName rest tail)) = (result,post) at actual
    have paid := ClockCost.sequence_terminating source post _ _ step.price ((rest.map Step.price).sum+tailPrice)
      (fun result target evaluated notTimeout => step.cost source target inputName p ch (valid step (by simp)) installed pointer chunks result evaluated notTimeout)
      (by intro middle normal result target evaluated notTimeout
          have kept (name : MlS) := CallNormal.ignored_lookup source middle name step.function (step.arguments inputName) normal
          have nextCode : OriginalCode.Installed middle.code := by
            rw [(evaluation_fields source middle _ none normal).2.2.2]
            exact installed
          exact ih (by intro next member; exact valid next (by simp [member])) middle target nextCode
            ((kept _).trans pointer) ((kept _).trans chunks)
            (by intro final restRun observed endpoint tailRun notTimeout
                apply tailCost final ?_ observed endpoint tailRun notTimeout
                change evaluateHOLFiniteState source (.seq (step.program inputName) (pipeline inputName rest .skip)) = (none,final)
                rw [evaluateHOLFiniteState_seq_line780, normal]
                exact restRun) result evaluated notTimeout)
      result actual notTimeout
    simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using paid

end InitECandidate.Solver.Input.CurrentHash.FixedRecord

#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.steps_valid
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.Step.arguments_read
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.Step.cost
#print axioms InitECandidate.Solver.Input.CurrentHash.FixedRecord.pipeline_cost
