import InitECandidate.Solver.Input.CurrentHash.PayloadStaticProgram

namespace InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

private theorem offset_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (offset : Nat) (p : BitVec 64)
    (pointer : source.locals.lookup (ofString name)=some (.val (.word p))) :
    evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (FixedRecord.offsetExpression name offset)=some (.val (.word (p+BitVec.ofNat 64 offset))) := by
  by_cases zero : offset=0
  · subst offset; simp [FixedRecord.offsetExpression,localVar,evalHOLFinite,evalHOLExact,toExact,pointer]
  · simp [FixedRecord.offsetExpression,zero,localVar,evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,pointer,valueIsWord,valueWord,wordOpHOL,wordOp]

theorem arguments_read (field : Field) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (raw ch : BitVec 64)
    (pointer : source.locals.lookup (ofString "raw")=some (.val (.word raw)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) :
    evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (arguments field)=some (field.values raw ch) := by
  have inputRead : evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) (inputExpression field)=some (.val (.word (raw+BitVec.ofNat 64 field.inputOffset))) := by
    simp [evalHOLFinite,evalHOLExact,evalListHOLExact,toExact,inputExpression,localVar,pointer,valueIsWord,valueWord,wordOpHOL,wordOp]
  have outputRead := offset_read source "ch" (32*field.field) ch chunks
  simp only [evalHOLFinite] at inputRead outputRead
  cases field <;> simp only [arguments,FixedRecord.Step.values,FixedRecord.Step.inputOffset,FixedRecord.Step.field] at inputRead outputRead ⊢
  all_goals simp only [outputExpression,evalListHOLFinite,evalListHOLExact,inputRead,outputRead,FixedRecord.scalarValues,CopyGeneral.values,BytesCallCost.values,evalHOLExact]

/-- Literal payload field expressions, including raw+0, have the same actual
source call result/state as the shared argument interface. Target straight-line
work must still be counted for the literal current program. -/
theorem argument_equivalence (field : Field) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (raw ch : BitVec 64)
    (pointer : source.locals.lookup (ofString "raw")=some (.val (.word raw)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) :
    evaluateHOLFiniteState source (step field)=evaluateHOLFiniteState source (field.program "raw") :=
  CallArguments.equivalent source (some (none,none)) field.function (arguments field) (field.arguments "raw")
    ((arguments_read field source raw ch pointer chunks).trans (field.arguments_read source "raw" raw ch pointer chunks).symm)

theorem program_equivalence (fields : List Field) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (raw ch : BitVec 64) (tail : ProgHOL 64)
    (pointer : source.locals.lookup (ofString "raw")=some (.val (.word raw)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch))) :
    evaluateHOLFiniteState source (program fields tail)=evaluateHOLFiniteState source (FixedRecord.pipeline "raw" fields tail) := by
  induction fields generalizing source with
  | nil=>rfl
  | cons field rest ih=>
    change evaluateHOLFiniteState source (.seq (step field) (program rest tail))=evaluateHOLFiniteState source (.seq (field.program "raw") (FixedRecord.pipeline "raw" rest tail))
    rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_seq_line780,argument_equivalence field source raw ch pointer chunks]
    generalize computed : evaluateHOLFiniteState source (field.program "raw")=output
    obtain ⟨result,target⟩ := output
    cases result with
    | none=>
      have kept (name : String) := CallNormal.ignored_lookup source target (ofString name) field.function (field.arguments "raw") computed
      exact ih target ((kept "raw").trans pointer) ((kept "ch").trans chunks)
    | some result=>rfl

/-- Share the checked field prices for the literal current payload prefix,
with all non-timeout stopping paths and the actual continuing prefix retained. -/
theorem program_cost (fields : List Field) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (raw ch : BitVec 64) (tail : ProgHOL 64) (tailPrice : Nat)
    (valid : ∀ field∈fields,field.Valid) (installed : OriginalCode.Installed source.code)
    (pointer : source.locals.lookup (ofString "raw")=some (.val (.word raw)))
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (tailCost : ∀ middle,evaluateHOLFiniteState source (program fields .skip)=(none,middle) → ∀ result target,
      evaluateHOLFiniteState middle tail=(result,target) → result≠some .timeOut → middle.clock-target.clock≤tailPrice)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source (program fields tail)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤(fields.map FixedRecord.Step.price).sum+tailPrice := by
  have canonical := (program_equivalence fields source raw ch tail pointer chunks).symm.trans actual
  exact FixedRecord.pipeline_cost fields "raw" tail tailPrice valid source post raw ch installed pointer chunks
    (by intro middle normal observed target evaluated notTimeout
        exact tailCost middle ((program_equivalence fields source raw ch .skip pointer chunks).trans normal) observed target evaluated notTimeout)
    result canonical notTimeout

end InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields

#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.arguments_read
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.argument_equivalence
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.program_equivalence
#print axioms InitECandidate.Solver.Input.CurrentHash.PayloadHash.StaticFields.program_cost
