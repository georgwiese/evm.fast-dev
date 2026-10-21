import InitECandidate.Solver.MutableTable.FindAnyStep
import InitECandidate.Solver.Input.ReturnFacts

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The probe suffix can only return its real current slot. Its ordinary
counter assignment cannot manufacture a caller return. -/
theorem after_equal_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (index : BitVec 64)
    (iCell : source.locals.lookup (ofString "i")=some (.val (.word index))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterEqual=(some (.returned value),post)) : value=.val (.word index) := by
  have read : eval source (localVar "i")=some (.val (.word index)) := by simp [eval,localVar,evalHOLExact,toExact,iCell]
  have front:=Input.ReturnFacts.conditional source equalTest (.return (localVar "i")) .skip (fun returned=>returned=.val (.word index))
    (Input.ReturnFacts.returned source _ (.val (.word index)) _ read rfl) (Input.ReturnFacts.skip source _)
  have full:=Input.ReturnFacts.sequence source (.ite equalTest (.return (localVar "i")) .skip) (.assign .local (ofString "i") nextIndex)
      (fun returned=>returned=.val (.word index)) front (by
    intro middle passed target returned run
    have safe : Input.LocalPrefix (ofString "n") (.assign .local (ofString "i") nextIndex) := .assign _ _ (by decide)
    exact ((safe.summary_full middle).2.1 returned (congrArg Prod.fst run)).elim)
  exact full post value normal

/-- Every genuine return from the original comparison caller selects its
actual occupied index, independently of query mapping and comparator values. -/
theorem any_step_returned (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p : Parameters) (index : BitVec 64)
    (locals : Locals source p index) (keyLength : p.keyLength=32#64)
    (code : source.code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source loopBody=(some (.returned value),post)) : value=.val (.word index) := by
  obtain ⟨callee,called,aCell,bCell,nCell⟩ := MemeqByteRuntime.environment source.code.lookup (p.keys+index*p.stride) p.key 32 code
  have args:=general_comparison_arguments source p index .word locals keyLength
  obtain ⟨funded,target,returned,inner,bodyRun,checked,continued,endpoint⟩ := Input.CallNormal.scoped_normal source post "eq" .one (ofString "memeq") comparisonArguments _
    Memeq32.body afterEqual callee .one args called value normal
  have currentI : (Input.CallNormal.continuationEntry source target "eq" returned).locals.lookup (ofString "i")=some (.val (.word index)) :=
    (Input.CallNormal.continuation_lookup_other source target "eq" "i" returned (by decide)).trans locals.index
  exact after_equal_returned _ inner index currentI value continued

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.after_equal_returned
#print axioms InitECandidate.Solver.MutableTable.Find.any_step_returned
