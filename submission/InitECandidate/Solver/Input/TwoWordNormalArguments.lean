import InitECandidate.Solver.Input.MemoryWordCalls
import InitECandidate.Solver.Input.IgnoredCallData

namespace InitECandidate.Solver.Input.MemoryWordCalls
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- An actual normal two-word writer call derives its second scalar
argument from that same call's real argument evaluation and ABI check.
No mapped-read success or future callee result is an entry assumption. -/
theorem normal_arguments (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (function : MlS) (body : ProgHOL 64)
    (first second : ExpHOL 64) (pointer : BitVec 64)
    (code : source.code.lookup function=some (formals,body,.one))
    (firstRead : eval source first=some (.val (.word pointer)))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) function [first,second])=(none,post)) :
    ∃ word : BitVec 64,evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [first,second]=some [.val (.word pointer),.val (.word word)] := by
  classical
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ := CallNormal.ignored_data source post function [first,second] run
  cases secondRead : eval source second with
  | none=>
    simp only [eval] at firstRead secondRead
    simp [evalListHOLFinite,evalListHOLExact,firstRead,secondRead] at actualArgs
  | some value=>
    have expected : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [first,second]=some [.val (.word pointer),value] := by
      simp only [eval] at firstRead secondRead
      simp [evalListHOLFinite,evalListHOLExact,firstRead,secondRead]
    have valuesEq : actualValues=[.val (.word pointer),value] := Option.some.inj (actualArgs.symm.trans expected)
    subst actualValues
    have raw := lookupCodeHOLFinite_eq_some source.code.lookup function [.val (.word pointer),value] actualBody actualCallee actualShape actualCalled
    have scalar : ∃ word : BitVec 64,value=.val (.word word) := by
      cases value with
      | val word=>cases word with | word word=>exact ⟨word,rfl⟩
      | rStruct values=>simp [lookupCodeHOLExact,code,formals,shapeEqHOL,shapeOfHOLExact] at raw
      | nStruct name values=>simp [lookupCodeHOLExact,code,formals,shapeEqHOL,shapeOfHOLExact] at raw
    obtain ⟨word,rfl⟩ := scalar
    exact ⟨word,expected⟩

end InitECandidate.Solver.Input.MemoryWordCalls

#print axioms InitECandidate.Solver.Input.MemoryWordCalls.normal_arguments
