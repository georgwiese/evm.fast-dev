import InitECandidate.Solver.Input.HeapScope
import InitECandidate.Solver.Input.NonTimeoutScopedCall

namespace InitECandidate.Solver.Input.HeapScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- An actual original heap_mark call reaches its saved-pointer binding at
any observed non-timeout clock. The enclosing result is unrestricted. -/
theorem mark_call_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark : BitVec 64)
    (name : String) (continuation : ProgHOL 64)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)))
    (code : source.code.lookup (ofString "heap_mark")=some ([],markBody,.one))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "heap_mark") [] continuation)=(result,post)) (notTimeout : result≠some .timeOut) :
    1≤source.clock ∧ ∃ final,evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name mark) continuation=(result,final) ∧ post=restore source name final := by
  have raw : lookupCodeHOLExact source.code.lookup (ofString "heap_mark") []=some (markBody,(fun _=>none),.one) := by
    simp [lookupCodeHOLExact,code]
  obtain ⟨callee,called,locals⟩ := WitnessRadix.CodeEnvironment.finite_lookup source.code.lookup (ofString "heap_mark") [] markBody (fun _=>none) .one raw
  have funded := (scoped_call_non_timeout source post (ofString name) .one (ofString "heap_mark") [] [] markBody continuation callee .one rfl called result run notTimeout).1
  have actual := mark_call_execute source mark name continuation heap code funded
  have remaining := actual.symm.trans run
  let final := (evaluateHOLFiniteState (bind {source with clock:=source.clock-1} name mark) continuation).2
  have observed := congrArg Prod.fst remaining
  have endpoint := congrArg Prod.snd remaining
  exact ⟨funded,final,Prod.ext observed rfl,endpoint.symm⟩

end InitECandidate.Solver.Input.HeapScope

#print axioms InitECandidate.Solver.Input.HeapScope.mark_call_trace
