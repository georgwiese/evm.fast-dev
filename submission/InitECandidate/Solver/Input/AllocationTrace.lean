import InitECandidate.Solver.WitnessRadix.AllocationCall
import InitECandidate.Solver.Input.NonTimeoutScopedCall

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- A real allocating scope derives its funded caller tick from the same
observed non-timeout execution. No later successful allocation is assumed. -/
theorem call_trace {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64) (pointer amount : BitVec 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values amount))
    (code : source.code.lookup (ofString "alloc")=some (formals,body,.one))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (fits : pointer.toNat+amount.toNat≤33806089496)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments continuation)=(result,target))
    (notTimeout : result≠some .timeOut) :
    1≤source.clock ∧ ∃ final,
      evaluateHOLFiniteState (bind (post {source with clock:=source.clock-1} pointer amount) name pointer) continuation=(result,final) ∧
      target=restore source name final := by
  obtain ⟨callee,called,amountLocal⟩ := environment source.code.lookup amount code
  have funded := (Input.scoped_call_non_timeout source target (ofString name) .one (ofString "alloc") arguments (values amount) body continuation callee .one args called result run notTimeout).1
  have actual := call_execute source name arguments continuation pointer amount args code heap fits funded
  have remaining := actual.symm.trans run
  let final := (evaluateHOLFiniteState (bind (post {source with clock:=source.clock-1} pointer amount) name pointer) continuation).2
  have observed := congrArg Prod.fst remaining
  have endpoint := congrArg Prod.snd remaining
  exact ⟨funded,final,Prod.ext observed rfl,endpoint.symm⟩

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.call_trace
