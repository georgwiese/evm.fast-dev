import InitECandidate.Solver.MutableTable.FindAnyHashTrace

namespace InitECandidate.Solver.MutableTable.Find
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Price the continuation only at the real word returned by the original
hash. Failed hashes retain the one caller tick; no query memory is assumed. -/
theorem any_hash_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (query : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word query)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word 32#64)))
    (code : source.code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one))
    (price : Nat)
    (tail : ∀ hash,let current:=QueryBranch.bind {source with clock:=source.clock-1} "h" hash;
      current.clock-(evaluateHOLFiniteState current afterHash).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source hashCall).2.clock≤price+1 := by
  let output:=evaluateHOLFiniteState source hashCall
  rcases any_hash_trace source output.2 query keyCell lengthCell code output.1 rfl with stopped|reached
  · exact stopped.trans (by omega)
  · obtain ⟨hash,inner,funded,continued,endpoint⟩ := reached
    have back:=tail hash
    dsimp only at back
    have forward:=evaluateHOLFiniteState_clock_le (QueryBranch.bind {source with clock:=source.clock-1} "h" hash) afterHash
    rw [continued] at back forward
    change source.clock-1-inner.clock≤price at back
    change inner.clock≤source.clock-1 at forward
    have finalClock : output.2.clock=inner.clock := (congrArg PanSemStateFiniteExact.clock endpoint).trans (restore_clock source inner "h")
    change source.clock-output.2.clock≤price+1
    omega

end InitECandidate.Solver.MutableTable.Find

#print axioms InitECandidate.Solver.MutableTable.Find.any_hash_call_cost
