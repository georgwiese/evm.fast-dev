import InitECandidate.Solver.Input.VarList.FundedTrace
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All actual non-timeout variable-list outcomes at any clock budget.
Malformed header/count/record exits are bounded alongside normal returns. -/
theorem body_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array limit : BitVec 64) (start length : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+length≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (l : source.locals.lookup (ofString "lim")=some (.val (.word limit)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (lower : 2701131776≤pointer.toNat) (aligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (arrayAfter : pointer.toNat+input.length%2^64+8≤array.toNat)
    (arrayRoom : array.toNat+4*length≤33806089496)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word array)))
    (allocCode : source.code.lookup (ofString "alloc")=some (WitnessRadix.PersistentAlloc.formals,WitnessRadix.PersistentAlloc.body,.one))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body = (result,post)) (notTimeout : result ≠ some .timeOut) :
    source.clock - post.clock ≤ length/4+2 ∧
      ((∃ value,result = some (.returned value)) ∨ ∃ error : BitVec 64,
        (error=20#64 ∨ error=21#64 ∨ error=22#64 ∨ error=23#64) ∧ result=some (.exception (ofString "SszErr") (.val (.word error)))) := by
  let padding := length/4+2
  have paddedRun := panPropsEvaluateAddClockEq body source result post padding ⟨run,notTimeout⟩
  obtain ⟨cost,outcome⟩ := body_trace_funded {source with clock:=source.clock+padding} {post with clock:=post.clock+padding}
    input pointer array limit start length heap inside p n l domain lower aligned arrayAligned arrayAfter arrayRoom heapGlobal allocCode failCode exceptionShape
    (by change length/4+2≤source.clock+padding; dsimp only [padding]; omega) result paddedRun
  change source.clock+padding-(post.clock+padding)≤length/4+2 at cost
  exact ⟨by omega,outcome⟩

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.body_trace
