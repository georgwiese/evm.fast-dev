import InitECandidate.Solver.Input.VarList.RecordCells

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem normal_count_limit (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer limit : BitVec 64) (start length : Nat) (heap : Blob.HeapInput source input pointer)
    (inside : start+length≤input.length%2^64)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word (BitVec.ofNat 64 length))))
    (l : source.locals.lookup (ofString "lim")=some (.val (.word limit)))
    (failCode : source.code.lookup (ofString "ssz_fail")=some (SszFail.formals,SszFail.body,.one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr")=some .one) (enough : 1≤source.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) : decodedCount input start length≤limit.toNat := by
  have parsed:=normal_entry source post input pointer limit start length heap inside p n l failCode exceptionShape enough value run
  rcases parsed with empty|nonempty
  · simp [decodedCount,empty.1]
  · obtain ⟨minimum,positive,header,upper,bound,rest⟩:=nonempty
    simpa only [decodedCount,if_neg (show length≠0 from by omega)] using bound

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.normal_count_limit
