import InitECandidate.Solver.Input.CurrentHash.RequestListCallCost
import InitECandidate.Solver.Input.Requests.DecodedBudget

namespace InitECandidate.Solver.Input.CurrentHash.RequestsHash
open Flapjack PanSemStateFiniteExact
set_option maxRecDepth 100000

def listPrices (counts : Nat→BitVec 64) : Nat :=
  (RequestList.kinds.map (fun kind=>RequestList.price kind (counts kind.tag).toNat+1)).sum

/-- The five actual list allowances use one encoded request budget. Each
selected per-record coefficient is at most13times its real encoded size. -/
theorem list_prices_budget {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob cursor : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (data : Requests.DecodedImage input source blob cursor start size counts) : listPrices counts≤13*(size-20)+15870 := by
  have budget := data.byte_budget
  change (1515*(counts 0).toNat+3174)+((970*(counts 1).toNat+3174)+((1234*(counts 2).toNat+3174)+
    ((1369*(counts 3).toNat+3174)+(824*(counts 4).toNat+3174))))≤13*(size-20)+15870
  omega

end InitECandidate.Solver.Input.CurrentHash.RequestsHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RequestsHash.list_prices_budget
