import InitECandidate.Solver.Input.CurrentTable.NewLeaf.ModelFields

namespace InitECandidate.Solver.Input.CurrentTable
open Flapjack PanSemStateFiniteExact

theorem NewLeaf.model_code (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table cap node pos pointer value : BitVec 64) :
    (model source table cap node pos pointer value).code = source.code := MemoryMetadata.code (model_metadata source table cap node pos pointer value)

end InitECandidate.Solver.Input.CurrentTable

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.model_code
