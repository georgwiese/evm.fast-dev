import InitECandidate.Solver.Headers.PipelineObligations
import InitECandidate.Solver.Headers.CurrentHelpers.Body

namespace InitECandidate.Solver.Headers.CurrentPipeline
open Pipeline
open Flapjack PanSemStateFiniteExact

def price (items : List Rlp.ListItem) (current : BitVec 64) : Code→Nat
  | .done | .returned=>0
  | .store _ _ rest | .guard _ _ _ rest=>price items current rest
  | .declare _ kind index _ rest | .assign _ kind index _ rest=>CurrentHelpers.bodyPrice kind (rowBytes items index)+1+price items current rest
  | .choose yes no rest=>(if current=0#64 then price items current no else price items current yes)+price items current rest


end InitECandidate.Solver.Headers.CurrentPipeline
