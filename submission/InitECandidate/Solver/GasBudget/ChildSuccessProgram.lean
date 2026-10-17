import InitECandidate.Solver.GasBudget.Repayment

namespace InitECandidate.Solver.GasBudget.ChildSuccess
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn_incorporate_child_on_success with | .function fn=>progToHOL fn.body | _=>.skip
def suffix : ProgHOL 64 := match body with
  | .seq _ (.seq _ (.dec _ _ _ (.seq _ (.seq _ (.seq _ (.seq _ tail))))))=>tail
  | _=>.skip
def program (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "incorporate_child_on_error") [localVar "child"])
    (.seq (ChildError.sumStore 192#64) (Repayment.program continuation))

theorem body_shape : body=program suffix := by
  simp only [body,program,suffix,Guest.guestFn_incorporate_child_on_success,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,ChildError.sumStore,ChildError.childLoad,Repayment.program,Repayment.choose,
    Repayment.stores,Repayment.gasExpression,Repayment.stateExpression,Repayment.spillExpression,frameAddress,frameLoad,localVar]
  rfl

structure Ready (source : PanSemStateFiniteExact 64 Guest.HostMemory) (parent child : BitVec 64)
    (p c : ChildError.Amounts) (parentSpill childSpill : BitVec 64) : Prop extends ChildError.Ready source parent child p c where
  parentSpillMapped : source.memaddrs (parent+192#64)
  childSpillMapped : source.memaddrs (child+192#64)
  parentSpillCell : source.memory (parent+192#64)=.word parentSpill
  childSpillCell : source.memory (child+192#64)=.word childSpill
  childSpillSeparate : ∀ offset∈ChildError.offsets,parent+BitVec.ofNat 64 offset≠child+192#64

end InitECandidate.Solver.GasBudget.ChildSuccess

#print axioms InitECandidate.Solver.GasBudget.ChildSuccess.body_shape
