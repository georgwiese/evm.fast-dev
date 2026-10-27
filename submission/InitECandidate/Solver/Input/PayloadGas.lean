import Guest.SoftwareAst
import InitECandidate.Solver.Input.FlatScalar

namespace InitECandidate.Solver.Input.Scalar
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def stores : ProgHOL 64→List (ExpHOL 64×ExpHOL 64)
  | .store destination value=>[(destination,value)]
  | .seq first second=>stores first++stores second
  | .dec _ _ _ rest=>stores rest
  | .decCall _ _ _ _ rest=>stores rest
  | .ite _ first second=>stores first++stores second
  | .while _ code=>stores code
  | _=>[]
def payloadBody : ProgHOL 64 := match Guest.Software.guestFn_decode_payload with
  | .function fn=>progToHOL fn.body | _=>.skip
def gasStore : ExpHOL 64×ExpHOL 64 := ((stores payloadBody)[15]?).getD (.const 0#64,.const 0#64)
def gasExpression : ExpHOL 64 := gasStore.2

/-- Exact literal gas-field store extracted from the fixed guest, including
its flattened additions and nested high-word macro expansion. -/
theorem gas_store_shape : gasStore=(plus (localVar "pl") 88,flat64 (localVar "p") [412]) := by
  simp only [gasStore,payloadBody,stores,Guest.Software.guestFn_decode_payload,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,List.getElem?_cons_zero,
    List.getElem?_cons_succ,Option.getD_some,Option.map_none,plus,flat64,flat32,flatAddress,localVar,shift]

theorem gas_expression_shape : gasExpression=flat64 (localVar "p") [412] :=
  congrArg Prod.snd gas_store_shape

/-- The fixed decoder's actual gas expression obeys the declared-gas premise
when the reachable copied-byte and container-position invariants hold. -/
theorem payload_gas_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (heap : Blob.HeapInput source input pointer) (inside : 482≤input.length%2^64)
    (payloadLocal : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (request : Guest.GasLimit.le32 input 2=16) (payload : Guest.GasLimit.le32 input 18=44)
    (gas : Guest.GasLimit.declaredGasLimit input≤200000000) :
    ∃ value : BitVec 64,eval source gasExpression=some (.val (.word value)) ∧ value.toNat≤200000000 := by
  classical
  have baseRead : eval source (localVar "p")=some (.val (.word (pointer+62#64))) := by
    simpa [eval,localVar,evalHOLExact,toExact] using payloadLocal
  have fieldRead : eval source (flatAddress (localVar "p") [412])=some (.val (.word (pointer+474#64))) := by
    simpa [BitVec.add_assoc] using flat_read source (localVar "p") (pointer+62#64) [412] baseRead
  have equal:=flat64_equiv source (localVar "p") (pointer+62#64) [412] baseRead
  rw [gas_expression_shape,equal]
  exact gas_read source input pointer _ heap inside fieldRead request payload gas

end InitECandidate.Solver.Input.Scalar

#print axioms InitECandidate.Solver.Input.Scalar.gas_store_shape
#print axioms InitECandidate.Solver.Input.Scalar.gas_expression_shape
#print axioms InitECandidate.Solver.Input.Scalar.payload_gas_read
