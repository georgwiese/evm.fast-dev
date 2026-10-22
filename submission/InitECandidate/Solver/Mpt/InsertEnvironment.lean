import InitECandidate.Solver.Mpt.InsertEmptyCost
import InitECandidate.Solver.WitnessRadix.CodeEnvironment
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def values (node key length level pointer size : BitVec 64) : List (ValueHOL 64):=
  [.val (.word node),.val (.word key),.val (.word length),.val (.word level),.val (.word pointer),.val (.word size)]
def rawLocals (node key length level pointer size : BitVec 64) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "vlen" then some (.val (.word size)) else if name=ofString "vptr" then some (.val (.word pointer))
  else if name=ofString "level" then some (.val (.word level)) else if name=ofString "klen" then some (.val (.word length))
  else if name=ofString "key" then some (.val (.word key)) else if name=ofString "node" then some (.val (.word node)) else none

/-- The six literal original insertion formals determine the real callee
environment; no callee execution or successful argument read is assumed. -/
theorem environment (table : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (node key length level pointer size : BitVec 64) (known : table (ofString "_mpt_insert_node")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "_mpt_insert_node") (values node key length level pointer size)=some (body,callee,.one) ∧
      callee.lookup (ofString "node")=some (.val (.word node)) ∧ callee.lookup (ofString "key")=some (.val (.word key)) ∧
      callee.lookup (ofString "klen")=some (.val (.word length)) ∧ callee.lookup (ofString "level")=some (.val (.word level)) ∧
      callee.lookup (ofString "vptr")=some (.val (.word pointer)) ∧ callee.lookup (ofString "vlen")=some (.val (.word size)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values node key length level pointer size).length ∧
      ((formals.zip (values node key length level pointer size)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true:=by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact table (ofString "_mpt_insert_node") (values node key length level pointer size)=
      some (body,rawLocals node key length level pointer size,.one):=by
    simp only [lookupCodeHOLExact,known,valid,if_pos]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_,?_,?_,?_⟩ <;> rw [locals] <;> simp [rawLocals,ofString]

/-- A true tail, ignored, or assigned empty-root insertion call costs at
most five source ticks at every outcome, including a failed child. -/
theorem empty_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key length level pointer size : BitVec 64) (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=
      some (values 0#64 key length level pointer size)) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "_mpt_insert_node") arguments)).2.clock≤5 := by
  obtain ⟨callee,called,node,_,_,_,_,_⟩:=environment source.code.lookup 0#64 key length level pointer size (original_code source.code installed)
  exact Input.ClockCost.call_current source destination (ofString "_mpt_insert_node") arguments _ body callee .one 4 args called
    (empty_body_cost (callEntryStateHOLFinite source callee) node installed)

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.environment
#print axioms InitECandidate.Solver.Mpt.Insert.empty_call_cost
