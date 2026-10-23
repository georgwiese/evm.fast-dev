import InitECandidate.Solver.Mpt.LeafInsertNormal
import InitECandidate.Solver.Mpt.SplitExtensionNormal
import InitECandidate.Solver.Input.WordQuadEnvironment

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def callValues (node key length pointer size : BitVec 64) : List (ValueHOL 64):=[.val (.word node),.val (.word key),.val (.word length),.val (.word pointer),.val (.word size)]

/-- Actual fixed original helper ABI, before assuming any callee result. -/
theorem environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node key length pointer size : BitVec 64)
    (known : source.code.lookup (ofString "_insert_into_leaf")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite source.code.lookup (ofString "_insert_into_leaf") (callValues node key length pointer size)=some (body,callee,.one) ∧
      callee.lookup (ofString "node")=some (.val (.word node)) ∧
      callee.lookup (ofString "rk")=some (.val (.word key)) ∧
      callee.lookup (ofString "rl")=some (.val (.word length)) ∧
      callee.lookup (ofString "vptr")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "vlen")=some (.val (.word size)) := by
  let rawLocals : MlS → Option (ValueHOL 64):=fun name=>if name=ofString "vlen" then some (.val (.word size)) else if name=ofString "vptr" then some (.val (.word pointer)) else if name=ofString "rl" then some (.val (.word length)) else if name=ofString "rk" then some (.val (.word key)) else if name=ofString "node" then some (.val (.word node)) else none
  have distinct : (formals.map Prod.fst).Nodup:=by decide
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(callValues node key length pointer size).length ∧
      ((formals.zip (callValues node key length pointer size)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true:=
    ⟨distinct,rfl,by simp [formals,callValues,shapeOfHOLExact,shapeEqHOL]⟩
  have raw : lookupCodeHOLExact source.code.lookup (ofString "_insert_into_leaf") (callValues node key length pointer size)=some (body,rawLocals,.one):=by
    simp only [lookupCodeHOLExact,known,if_pos valid]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup source.code.lookup _ _ _ _ _ raw
  refine ⟨callee,called,?_⟩
  repeat apply And.intro
  all_goals rw [locals]
  all_goals simp [rawLocals,ofString]

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.environment

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def callValues (node key length pointer size prefixLength : BitVec 64) : List (ValueHOL 64):=[.val (.word node),.val (.word key),.val (.word length),.val (.word pointer),.val (.word size),.val (.word prefixLength)]

/-- Actual fixed original helper ABI, before assuming any callee result. -/
theorem environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node key length pointer size prefixLength : BitVec 64)
    (known : source.code.lookup (ofString "_split_extension")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite source.code.lookup (ofString "_split_extension") (callValues node key length pointer size prefixLength)=some (body,callee,.one) ∧
      callee.lookup (ofString "node")=some (.val (.word node)) ∧
      callee.lookup (ofString "rk")=some (.val (.word key)) ∧
      callee.lookup (ofString "rl")=some (.val (.word length)) ∧
      callee.lookup (ofString "vptr")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "vlen")=some (.val (.word size)) ∧
      callee.lookup (ofString "pl")=some (.val (.word prefixLength)) := by
  let rawLocals : MlS → Option (ValueHOL 64):=fun name=>if name=ofString "pl" then some (.val (.word prefixLength)) else if name=ofString "vlen" then some (.val (.word size)) else if name=ofString "vptr" then some (.val (.word pointer)) else if name=ofString "rl" then some (.val (.word length)) else if name=ofString "rk" then some (.val (.word key)) else if name=ofString "node" then some (.val (.word node)) else none
  have distinct : (formals.map Prod.fst).Nodup:=by decide
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(callValues node key length pointer size prefixLength).length ∧
      ((formals.zip (callValues node key length pointer size prefixLength)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true:=
    ⟨distinct,rfl,by simp [formals,callValues,shapeOfHOLExact,shapeEqHOL]⟩
  have raw : lookupCodeHOLExact source.code.lookup (ofString "_split_extension") (callValues node key length pointer size prefixLength)=some (body,rawLocals,.one):=by
    simp only [lookupCodeHOLExact,known,if_pos valid]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup source.code.lookup _ _ _ _ _ raw
  refine ⟨callee,called,?_⟩
  repeat apply And.intro
  all_goals rw [locals]
  all_goals simp [rawLocals,ofString]

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.environment

