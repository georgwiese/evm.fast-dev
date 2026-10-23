import InitECandidate.Solver.Mpt.SetProgram
import InitECandidate.Solver.WitnessRadix.CodeEnvironment

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def values (m key length pointer size : BitVec 64) : List (ValueHOL 64):=
  [.val (.word m),.val (.word key),.val (.word length),.val (.word pointer),.val (.word size)]

def rawLocals (m key length pointer size : BitVec 64) (name : MlS) : Option (ValueHOL 64):=
  if name=ofString "vlen" then some (.val (.word size)) else if name=ofString "vptr" then some (.val (.word pointer))
  else if name=ofString "klen" then some (.val (.word length)) else if name=ofString "key" then some (.val (.word key))
  else if name=ofString "m" then some (.val (.word m)) else none

/-- The actual five scalar arguments determine the original setter's
callee locals, independently of whether its execution succeeds. -/
theorem environment (table : MlS→Option (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL))
    (m key length pointer size : BitVec 64) (known : table (ofString "mpt_set")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite table (ofString "mpt_set") (values m key length pointer size)=some (body,callee,.one) ∧
      callee.lookup (ofString "m")=some (.val (.word m)) ∧ callee.lookup (ofString "key")=some (.val (.word key)) ∧
      callee.lookup (ofString "klen")=some (.val (.word length)) ∧ callee.lookup (ofString "vptr")=some (.val (.word pointer)) ∧
      callee.lookup (ofString "vlen")=some (.val (.word size)) := by
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values m key length pointer size).length ∧
      ((formals.zip (values m key length pointer size)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true:=by
    refine ⟨by decide,rfl,?_⟩
    simp [formals,values,shapeOfHOLExact,shapeEqHOL]
  have raw : lookupCodeHOLExact table (ofString "mpt_set") (values m key length pointer size)=
      some (body,rawLocals m key length pointer size,.one):=by
    simp only [lookupCodeHOLExact,known,valid]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup table _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_,?_,?_,?_⟩ <;> rw [locals] <;> simp [rawLocals,ofString]

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.environment
