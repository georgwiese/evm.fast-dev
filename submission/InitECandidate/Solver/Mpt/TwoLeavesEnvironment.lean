import InitECandidate.Solver.Mpt.TwoLeavesInputs
import InitECandidate.Solver.Input.WordQuadEnvironment

namespace InitECandidate.Solver.Mpt.TwoLeaves
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def values (key1 length1 pointer1 size1 key2 length2 pointer2 size2 : BitVec 64) : List (ValueHOL 64):=
  [.val (.word key1),.val (.word length1),.val (.word pointer1),.val (.word size1),
    .val (.word key2),.val (.word length2),.val (.word pointer2),.val (.word size2)]

/-- The actual fixed eight-word ABI supplies both sides' current locals. -/
theorem environment (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (key1 length1 pointer1 size1 key2 length2 pointer2 size2 : BitVec 64)
    (known : source.code.lookup (ofString "_create_branch_from_two_leaves")=some (formals,body,.one)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite source.code.lookup (ofString "_create_branch_from_two_leaves") (values key1 length1 pointer1 size1 key2 length2 pointer2 size2)=some (body,callee,.one) ∧
      SideInputs (callEntryStateHOLFinite source callee) false key1 length1 pointer1 size1 ∧
      SideInputs (callEntryStateHOLFinite source callee) true key2 length2 pointer2 size2 := by
  let rawLocals : MlS → Option (ValueHOL 64):=fun name=>
    if name=ofString "vl2" then some (.val (.word size2)) else if name=ofString "v2" then some (.val (.word pointer2))
    else if name=ofString "l2" then some (.val (.word length2)) else if name=ofString "k2" then some (.val (.word key2))
    else if name=ofString "vl1" then some (.val (.word size1)) else if name=ofString "v1" then some (.val (.word pointer1))
    else if name=ofString "l1" then some (.val (.word length1)) else if name=ofString "k1" then some (.val (.word key1)) else none
  have distinct : (formals.map Prod.fst).Nodup:=by decide
  have valid : (formals.map Prod.fst).Nodup ∧ formals.length=(values key1 length1 pointer1 size1 key2 length2 pointer2 size2).length ∧
      ((formals.zip (values key1 length1 pointer1 size1 key2 length2 pointer2 size2)).all (fun pair=>shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)))=true:=
    ⟨distinct,rfl,by simp [formals,values,shapeOfHOLExact,shapeEqHOL]⟩
  have raw : lookupCodeHOLExact source.code.lookup (ofString "_create_branch_from_two_leaves") (values key1 length1 pointer1 size1 key2 length2 pointer2 size2)=some (body,rawLocals,.one):=by
    simp only [lookupCodeHOLExact,known,if_pos valid]
    rfl
  obtain ⟨callee,called,locals⟩:=CodeEnvironment.finite_lookup source.code.lookup _ _ _ _ _ raw
  refine ⟨callee,called,?_,?_⟩
  all_goals constructor
  all_goals change callee.lookup _=some _
  all_goals rw [locals]
  all_goals simp [rawLocals,label,ofString]

end InitECandidate.Solver.Mpt.TwoLeaves

#print axioms InitECandidate.Solver.Mpt.TwoLeaves.environment
