import InitECandidate.Solver.Mpt.SetEmptyDispatch
import InitECandidate.Solver.Mpt.DeleteNodeAssigned

namespace InitECandidate.Solver.Mpt.SetTrie
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def deleteArguments : List (ExpHOL 64):=[localVar "root",.rfield 0 (localVar "nk"),.rfield 1 (localVar "nk"),.const 0#64]

theorem deletion_shape : deletionCall=.call (some (some (.local,ofString "root"),none)) (ofString "_mpt_delete_node") deleteArguments := by
  simp only [deletionCall,mutationChoice,afterRoot,afterKey,body,deleteArguments,
    Guest.guestFn_mpt_set,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,Option.map_some,localVar]

theorem mutation_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer size : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size))) :
    evaluateHOLFiniteState source mutationChoice=if pointer=0#64 ∨ size=0#64 then evaluateHOLFiniteState source deletionCall else evaluateHOLFiniteState source insertCall := by
  by_cases absent : pointer=0#64 ∨ size=0#64
  · have observed : eval source deletionTest=some (.val (.word 1#64)):=by
      rcases absent with zero|zero
      all_goals simp [eval,deletionTest,localVar,evalHOLExact,evalListHOLExact,toExact,pointerCell,sizeCell,zero,
        valueIsWord,valueWord,wordOpHOL,wordOp,Flapjack.Compiler.Encoders.Asm.wordCmpHOL] <;> split <;> decide
    rw [if_pos absent,mutation_shapes.2.2.1,evaluateHOLFiniteState_ite]
    simp only [eval] at observed
    rw [observed]
    rfl
  · rw [if_neg absent]
    exact insert_selected source pointer size pointerCell sizeCell (fun zero=>absent (Or.inl zero)) (fun zero=>absent (Or.inr zero))

theorem delete_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root key length : BitVec 64)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root)))
    (nkCell : source.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)])) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) deleteArguments=some (DeleteNode.values root key length 0#64) := by
  simp [deleteArguments,DeleteNode.values,evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,rootCell,nkCell]

theorem insert_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (root key length pointer size : BitVec 64)
    (rootCell : source.locals.lookup (ofString "root")=some (.val (.word root)))
    (nkCell : source.locals.lookup (ofString "nk")=some (.rStruct [.val (.word key),.val (.word length)]))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) insertArguments=some (Insert.values root key length 0#64 pointer size) := by
  simp [insertArguments,Insert.values,evalListHOLFinite,evalListHOLExact,localVar,evalHOLExact,toExact,rootCell,nkCell,pointerCell,sizeCell]

end InitECandidate.Solver.Mpt.SetTrie

#print axioms InitECandidate.Solver.Mpt.SetTrie.deletion_shape
#print axioms InitECandidate.Solver.Mpt.SetTrie.mutation_dispatch
#print axioms InitECandidate.Solver.Mpt.SetTrie.delete_arguments
#print axioms InitECandidate.Solver.Mpt.SetTrie.insert_arguments
