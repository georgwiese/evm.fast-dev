import InitECandidate.Solver.Mpt.WitnessCoreReturnProgram
import InitECandidate.Solver.Mpt.WitnessRecordView
import InitECandidate.Solver.Input.ScalarScopeTrace

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual br/i declarations load the current physical node/index
and expose the genuine child-processing execution. Both real lexical
restorations are retained for arbitrary normal or stopped outcomes. -/
theorem return_branch_node_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node : BitVec 64) (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source returnBranchNode=(result,post)) :
    ∃ inner,
      let branchReady:=QueryBranch.bind source "br" node
      let ready:=QueryBranch.bind branchReady "i" (BitVec.ofNat 64 index.val)
      evaluateHOLFiniteState ready branchChildren=(result,inner) ∧ post=restore source "br" (restore branchReady "i" inner) := by
  have mapped16 : source.memaddrs (record+16#64):=by simpa only [byteAddress] using view.mapped source record db data 16 (by decide) (by decide)
  have mapped32 : source.memaddrs (record+32#64):=by simpa only [byteAddress] using view.mapped source record db data 32 (by decide) (by decide)
  have nodeCell : source.memory (record+16#64)=.word node:=view.cells (16,node) (by simp [WitnessRecord.Description.cells,payload])
  have indexCell : source.memory (record+32#64)=.word (BitVec.ofNat 64 index.val):=view.cells (32,BitVec.ofNat 64 index.val) (by simp [WitnessRecord.Description.cells,payload])
  have nodeRead : eval source (readAt "top" 16#64)=some (.val (.word node)):=by
    simp [eval,readAt,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped16,nodeCell]
  rw [return_branch_node_shape] at run
  obtain ⟨branchPost,branchRun,branchEndpoint⟩:=Input.ScalarScope.declare_trace source post "br" (readAt "top" 16#64) node branchIndexRead result nodeRead run
  let branchReady:=QueryBranch.bind source "br" node
  have branchTop : branchReady.locals.lookup (ofString "top")=some (.val (.word record)):=
    (bind_lookup_other source "br" "top" node (by decide)).trans topCell
  have indexRead : eval branchReady (readAt "top" 32#64)=some (.val (.word (BitVec.ofNat 64 index.val))):=by
    simp [eval,readAt,evalHOLExact,evalListHOLExact,localVar,toExact,branchTop,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped32,indexCell]
    exact ⟨mapped32,indexCell⟩
  rw [branch_index_read_shape] at branchRun
  obtain ⟨inner,continued,indexEndpoint⟩:=Input.ScalarScope.declare_trace branchReady branchPost "i" (readAt "top" 32#64)
    (BitVec.ofNat 64 index.val) branchChildren result indexRead branchRun
  exact ⟨inner,continued,by rw [branchEndpoint,indexEndpoint]⟩

theorem branch_scope_entry_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record node child : BitVec 64) (index : Fin 16)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child))) :
    let ready:=QueryBranch.bind (QueryBranch.bind source "br" node) "i" (BitVec.ofNat 64 index.val)
    ready.locals.lookup (ofString "top")=some (.val (.word record)) ∧
      ready.locals.lookup (ofString "br")=some (.val (.word node)) ∧
      ready.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val))) ∧
      ready.locals.lookup (ofString "result")=some (.val (.word child)) := by
  exact ⟨(bind_lookup_other _ "i" "top" _ (by decide)).trans ((bind_lookup_other source "br" "top" node (by decide)).trans topCell),
    (bind_lookup_other _ "i" "br" _ (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _,
    (bind_lookup_other _ "i" "result" _ (by decide)).trans ((bind_lookup_other source "br" "result" node (by decide)).trans resultCell)⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.return_branch_node_trace
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_scope_entry_fields
