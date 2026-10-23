import InitECandidate.Solver.Mpt.DeleteFrameReads

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def extensionArguments : List (ExpHOL 64):=[localVar "fnode",field "top" 24#64,field "top" 32#64,localVar "res"]
def branchArguments : List (ExpHOL 64):=[localVar "fnode"]
def finishExtension : ProgHOL 64:=.call (some (some (.local,ofString "res"),none)) (ofString "_delete_ext_finish") extensionArguments
def finishBranch : ProgHOL 64:=.call (some (some (.local,ofString "res"),none)) (ofString "_collapse_branch") branchArguments
def replaceChild : ProgHOL 64:=.store (childAddress "fnode" (field "top" 32#64)) (localVar "res")
def branchUnwind : ProgHOL 64:=.seq replaceChild finishBranch

theorem choice_shape : unwindChoice=.ite (.cmp .equal (field "top" 16#64) (.const 2#64)) finishExtension branchUnwind :=
  unwind_shapes.2.2.2.1

theorem unwind_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : DeleteFrame.Saved)
    (view : saved.View source) (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer))) :
    evaluateHOLFiniteState source unwindChoice=evaluateHOLFiniteState source
      (match saved.kind with | .extension=>finishExtension | .branch=>branchUnwind) := by
  have read:=view.tag_read source saved domain topCell
  simp only [eval] at read
  rw [choice_shape,evaluateHOLFiniteState_ite,evalHOLExact,read]
  cases kindEq : saved.kind <;> simp [kindEq,DeleteFrame.Kind.tag,evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem extension_arguments (source : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : DeleteFrame.Saved) (result : BitVec 64)
    (view : saved.View source) (kindEq : saved.kind=.extension) (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer)))
    (nodeCell : source.locals.lookup (ofString "fnode")=some (.val (.word saved.node)))
    (resultCell : source.locals.lookup (ofString "res")=some (.val (.word result))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) extensionArguments=
      some [.val (.word saved.node),.val (.word (saved.words "seg")),.val (.word (saved.words "sl")),.val (.word result)] := by
  have segmentIn : (⟨24,.saved "seg" (saved.words "seg")⟩ : LocalFields.Field)∈saved.kind.fields saved.words:=by simp [kindEq,DeleteFrame.Kind.fields]
  have lengthIn : (⟨32,.saved "sl" (saved.words "sl")⟩ : LocalFields.Field)∈saved.kind.fields saved.words:=by simp [kindEq,DeleteFrame.Kind.fields]
  have segmentRead:=view.field_read source saved domain topCell _ segmentIn
  have lengthRead:=view.field_read source saved domain topCell _ lengthIn
  simp only [eval,LocalFields.Operand.word] at segmentRead lengthRead
  simp only [extensionArguments,evalListHOLFinite,evalListHOLExact,segmentRead,lengthRead]
  simp [localVar,evalHOLExact,toExact,nodeCell,resultCell]

theorem branch_index_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (saved : DeleteFrame.Saved)
    (view : saved.View source) (kindEq : saved.kind=.branch) (domain : source.memaddrs=InitE.ordinaryDomain)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word saved.pointer))) :
    eval source (field "top" 32#64)=some (.val (.word (saved.words "idx"))) := by
  have indexIn : (⟨32,.saved "idx" (saved.words "idx")⟩ : LocalFields.Field)∈saved.kind.fields saved.words:=by simp [kindEq,DeleteFrame.Kind.fields]
  simpa only [LocalFields.Operand.word] using view.field_read source saved domain topCell _ indexIn

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.choice_shape
#print axioms InitECandidate.Solver.Mpt.DeleteBody.unwind_dispatch
#print axioms InitECandidate.Solver.Mpt.DeleteBody.extension_arguments
#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_index_read
