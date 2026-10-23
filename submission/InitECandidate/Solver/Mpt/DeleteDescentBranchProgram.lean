import InitECandidate.Solver.Mpt.DeleteDescentPathReads

namespace InitECandidate.Solver.Mpt.DeleteBody
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def branchIndex : ExpHOL 64:=.loadByte keySuffix
def branchValueArguments : List (ExpHOL 64):=[localVar "node"]
def branchCollapse : ProgHOL 64:=.call (some (some (.local,ofString "res"),none)) (ofString "_collapse_branch") branchValueArguments
def branchClear : ProgHOL 64:=.seq (.store (.op .add [localVar "node",.const 160#64]) (.const 0#64))
  (.seq (.store (.op .add [localVar "node",.const 168#64]) (.const 0#64)) branchCollapse)

theorem branch_index_shape : branchIndexScope=.dec (ofString "idx") .one branchIndex branchFrameScope := branch_shapes.2.1

theorem branch_value_shape : branchValue=.ite (.cmp .equal (field "node" 168#64) (.const 0#64))
    (.assign .local (ofString "res") (localVar "node")) branchClear := branch_shapes.2.2.2

theorem branch_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) :
    evaluateHOLFiniteState source branchBlock=if model.level=length then evaluateHOLFiniteState source branchValue else evaluateHOLFiniteState source branchIndexScope := by
  rw [branch_shapes.1,evaluateHOLFiniteState_ite]
  by_cases done : model.level=length <;>
    simp [evalHOLExact,toExact,localVar,model.levelCell,model.lengthCell,done,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem branch_value_dispatch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (key length : BitVec 64)
    (limit nodeLower pathLower : Nat) (property : BitVec 64→BitVec 64→Prop)
    (model : DescentModel source key length limit nodeLower pathLower property) (active : model.node≠0#64)
    (tag : wordAt source.memory model.node=3#64) :
    evaluateHOLFiniteState source branchValue=if wordAt source.memory (model.node+168#64)=0#64
      then evaluateHOLFiniteState source (.assign .local (ofString "res") (localVar "node")) else evaluateHOLFiniteState source branchClear := by
  let view:=model.pending.values.branch model.node model.nodeMember active (by rw [tag]; decide) (by rw [tag]; decide) (by rw [tag]; decide)
  have sizeEq : wordAt source.memory (model.node+168#64)=view.length:=by simp [wordAt,view.lengthStored,MemoryBytes.wordBits]
  have read : eval source (field "node" 168#64)=some (.val (.word (wordAt source.memory (model.node+168#64)))):=by
    rw [sizeEq]
    exact DeleteExtension.field_read source "node" model.node 168#64 view.length model.nodeCell view.lengthMapped view.lengthStored
  simp only [eval] at read
  rw [branch_value_shape,evaluateHOLFiniteState_ite,evalHOLExact,read]
  by_cases empty : wordAt source.memory (model.node+168#64)=0#64 <;>
    simp [empty,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evalHOLExact]

end InitECandidate.Solver.Mpt.DeleteBody

#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_index_shape
#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_value_shape
#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_dispatch
#print axioms InitECandidate.Solver.Mpt.DeleteBody.branch_value_dispatch
