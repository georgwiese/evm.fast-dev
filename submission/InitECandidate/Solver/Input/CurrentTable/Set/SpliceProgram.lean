import InitECandidate.Solver.Input.CurrentTable.Set.Guards
import InitECandidate.Solver.Input.CurrentTable.KeyRead
import InitECandidate.Solver.Input.StraightBody

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def newInternalCall : ProgHOL 64 := match newLeafCall with | .decCall _ _ _ _ rest => rest | _ => .skip
def splice : ProgHOL 64 := match newInternalCall with | .decCall _ _ _ _ rest => rest | _ => .skip
def afterRefresh : ProgHOL 64 := match splice with | .seq _ rest => rest | _ => .skip
def afterInternalParent : ProgHOL 64 := match afterRefresh with | .seq _ rest => rest | _ => .skip
def afterLeafParent : ProgHOL 64 := match afterInternalParent with | .seq _ rest => rest | _ => .skip
def afterOldParent : ProgHOL 64 := match afterLeafParent with | .seq _ rest => rest | _ => .skip
def splitChildren : ProgHOL 64 := match afterOldParent with | .seq first _ => first | _ => .skip
def afterSplit : ProgHOL 64 := match afterOldParent with | .seq _ rest => rest | _ => .skip
def attach : ProgHOL 64 := match afterSplit with | .seq first _ => first | _ => .skip
def nodeFor (name : String) (offset : Nat) : ExpHOL 64 :=
  .op .add [localVar "nodes",.panop .mul [localVar name,.const 32#64],.const (BitVec.ofNat 64 offset)]
def leftFresh : ProgHOL 64 := .seq (.store (nodeFor "ni" 8) (localVar "nl")) (.store (nodeFor "ni" 16) (localVar "n"))
def rightFresh : ProgHOL 64 := .seq (.store (nodeFor "ni" 8) (localVar "n")) (.store (nodeFor "ni" 16) (localVar "nl"))

set_option maxRecDepth 100000 in
theorem splice_shapes :
    newLeafCall = .decCall (ofString "nl") .one (ofString "htab_new_leaf") leafArguments newInternalCall ∧
    newInternalCall = .decCall (ofString "ni") .one (ofString "htab_new_internal") [localVar "t",localVar "d"] splice ∧
    splice = .seq (.assign .local (ofString "nodes") (.load .one (.op .add [localVar "t",.const 40#64]))) afterRefresh ∧
    afterRefresh = .seq (.store (nodeFor "ni" 0) (localVar "p")) afterInternalParent ∧
    afterInternalParent = .seq (.store (nodeFor "nl" 0) (localVar "ni")) afterLeafParent ∧
    afterLeafParent = .seq (.store (nodeFor "n" 0) (localVar "ni")) afterOldParent ∧
    afterOldParent = .seq splitChildren afterSplit ∧
    splitChildren = .ite (.cmp .equal (KeyRead.mask "key" "d") (.const 0#64)) leftFresh rightFresh ∧
    afterSplit = .seq attach (.return (.const 0#64)) ∧
    attach = .ite (.cmp .equal (localVar "p") (.const 0#64))
      (.store (.op .add [localVar "t",.const 56#64]) (localVar "ni"))
      (.ite (.cmp .equal (.load .one (nodeFor "p" 8)) (localVar "n"))
        (.store (nodeFor "p" 8) (localVar "ni")) (.store (nodeFor "p" 16) (localVar "ni"))) := by
  simp only [newLeafCall,newInternalCall,splice,afterRefresh,afterInternalParent,afterLeafParent,afterOldParent,splitChildren,
    afterSplit,attach,nodeFor,leftFresh,rightFresh,leafArguments,KeyRead.mask,KeyRead.loaded,KeyRead.byteIndex,KeyRead.amount,KeyRead.digitIndex,
    afterNode,afterParent,afterNodes,afterDifference,differenceCall,afterCompare,compareCall,afterKeys,afterLeaf,afterStride,afterLength,body,
    Guest.Software.guestFn_htab_set,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem splice_supported : StraightBody.accepts splice = true := by
  obtain ⟨_,_,refresh,internalParent,leafParent,oldParent,children,split,finish,link⟩ := splice_shapes
  simp only [refresh,internalParent,leafParent,oldParent,children,split,finish,link,leftFresh,rightFresh,StraightBody.accepts]
  rfl

/-- Every original post-constructor rewiring outcome spends zero source
ticks, including failed reads/stores and either parent/root branch. -/
theorem splice_quiet (code) : QuietClock.Preserves code splice :=
  (StraightBody.effects (ofString "heap_ptr") code splice splice_supported).1

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_shapes
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.splice_quiet
