import InitECandidate.Solver.Input.CurrentTable.Set.Program
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def emptyLeafCall : ProgHOL 64 := match emptyGuard with | .ite _ yes _ => yes | _ => .skip
def emptyFinish : ProgHOL 64 := match emptyLeafCall with | .decCall _ _ _ _ rest => rest | _ => .skip
def updateBody : ProgHOL 64 := match updateGuard with | .ite _ yes _ => yes | _ => .skip

def compareArguments : List (ExpHOL 64) :=
  [.op .add [localVar "keys",.panop .mul [localVar "leaf",localVar "stride"]],localVar "key",localVar "klen"]
def leafArguments : List (ExpHOL 64) := [localVar "t",localVar "key",localVar "value"]

set_option maxRecDepth 100000 in
theorem guard_shapes :
    emptyGuard = .ite (.cmp .equal (localVar "leaf") (.const 0#64)) emptyLeafCall .skip ∧
    emptyLeafCall = .decCall (ofString "nl") .one (ofString "htab_new_leaf") leafArguments emptyFinish ∧
    emptyFinish = .seq (.store (.op .add [localVar "t",.const 56#64]) (localVar "nl")) (.return (.const 0#64)) ∧
    updateGuard = .ite (.cmp .notEqual (localVar "eq") (.const 0#64)) updateBody .skip ∧
    updateBody = .seq (.store (.op .add [.load .one (.op .add [localVar "t",.const 40#64]),
      .panop .mul [localVar "leaf",.const 32#64],.const 8#64]) (localVar "value")) (.return (.const 0#64)) ∧
    compareCall = .decCall (ofString "eq") .one (ofString "memeq") compareArguments afterCompare := by
  simp only [emptyGuard,emptyLeafCall,emptyFinish,updateGuard,updateBody,compareCall,compareArguments,leafArguments,
    afterCompare,afterKeys,afterLeaf,afterStride,afterLength,body,Guest.Software.guestFn_htab_set,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
  trivial

theorem empty_leaf_no_fallthrough : NoFallthrough emptyLeafCall := by
  rw [guard_shapes.2.1]
  apply NoFallthrough.scoped
  rw [guard_shapes.2.2.1]
  exact NoFallthrough.sequence _ _ (NoFallthrough.returned _)

theorem after_keys_empty (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (leafCell : source.locals.lookup (ofString "leaf") = some (.val (.word 0#64))) :
    evaluateHOLFiniteState source afterKeys = evaluateHOLFiniteState source emptyLeafCall := by
  have read : eval source (.cmp .equal (localVar "leaf") (.const 0#64)) = some (.val (.word 1#64)) := by
    simp [eval,evalHOLExact,localVar,leafCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  simp only [eval] at read
  rw [entry_shapes.2.2.2.2.1,evaluateHOLFiniteState_seq_line780,guard_shapes.1,evaluateHOLFiniteState_ite,read]
  simp only [if_neg (show (1#64 : BitVec 64) ≠ 0 from by decide)]
  generalize run : evaluateHOLFiniteState source emptyLeafCall = output
  obtain ⟨outcome,post⟩ := output
  cases outcome with
  | none =>
    have stopped := empty_leaf_no_fallthrough source
    rw [run] at stopped
    exact (stopped rfl).elim
  | some result => rfl


end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.guard_shapes
