import InitECandidate.Solver.Input.CurrentTable.Get.Setup
import InitECandidate.Solver.Input.MemeqCode
import InitECandidate.Solver.MutableTable.MemeqAnyFast32
import InitECandidate.Solver.MutableTable.MemeqByteRuntime.Environment
import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.NoFallthrough

namespace InitECandidate.Solver.Input.CurrentTable.Get
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch
open Flapjack.Compiler.Encoders.Asm

theorem after_compare_cost (code) : ClockCost.Bound code afterCompare 0 := by
  unfold afterCompare compareGuard absent
  exact ClockCost.sequence code _ _ 0 0
    (ClockCost.conditional code _ _ _ 0 0 (ClockCost.returned code _) (ClockCost.skip code)) (ClockCost.returned code _)

theorem compare_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table pointer leaf : BitVec 64)
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word leaf)))
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState (prepared source table) compareCall).2.clock≤5 := by
  let entry := prepared source table
  obtain ⟨callee,called,aCell,bCell,nCell⟩ := MutableTable.MemeqByteRuntime.environment entry.code.lookup (slot (New.keysPointer table) leaf 32) pointer 32
    (MutableTable.MemeqAny.original_code entry.code installed)
  exact ClockCost.scoped_current entry (ofString "eq") .one (ofString "memeq") compareArguments _ Memeq32.body afterCompare callee .one 4 0
    (compare_arguments source table pointer leaf keyCell leafCell) called
    (MutableTable.MemeqAny.tight_body_cost (callEntryStateHOLFinite entry callee) nCell) (after_compare_cost entry.code)

theorem after_empty_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer leaf : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word leaf)))
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterEmpty).2.clock≤5 := by
  rw [setup image tableCell]
  exact compare_cost source table pointer leaf keyCell leafCell installed

theorem after_leaf_empty (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word 0#64))) :
    evaluateHOLFiniteState source afterLeaf=evaluateHOLFiniteState source absent := by
  have read : eval source (.cmp .equal (localVar "leaf") (.const 0#64))=some (.val (.word 1#64)) := by
    simp [eval,evalHOLExact,localVar,leafCell,wordCmpHOL]
  simp only [eval] at read
  rw [afterLeaf,evaluateHOLFiniteState_seq_line780,emptyGuard,evaluateHOLFiniteState_ite,read]
  simp only [if_neg (show (1#64 : BitVec 64)≠0 from by decide)]
  generalize actual : evaluateHOLFiniteState source absent=output
  obtain ⟨outcome,post⟩ := output
  cases outcome with
  | none =>
    have stopped : NoFallthrough absent := NoFallthrough.returned _
    have no := stopped source
    rw [actual] at no
    exact (no rfl).elim
  | some result => rfl

theorem after_leaf_nonempty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (leaf : BitVec 64)
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word leaf))) (nonzero : leaf≠0#64) :
    evaluateHOLFiniteState source afterLeaf=evaluateHOLFiniteState source afterEmpty := by
  have read : eval source (.cmp .equal (localVar "leaf") (.const 0#64))=some (.val (.word 0#64)) := by
    simp [eval,evalHOLExact,localVar,leafCell,wordCmpHOL,nonzero]
  simp only [eval] at read
  rw [afterLeaf,evaluateHOLFiniteState_seq_line780,emptyGuard,evaluateHOLFiniteState_ite,read]
  simp [evaluateHOLFiniteState_skip]

theorem after_leaf_cost {source : PanSemStateFiniteExact 64 Guest.HostMemory} {table cap root pointer leaf : BitVec 64}
    {next count : Nat} {valid : BitVec 64 → Prop} {bits : BitVec 64 → Nat} {left right : BitVec 64 → BitVec 64}
    {keys : BitVec 64 → KeyBits.Key} {ValueOf : BitVec 64 → Prop}
    (image : Image source table cap root next count valid bits left right keys ValueOf)
    (tableCell : source.locals.lookup (ofString "t")=some (.val (.word table)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word pointer)))
    (leafCell : source.locals.lookup (ofString "leaf")=some (.val (.word leaf)))
    (installed : OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterLeaf).2.clock≤5 := by
  by_cases zero : leaf=0#64
  · rw [zero] at leafCell
    rw [after_leaf_empty source leafCell]
    exact Nat.le_trans (ClockCost.returned source.code _ source rfl) (by omega)
  · rw [after_leaf_nonempty source leaf leafCell zero]
    exact after_empty_cost image tableCell keyCell leafCell installed

end InitECandidate.Solver.Input.CurrentTable.Get

#print axioms InitECandidate.Solver.Input.CurrentTable.Get.after_leaf_cost
