import InitECandidate.Solver.Input.StoreMemoryAway
import InitECandidate.Solver.Input.MemoryNormal

namespace InitECandidate.Solver.Input.MemoryAt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def literalStores (name : String) : List (Nat×BitVec 64)→ProgHOL 64
  | []=>.return (.const 0#64)
  | (offset,value)::rest=>.seq (.store (.op .add [localVar name,.const (BitVec.ofNat 64 offset)]) (.const value)) (literalStores name rest)

/-- A real returning literal-store pipeline preserves every other word.
Mapping and individual store success follow from that observed return. -/
theorem literal_stores_returned {F : Type} (fields : List (Nat×BitVec 64)) (source post : PanSemStateFiniteExact 64 F)
    (name : String) (pointer query : BitVec 64)
    (cell : source.locals.lookup (ofString name)=some (.val (.word pointer)))
    (away : ∀ entry∈fields,query≠pointer+BitVec.ofNat 64 entry.1)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (literalStores name fields)=(some (.returned value),post)) : post.memory query=source.memory query := by
  induction fields generalizing source post with
  | nil=>
    have actual : evaluateHOLFiniteState source (.return (.const 0#64))=(some (.returned (.val (.word 0#64))),emptyLocalsHOLFinite source) := by simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL]
    change evaluateHOLFiniteState source (.return (.const 0#64))=(some (.returned value),post) at run
    rw [actual] at run
    have endpoint : post=emptyLocalsHOLFinite source := (congrArg Prod.snd run).symm
    rw [endpoint]
    rfl
  | cons entry rest ih=>
    obtain ⟨offset,word⟩ := entry
    have safe : LocalPrefix (ofString name) (.store (.op .add [localVar name,.const (BitVec.ofNat 64 offset)]) (.const word)) := .store _ _
    change evaluateHOLFiniteState source (.seq _ (literalStores name rest))=(some (.returned value),post) at run
    obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 run
    have read : eval source (.op .add [localVar name,.const (BitVec.ofNat 64 offset)])=some (.val (.word (pointer+BitVec.ofNat 64 offset))) := by
      simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,cell,valueIsWord,valueWord,wordOpHOL,wordOp]
    have frame := Input.word_store_normal source middle _ (.const word) (pointer+BitVec.ofNat 64 offset) word read rfl normal
    have nextCell : middle.locals.lookup (ofString name)=some (.val (.word pointer)) := by rw [frame.2]; exact cell
    have tail := ih middle post nextCell (by intro next member; exact away next (by simp [member])) remaining
    have first : middle.memory query=source.memory query := by
      rw [frame.2]
      exact if_neg (away (offset,word) (by simp))
    exact tail.trans first

end InitECandidate.Solver.Input.MemoryAt

#print axioms InitECandidate.Solver.Input.MemoryAt.literal_stores_returned
