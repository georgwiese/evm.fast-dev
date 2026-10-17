import InitECandidate.Solver.WitnessRadix.WordWrites
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.FieldStores
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A specification of scalar initialization stores. Expected source words are
proof data; local/copy expressions use the actual runtime bindings and memory. -/
inductive Value where
  | literal (word : BitVec 64)
  | saved (name : String) (word : BitVec 64)
  | copied (offset : Nat) (word : BitVec 64)

def Value.word : Value → BitVec 64
  | .literal word | .saved _ word | .copied _ word => word

def Value.expression (messageName : String) : Value → ExpHOL 64
  | .literal word => .const word
  | .saved name _ => localVar name
  | .copied offset _ => .load .one (addConst (localVar messageName) (BitVec.ofNat 64 offset))

def Value.Ready {F : Type} (source : PanSemStateFiniteExact 64 F) (messageName : String) (message : BitVec 64) : Value → Prop
  | .literal _ => True
  | .saved name word => source.locals.lookup (ofString name) = some (.val (.word word))
  | .copied offset word =>
      source.locals.lookup (ofString messageName) = some (.val (.word message)) ∧
      source.memaddrs (message + BitVec.ofNat 64 offset) ∧
      source.memory (message + BitVec.ofNat 64 offset) = .word word

def Value.Avoid (message address : BitVec 64) : Value → Prop
  | .copied offset _ => message + BitVec.ofNat 64 offset ≠ address
  | _ => True

structure Field where
  offset : Nat
  value : Value

def address (baseName : String) (offset : Nat) : ExpHOL 64 := addConst (localVar baseName) (BitVec.ofNat 64 offset)
def program (baseName messageName : String) : List Field → ProgHOL 64 → ProgHOL 64
  | [], continuation => continuation
  | field :: rest, continuation =>
      .seq (.store (address baseName field.offset) (field.value.expression messageName))
        (program baseName messageName rest continuation)
def writes (base : BitVec 64) (fields : List Field) : List (BitVec 64 × BitVec 64) :=
  fields.map (fun field => (base + BitVec.ofNat 64 field.offset, field.value.word))

theorem Value.read {F : Type} (source : PanSemStateFiniteExact 64 F) (messageName : String)
    (message : BitVec 64) (value : Value) (ready : value.Ready source messageName message) :
    eval source (value.expression messageName) = some (.val (.word value.word)) := by
  cases value with
  | literal word => rfl
  | saved name word => simpa [Value.Ready, eval, Value.expression, Value.word, localVar, evalHOLExact, toExact] using ready
  | copied offset word =>
    obtain ⟨stored, mapped, cell⟩ := ready
    simp [eval, Value.expression, Value.word, addConst, localVar, evalHOLExact, evalListHOLExact,
      toExact, stored, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact,
      isWfShapeExactHOL, mapped, cell]

theorem Value.ready_store {F : Type} (source : PanSemStateFiniteExact 64 F) (messageName : String)
    (message address word : BitVec 64) (value : Value)
    (ready : value.Ready source messageName message) (away : value.Avoid message address) :
    value.Ready {source with memory := WitnessRadix.StoreWord.put source.memory address word} messageName message := by
  cases value with
  | literal value => trivial
  | saved name value => exact ready
  | copied offset value =>
    exact ⟨ready.1, ready.2.1, by simpa only [WitnessRadix.StoreWord.put, if_neg away] using ready.2.2⟩

/-- Real initialization stores with exact memory effects. Read sources are
protected from every destination, so each actual later load is justified by
the initial snapshot. Arbitrary continuations and all their outcomes remain. -/
theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F) (baseName messageName : String)
    (base message : BitVec 64) (fields : List Field)
    (baseLocal : source.locals.lookup (ofString baseName) = some (.val (.word base)))
    (ready : ∀ field ∈ fields, field.value.Ready source messageName message)
    (mapped : ∀ field ∈ fields, source.memaddrs (base + BitVec.ofNat 64 field.offset))
    (separate : ∀ reader ∈ fields, ∀ writer ∈ fields,
      reader.value.Avoid message (base + BitVec.ofNat 64 writer.offset)) (continuation : ProgHOL 64) :
    evaluateHOLFiniteState source (program baseName messageName fields continuation) =
      evaluateHOLFiniteState {source with memory := WitnessRadix.WordWrites.write source.memory (writes base fields)} continuation := by
  classical
  induction fields generalizing source with
  | nil => rfl
  | cons field rest ih =>
    let middle := {source with memory := (WitnessRadix.StoreWord.put source.memory
      (base + BitVec.ofNat 64 field.offset) field.value.word)}
    have addressRead : eval source (address baseName field.offset) =
        some (.val (.word (base + BitVec.ofNat 64 field.offset))) := by
      simp [eval, address, addConst, localVar, evalHOLExact, evalListHOLExact, toExact,
        baseLocal, valueIsWord, valueWord, wordOpHOL, wordOp]
    have storeRun := WitnessRadix.StoreWord.execute source (address baseName field.offset)
      (field.value.expression messageName) (base + BitVec.ofNat 64 field.offset) field.value.word
      addressRead (field.value.read source messageName message (ready field (by simp))) (mapped field (by simp))
    have remaining : ∀ next ∈ rest, next.value.Ready middle messageName message := by
      intro next member
      exact next.value.ready_store source messageName message _ _ (ready next (by simp [member]))
        (separate next (by simp [member]) field (by simp))
    have tailMapped : ∀ next ∈ rest, middle.memaddrs (base + BitVec.ofNat 64 next.offset) := by
      intro next member
      exact mapped next (by simp [member])
    have tailSeparate : ∀ reader ∈ rest, ∀ writer ∈ rest,
        reader.value.Avoid message (base + BitVec.ofNat 64 writer.offset) := by
      intro reader readerIn writer writerIn
      exact separate reader (by simp [readerIn]) writer (by simp [writerIn])
    rw [program, WitnessRadix.StateSteps.next_sequence source middle _ _ storeRun (Nat.le_refl _),
      ih middle baseLocal remaining tailMapped tailSeparate]
    rfl

end InitECandidate.Solver.FieldStores

#print axioms InitECandidate.Solver.FieldStores.Value.read
#print axioms InitECandidate.Solver.FieldStores.Value.ready_store
#print axioms InitECandidate.Solver.FieldStores.execute
