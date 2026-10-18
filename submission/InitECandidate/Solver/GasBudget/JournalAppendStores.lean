import InitECandidate.Solver.GasBudget.JournalRecordImage
import InitECandidate.Solver.GasBudget.JournalAppendKeyModel

namespace InitECandidate.Solver.GasBudget.Journal.Append
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch MutableTable

def storedFlag (deleting : Bool) : ExpHOL 64 := if deleting then .const 1#64 else .rfield 0 (localVar "old")
def storesProgram (deleting : Bool) (continuation : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (localVar "r") (localVar "t"))
    (.seq (.store (addConst (localVar "r") 8#64) (localVar "kc"))
      (.seq (.store (addConst (localVar "r") 16#64) (storedFlag deleting))
        (.seq (.store (addConst (localVar "r") 24#64) (.rfield 1 (localVar "old"))) continuation)))
def afterStores (program : ProgHOL 64) : ProgHOL 64 :=
  match program with | .dec _ _ _ (.seq _ (.seq _ (.seq _ (.seq _ rest)))) => rest | _ => .skip

theorem set_stores_shape : setAfterCopy = .dec (ofString "r") .one recordExpression (storesProgram false (afterStores setAfterCopy)) := by
  simp only [setAfterCopy, setAfterGuard, setAfterGet, setBody, afterStores, Guest.guestFn_jset, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, recordExpression, journalVar, countVar,
    storesProgram, storedFlag, Bool.false_eq_true, ↓reduceIte, localVar, addConst]

theorem delete_stores_shape : deleteAfterCopy = .dec (ofString "r") .one recordExpression (storesProgram true (afterStores deleteAfterCopy)) := by
  simp only [deleteAfterCopy, deleteAfterGuard, deleteAfterEmpty, deleteAfterGet, deleteBody, afterStores, Guest.guestFn_jdel, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none, Option.map_some, recordExpression, journalVar, countVar,
    storesProgram, storedFlag, ↓reduceIte, localVar, addConst]

theorem entry_address_add (base index : Nat) (field : Fin 4) :
    entryAddress base index 0 + BitVec.ofNat 64 (8 * field.val) = entryAddress base index field := by
  simp [entryAddress, ← BitVec.ofNat_add]

/-- All four actual original journal stores execute with their real local
and tuple reads. They establish exactly the record image's four writes. -/
theorem stores_execute {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base index : Nat) (entry : Entry ι) (flag : BitVec 64) (deleting : Bool) (continuation : ProgHOL 64)
    (r : source.locals.lookup (ofString "r") = some (.val (.word (entryAddress base index 0))))
    (t : source.locals.lookup (ofString "t") = some (.val (.word (objects entry.writer).pointer)))
    (keyCopy : source.locals.lookup (ofString "kc") = some (.val (.word entry.key)))
    (old : source.locals.lookup (ofString "old") = some (Get.pair flag entry.value))
    (flagEq : entry.flag = if deleting then 1#64 else flag)
    (mapped : ∀ field : Fin 4, source.memaddrs (entryAddress base index field)) :
    evaluateHOLFiniteState source (storesProgram deleting continuation) = evaluateHOLFiniteState (recordState source objects base index entry) continuation := by
  let first := {source with memory := StoreWord.put source.memory (entryAddress base index 0) (objects entry.writer).pointer}
  let second := {first with memory := StoreWord.put first.memory (entryAddress base index 1) entry.key}
  let third := {second with memory := StoreWord.put second.memory (entryAddress base index 2) entry.flag}
  let fourth := {third with memory := StoreWord.put third.memory (entryAddress base index 3) entry.value}
  have readR (memory : WordWrites.Memory) : eval {source with memory := memory} (localVar "r") = some (.val (.word (entryAddress base index 0))) := by
    simp [eval, localVar, evalHOLExact, toExact, r]
  have readAddress (memory : WordWrites.Memory) (field : Fin 4) :
      eval {source with memory := memory} (addConst (localVar "r") (BitVec.ofNat 64 (8 * field.val))) = some (.val (.word (entryAddress base index field))) := by
    simp [eval, addConst, localVar, evalHOLExact, evalListHOLExact, toExact, r,
      valueIsWord, valueWord, wordOpHOL, wordOp, entry_address_add]
  have readTable : eval source (localVar "t") = some (.val (.word (objects entry.writer).pointer)) := by simp [eval, localVar, evalHOLExact, toExact, t]
  have readCopy : eval first (localVar "kc") = some (.val (.word entry.key)) := by
    change eval {source with memory := first.memory} (localVar "kc") = _
    simp [eval, localVar, evalHOLExact, toExact, keyCopy]
  have readFlag : eval second (storedFlag deleting) = some (.val (.word entry.flag)) := by
    change eval {source with memory := second.memory} (storedFlag deleting) = _
    cases deleting <;> simp [eval, storedFlag, localVar, evalHOLExact, toExact, old, Get.pair, flagEq] at *
  have readValue : eval third (.rfield 1 (localVar "old")) = some (.val (.word entry.value)) := by
    change eval {source with memory := third.memory} (.rfield 1 (localVar "old")) = _
    simp [eval, localVar, evalHOLExact, toExact, old, Get.pair]
  have firstRun : evaluateHOLFiniteState source (.store (localVar "r") (localVar "t")) = (none, first) :=
    StoreWord.execute source _ _ _ _ (readR source.memory) readTable (mapped 0)
  have secondRun : evaluateHOLFiniteState first (.store (addConst (localVar "r") 8#64) (localVar "kc")) = (none, second) :=
    StoreWord.execute first _ _ _ _ (readAddress first.memory 1) readCopy (mapped 1)
  have thirdRun : evaluateHOLFiniteState second (.store (addConst (localVar "r") 16#64) (storedFlag deleting)) = (none, third) :=
    StoreWord.execute second _ _ _ _ (readAddress second.memory 2) readFlag (mapped 2)
  have fourthRun : evaluateHOLFiniteState third (.store (addConst (localVar "r") 24#64) (.rfield 1 (localVar "old"))) = (none, fourth) :=
    StoreWord.execute third _ _ _ _ (readAddress third.memory 3) readValue (mapped 3)
  rw [storesProgram, StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _),
    StateSteps.next_sequence first second _ _ secondRun (Nat.le_refl _),
    StateSteps.next_sequence second third _ _ thirdRun (Nat.le_refl _),
    StateSteps.next_sequence third fourth _ _ fourthRun (Nat.le_refl _)]
  rfl

end InitECandidate.Solver.GasBudget.Journal.Append

#print axioms InitECandidate.Solver.GasBudget.Journal.Append.set_stores_shape
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.delete_stores_shape
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.entry_address_add
#print axioms InitECandidate.Solver.GasBudget.Journal.Append.stores_execute
