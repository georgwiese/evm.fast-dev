import InitECandidate.Solver.GasBudget.JournalImage
import InitECandidate.Solver.WitnessRadix.ProgramPrefix

namespace InitECandidate.Solver.GasBudget.Journal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable

def entered {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base index : Nat) (entry : Entry ι) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  bind (bind (bind source "r" (entryAddress base index 0)) "t" (objects entry.writer).pointer) "key" entry.key

def restored (source target : PanSemStateFiniteExact 64 Guest.HostMemory) : PanSemStateFiniteExact 64 Guest.HostMemory :=
  restore source "r" (restore source "t" (restore source "key" target))

theorem record_expression_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base index : Nat)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 index)))) :
    eval source recordExpression = some (.val (.word (entryAddress base index 0))) := by
  simp [eval, recordExpression, journalVar, countVar, evalHOLExact, evalListHOLExact, toExact, journal, counter,
    valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL, entryAddress, ← BitVec.ofNat_mul, ← BitVec.ofNat_add, Nat.mul_comm index 32]

theorem field_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (base index : Nat) (field : Fin 4) (word : BitVec 64)
    (r : source.locals.lookup (ofString "r") = some (.val (.word (entryAddress base index 0))))
    (mapped : source.memaddrs (entryAddress base index field))
    (stored : source.memory (entryAddress base index field) = .word word) :
    eval source (recordField (BitVec.ofNat 64 (8 * field.val))) = some (.val (.word word)) := by
  have address : entryAddress base index 0 + BitVec.ofNat 64 (8 * field.val) = entryAddress base index field := by
    simp [entryAddress, ← BitVec.ofNat_add]
  simp [eval, recordField, localVar, evalHOLExact, evalListHOLExact, toExact, r,
    valueIsWord, valueWord, wordOpHOL, wordOp, address, isWfShapeExactHOL, memLoadHOLExact, mapped, stored]

/-- The three real journal declarations read the current record. The returned
equation retains their lexical restoration and the actual selected helper. -/
theorem records_execute {ι : Type} (source : PanSemStateFiniteExact 64 Guest.HostMemory) (objects : ι → TableFamily.Object)
    (base count index : Nat) (entries : Nat → Entry ι) (inside : index < count)
    (image : Image source objects base count entries)
    (journal : source.globals.lookup (ofString "journal") = some (.val (.word (BitVec.ofNat 64 base))))
    (counter : source.globals.lookup (ofString "journal_n") = some (.val (.word (BitVec.ofNat 64 index)))) :
    evaluateHOLFiniteState source records =
      (let result := evaluateHOLFiniteState (entered source objects base index (entries index)) selectCall
       (result.1, restored source result.2)) := by
  let withRecord := bind source "r" (entryAddress base index 0)
  let withTable := bind withRecord "t" (objects (entries index).writer).pointer
  have rRead := record_expression_read source base index journal counter
  have tRead : eval withRecord (.load .one (localVar "r")) = some (.val (.word (objects (entries index).writer).pointer)) := by
    have rBinding : withRecord.locals.lookup (ofString "r") = some (.val (.word (entryAddress base index 0))) := bind_lookup_same _ _ _
    have mapped : withRecord.memaddrs (entryAddress base index 0) := image.mapped index inside 0
    have stored : withRecord.memory (entryAddress base index 0) = .word (objects (entries index).writer).pointer := image.words index inside 0
    simp [eval, localVar, evalHOLExact, toExact, rBinding, isWfShapeExactHOL, memLoadHOLExact, mapped, stored]
  have keyR : withTable.locals.lookup (ofString "r") = some (.val (.word (entryAddress base index 0))) :=
    (bind_lookup_other _ "t" "r" _ (by decide)).trans (bind_lookup_same _ _ _)
  have keyRead : eval withTable (recordField 8#64) = some (.val (.word (entries index).key)) :=
    field_read withTable base index 1 _ keyR (image.mapped index inside 1) (image.words index inside 1)
  have setup : WitnessRadix.ProgramPrefix.Executes source
      [.declare "r" recordExpression, .declare "t" (.load .one (localVar "r")), .declare "key" (recordField 8#64)]
      (entered source objects base index (entries index))
      (fun post => restore source "r" (restore withRecord "t" (restore withTable "key" post))) :=
    .declare _ rRead (.declare _ tRead (.declare _ keyRead (.done _)))
  have actual := WitnessRadix.ProgramPrefix.execute setup selectCall
  have restoreEq (post : PanSemStateFiniteExact 64 Guest.HostMemory) :
      restore source "r" (restore withRecord "t" (restore withTable "key" post)) = restored source post := by
    have rt : ofString "r" ≠ ofString "t" := by decide
    have rk : ofString "r" ≠ ofString "key" := by decide
    have tk : ofString "t" ≠ ofString "key" := by decide
    simp [restored, restore, WitnessRadix.QueryBranch.bind, setVarHOLFinite,
      withRecord, withTable, HolFiniteMapExact.update, FUPDATE, rt, rk, tk]
  change evaluateHOLFiniteState source records = _ at actual
  simpa only [restoreEq] using actual

end InitECandidate.Solver.GasBudget.Journal

#print axioms InitECandidate.Solver.GasBudget.Journal.record_expression_read
#print axioms InitECandidate.Solver.GasBudget.Journal.field_read
#print axioms InitECandidate.Solver.GasBudget.Journal.records_execute
